import IxCCAiur.TypedGadgets
import IxCCAiur.Backward
import IxCC.Fir.Proof.Shape

/-! # Certified Backward Simulation for Typed / Unboxed `Fir → Formal Aiur` (`IxCCAiur.TypedBackward`)

Proves end-to-end backward simulation from `Aiur.Generic.SourceSemantics.EvalFn` on
programs lowered by `IxCC.AiurBackend.TypedLower.lowerProgram` back to `IxCC.Fir.run`,
covering:

1. **`eval_u32_mul` and `eval_u32_shl`** under `TypedGadgets.FieldCompatible64 F`
   (sound via the `hi ≠ 2^32 - 1` Goldilocks wraparound guard in `TypedLower.u32MulFn`).
2. **Typed Value Relation (`TVR` & `TVRDataFields`)** across all nine `TypedRep.Rep`
   representations (`.irr`, `.nat b`, `.w8`, `.w16`, `.w32`, `.w64`, `.enum ind`,
   `.data d` with inline acyclic & heap-pointer cyclic fields, and fallback `.obj`),
   together with heap-extension monotonicity (`TVR.extend`) and inversion lemmas.
3. **`TypedLoweredWorld` & `typedLoweredWorld_of_check`**: tier-aware world hypothesis
   discharged directly from `TypedWorld.checkTypedWorld`.
4. **Peephole backward simulation (`evalExprN_of_rewriteExpr_noU32`)**: strips
   `Peephole.rewriteExpr` (including dead constant-binding elimination `tryDropDeadConst`)
   on all `noU32Calls` expressions.
5. **Complete backward simulation for the certified `Nat`/enum/data/obj core fragment**
   (`natCoreProgram`): covers all 16 `Nat` primitives, `coerceE`, `OffMap` + `nz`
   countdown subtraction (`stepDownNat`, `natAdd (base - d) k`, `proj x natSucc 0`,
   `natPred`, `natSub _ 1`), join points with arbitrary capture filtering
   (`filterJpCaptures`), `tCaseE`, `tFunE`, `tEntryE`, and Goldilocks circuit
   composition (`typed_circuit_sound_goldilocks`).

Zero `sorry`, zero `admit`, zero `axiom`, zero `native_decide`, zero `bv_decide`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.TypedBackward

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.Fir (Program Fun FunId Var JoinId Arg Rhs Code Alt CtorInfo Env
  evalArgs lookupJ projVal boolVal evalRhs evalCall bindAll primResult natArgs)
open IxCC.Key
open IxCC.Lam (Lit Prim)
open IxCC.Shape (Shape DataDecl)
open IxCC.Fir.Shape (ShapeCert FunShapes ValOk ValsOk EnvOk ArgOk ArgsOk ParamsOk
  PrimOk RhsOk CodeOk AltsOk OptOk Checked)
open IxCC.AiurBackend.Lower
  (Ty Expr Pat Fn natLimit natDigits moduleName qualified objName bytesName objQName bytesQName
   objTy bytesTy funName entryName jpFunName localName entryParamName ctorNameOf
   allDistinct objCtorNames mk natE erasedE bytesE strE pN pC callE vE litE letE seqE
   matchE addE subE assertion trapE wordE qualifyName qualifyTy qualifyExpr qualifyPat
   qualifyExprF qualifyPatF isPlainExpr isPlainList isPlainArms isPlainExpr_qualifyExprF
   AllLocalLt qualifyName_obj ctorEntry?_sound ctorEntry?_complete ctorNameOf_inj_of_nodup
   localName_inj entryParamName_inj qualifyName_funName qualifyName_jpFunName qualifyName_entryName
   qualifyName_u64_from_field qualifyName_u64_to_field qualifyName_u64_and qualifyName_u64_or
   qualifyName_u64_xor)
open IxCC.AiurBackend.Schedule (CircuitSchedule)
open IxCC.AiurBackend.Gadgets
open IxCC.AiurBackend.World
open IxCC.AiurBackend.Backward
  (BytesRep VR VRs VR_N_inv VR_E_inv VR_S_inv VR_ctor_inv
   EvalExprN EvalArgsN EvalFnN EvalExitN EvalArgsExitN
   evalFnN_plain_inv evalExprN_literal_inv evalExprN_var_inv evalExprN_let_bind_inv
   evalExprN_let_wildcard_inv evalExprN_call_inv evalExprN_construct_inv
   evalExprN_store_inv evalExprN_load_inv evalExprN_binary_inv evalArgsN_append_inv
   eval_bytesE eval_projE EvalCapArgs find?_eq_of_evalCapArgs eval_capNames
   firstPerKey_nil_find?)
open IxCC.AiurBackend.TypedRep
open IxCC.AiurBackend.TypedLower
open IxCC.AiurBackend.TypedWorld
open IxCC.AiurBackend.TypedGadgets

/-! ## Section 1: Soundness of `Prog::u32_mul` and `Prog::u32_shl` -/

section U32MulShl

variable {F : Type} [Field F] [DecidableEq F]

private theorem evalExpr_var_eq {world : World F} {locals : Environment F Nat}
    {nm : String} {v r : SourceValue F} {h h' : Heap F}
    (hlook : locals.find? (·.1 == nm) = some (nm, v))
    (ev : EvalExpr world [] locals (.var nm) h r h') :
    r = v ∧ h' = h := by
  obtain ⟨hl, rfl⟩ := evalExpr_var_inv ev
  rw [hlook, Option.some.injEq, Prod.mk.injEq] at hl
  exact ⟨hl.2.symm, rfl⟩

private theorem eval_u32ToField_var {world : World F} (u32 : U32Contracts world)
    {locals : Environment F Nat} {nm : String} {n : Nat} {w r : SourceValue F}
    {h h' : Heap F} (hw : isU32Val n w)
    (hlook : locals.find? (·.1 == nm) = some (nm, w))
    (ev : EvalExpr world [] locals
      (.call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [.var nm]])
      h r h') :
    r = .field (n : F) ∧ h' = h := by
  obtain ⟨vc, _, evc, ccf⟩ := evalExpr_call1_inv ev
  obtain ⟨vw, _, evw, cc⟩ := evalExpr_call1_inv evc
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evw
  obtain ⟨rfl, rfl⟩ := u32.compact _ _ _ _ _ hw cc
  exact u32.compact_field _ _ _ _ ccf

private theorem body_u32MulFn :
    u32MulFn.body =
      .letValue (.bind "p")
        (.binary .mul
          (.call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [.var "a"]])
          (.call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [.var "b"]]))
        (.letValue (.array [.bind "h0", .bind "h1", .bind "h2", .bind "h3",
                            .bind "h4", .bind "h5", .bind "h6", .bind "h7"])
          (.hint (.array .field 8) (.var "p") "bytes_le")
          (.letValue (.bind "lo")
            (.call "UInt32::from_fields" (some []) [.array [.var "h0", .var "h1", .var "h2", .var "h3"]])
            (.letValue (.bind "hi")
              (.call "UInt32::from_fields" (some []) [.array [.var "h4", .var "h5", .var "h6", .var "h7"]])
              (.letValue (.bind "hif")
                (.call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [.var "hi"]])
                (.letValue .wildcard
                  (.builtin (.assertEq (assertion "u32_mul: recomposition failed"))
                    [.binary .add
                      (.call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [.var "lo"]])
                      (.binary .mul (.literal (2 ^ 32)) (.var "hif")),
                     .var "p"])
                  (.matchValue (.var "hif")
                    [(.literal (2 ^ 32 - 1),
                      .letValue .wildcard
                        (.builtin (.assertEq (assertion "u32_mul: hi = 2^32 - 1 overflow"))
                          [.literal 0, .literal 1])
                        (.var "lo")),
                     (.wildcard, .var "lo")])))))) := rfl

/-- Exact soundness of `Prog::u32_mul` under `FieldCompatible64 F`:
because `(2^32 - 1)^2 = 1 + 2^32 * (2^32 - 2) < 2^64 - 2^32 + 1 = fieldBound64` and
the `hi ≠ 2^32 - 1` guard bounds `lo + 2^32 * hi ≤ 2^64 - 2^32 - 1 < fieldBound64`,
no Goldilocks wraparound forgery is possible and the result is `(a * b) % 2^32`. -/
theorem eval_u32_mul {world : World F}
    (fc : FieldCompatible64 F) (u32 : U32Contracts world)
    (hfn : WorldHasFn world (qualified "u32_mul") ["a", "b"]
      (qualifyExprF F u32MulFn.body))
    {a b : Nat} {wa wb r : SourceValue F} {h h' : Heap F}
    (hwa : isU32Val a wa) (hwb : isU32Val b wb)
    (ev : EvalFn world (qualified "u32_mul") [wa, wb] h r h') :
    h' = h ∧ isU32Val ((a * b) % U32.base) r := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_u32MulFn) ev
  rw [body_u32MulFn] at body
  simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy,
    qualifyName_u32_compact_field, qualifyName_u32_compact, qualifyName_u32_from_fields,
    Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
    Nat.cast_zero, Nat.cast_one] at body
  -- 1. `p = a * b`
  obtain ⟨vp, _, evp, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨va, vb, _, eva, evb, hmul⟩ := evalExpr_binary_inv evp
  obtain ⟨rfl, rfl⟩ := eval_u32ToField_var u32 hwa (by simp) eva
  obtain ⟨rfl, rfl⟩ := eval_u32ToField_var u32 hwb (by simp) evb
  simp only [evalBinOp, Except.ok.injEq] at hmul; subst hmul
  -- 2. `[h0..h7] = hint bytes_le p`
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, _, evh, k2⟩ := evalExpr_let_array8_inv k1
  obtain ⟨_, evp'⟩ := evalExpr_hint_inv evh
  obtain ⟨_, rfl⟩ := evalExpr_var_inv evp'
  -- 3. `lo = UInt32::from_fields [h0..h3]`
  obtain ⟨vlo, _, evlo, k3⟩ := evalExpr_let_bind_inv k2
  obtain ⟨va1, _, eva1, cff1⟩ := evalExpr_call1_inv evlo
  obtain ⟨u0, u1, u2, u3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv eva1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e3
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl, rfl, rfl, hloVal, rfl⟩ :=
    u32.from_fields _ _ _ _ _ _ _ cff1
  -- 4. `hi = UInt32::from_fields [h4..h7]`
  obtain ⟨vhi, _, evhi, k4⟩ := evalExpr_let_bind_inv k3
  obtain ⟨va2, _, eva2, cff2⟩ := evalExpr_call1_inv evhi
  obtain ⟨u4, u5, u6, u7, _, _, _, e4, e5, e6, e7, rfl⟩ := evalExpr_array4_inv eva2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e4
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e5
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e6
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e7
  obtain ⟨b4, b5, b6, b7, hb4, hb5, hb6, hb7, rfl, rfl, rfl, rfl, hhiVal, rfl⟩ :=
    u32.from_fields _ _ _ _ _ _ _ cff2
  -- 5. `hif = u32ToField hi`
  obtain ⟨vhif, _, evhif, k5⟩ := evalExpr_let_bind_inv k4
  obtain ⟨rfl, rfl⟩ := eval_u32ToField_var u32 hhiVal (by simp) evhif
  -- 6. `assertEq(lo + 2^32 * hif, p)`
  obtain ⟨_, _, hass, k6⟩ := evalExpr_let_wildcard_inv k5
  obtain ⟨vl, vr, _, evl, evr, hrecEq, _⟩ := evalExpr_assertEq_inv hass
  obtain ⟨vla, vlb, _, evla, evlb, hadd⟩ := evalExpr_binary_inv evl
  obtain ⟨rfl, rfl⟩ := eval_u32ToField_var u32 hloVal (by simp) evla
  obtain ⟨vm1, vm2, _, evm1, evm2, hmul2⟩ := evalExpr_binary_inv evlb
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evm1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evm2
  simp only [evalBinOp, Except.ok.injEq] at hmul2; subst hmul2
  simp only [evalBinOp, Except.ok.injEq] at hadd; subst hadd
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr
  -- 7. `match hif { 2^32 - 1 => assertEq(0, 1); lo, _ => lo }`
  obtain ⟨vhif', _, evhif', hbr⟩ := evalExpr_match_lit_wild_inv k6
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evhif'
  rcases hbr with ⟨_, hbad⟩ | ⟨hhiNeF, hgood⟩
  · exfalso
    obtain ⟨_, _, h01, _⟩ := evalExpr_let_wildcard_inv hbad
    obtain ⟨v0, v1, _, ev0, ev1, heq01, _⟩ := evalExpr_assertEq_inv h01
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
    exact zero_ne_one (Value.field.inj heq01)
  · obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) hgood
    set lo := U32.pack b0 b1 b2 b3
    set hi := U32.pack b4 b5 b6 b7
    have hloLt : lo < U32.base := U32.pack_lt hb0 hb1 hb2 hb3
    have hhiLt : hi < U32.base := U32.pack_lt hb4 hb5 hb6 hb7
    have hhiNe : hi ≠ 2 ^ 32 - 1 := by
      intro heq
      apply hhiNeF
      rw [heq]
    have hhiLe : hi ≤ 2 ^ 32 - 2 := by unfold U32.base at hhiLt; omega
    have haLt : a < U32.base := isU32Val_lt hwa
    have hbLt : b < U32.base := isU32Val_lt hwb
    have hprodLt : a * b < fieldBound64 := by
      have haLe : a ≤ 2 ^ 32 - 1 := by unfold U32.base at haLt; omega
      have hbLe : b ≤ 2 ^ 32 - 1 := by unfold U32.base at hbLt; omega
      have hmulLe : a * b ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul haLe hbLe
      have hbound : (2 ^ 32 - 1) * (2 ^ 32 - 1) < fieldBound64 := by decide
      exact lt_of_le_of_lt hmulLe hbound
    have hrecLt : lo + 2 ^ 32 * hi < fieldBound64 := by
      unfold U32.base fieldBound64 at *; omega
    have hlift : lo + 2 ^ 32 * hi = a * b := by
      apply fc.natCast_inj hrecLt hprodLt
      simpa [Nat.cast_add, Nat.cast_mul] using Value.field.inj hrecEq
    have hmod : lo = (a * b) % U32.base := by
      have hbase : (2 ^ 32 : Nat) = U32.base := rfl
      rw [← hlift, hbase, Nat.mul_comm U32.base, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hloLt]
    rw [← hmod]
    exact ⟨rfl, hloVal⟩

private theorem body_u32ShlFn :
    u32ShlFn.body =
      .letValue (.bind "s")
        (.call "UInt8::to_field" (some [])
          [.index (.call "UInt32::to_bytes" (some []) [.var "b"]) 0])
        (.letValue (.tuple [.wildcard, .bind "k"])
          (.call "divmod_56" (some []) [.var "s", .literal 32])
          (.letValue (.bind "p")
            (.call "pow_56" (some []) [.literal 2, .var "k"])
            (.call "u32_mul" (some [])
              [.var "a", .call "UInt32::from_field" (some []) [.var "p"]]))) := rfl

/-- Contract-parameterized soundness of `Prog::u32_shl`:
left shift `(a <<< (b % 32)) % 2^32`. -/
theorem eval_u32_shl_of_contracts {world : World F}
    (fc : FieldCompatible64 F) (u32 : U32Contracts world)
    (hfn : WorldHasFn world (qualified "u32_shl") ["a", "b"]
      (qualifyExprF F u32ShlFn.body))
    (hdivmodSpec : ∀ a b h r h', a < natLimit → b < natLimit →
      EvalFn world (qualified "divmod_56") [.field (a : F), .field (b : F)] h r h' →
      h' = h ∧ 0 < b ∧ r = .tuple [.field ((a / b : Nat) : F), .field ((a % b : Nat) : F)])
    (hpowSpec : ∀ a b h r h', a < natLimit → b < natLimit →
      EvalFn world (qualified "pow_56") [.field (a : F), .field (b : F)] h r h' →
      h' = h ∧ a ^ b < natLimit ∧ r = .field ((a ^ b : Nat) : F))
    (hmulSpec : ∀ a b wa wb h r h', isU32Val a wa → isU32Val b wb →
      EvalFn world (qualified "u32_mul") [wa, wb] h r h' →
      h' = h ∧ isU32Val ((a * b) % U32.base) r)
    {a b : Nat} {wa wb r : SourceValue F} {h h' : Heap F}
    (hwa : isU32Val a wa) (hwb : isU32Val b wb)
    (ev : EvalFn world (qualified "u32_shl") [wa, wb] h r h') :
    h' = h ∧ isU32Val ((Nat.shiftLeft a (b % 32)) % U32.base) r := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_u32ShlFn) ev
  rw [body_u32ShlFn] at body
  simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyName_u8_to_field,
    qualifyName_u32_to_bytes, qualifyName_divmod_56, qualifyName_pow_56,
    qualifyName_u32_mul, qualifyName_u32_from_field,
    Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at body
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩ := hwb
  obtain ⟨vs, _, evs, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨vi, _, evi, cu8⟩ := evalExpr_call1_inv evs
  obtain ⟨vt, evt, hproj⟩ := evalExpr_index_inv evi
  obtain ⟨vb', _, evb', ctb⟩ := evalExpr_call1_inv evt
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
  obtain ⟨rfl, rfl⟩ := u32.to_bytes _ _ _ _ _ ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩ ctb
  simp only [projectValue, List.getElem?_cons_zero, pure, Except.pure, Except.ok.injEq] at hproj
  subst hproj
  obtain ⟨rfl, rfl⟩ := u32.u8_to_field _ _ _ _ cu8
  obtain ⟨_, vk, _, evdm, k2⟩ := evalExpr_let_wild_tuple2_inv k1
  obtain ⟨vs', v32, _, _, evs', ev32, cdm⟩ := evalExpr_call2_inv evdm
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evs'
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev32
  obtain ⟨rfl, _, hdmEq⟩ :=
    hdivmodSpec b0 32 _ _ _ (by unfold natLimit; omega) (by unfold natLimit; omega) cdm
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hdmEq
  obtain ⟨_, rfl⟩ := hdmEq
  have hkMod : b0 % 32 = U32.pack b0 b1 b2 b3 % 32 := by
    unfold U32.pack; omega
  obtain ⟨vp, _, evp, k3⟩ := evalExpr_let_bind_inv k2
  obtain ⟨v2, vk', _, _, ev2, evk', cpow⟩ := evalExpr_call2_inv evp
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evk'
  obtain ⟨rfl, _, rfl⟩ :=
    hpowSpec 2 (b0 % 32) _ _ _ (by unfold natLimit; omega) (by unfold natLimit; omega) cpow
  obtain ⟨va', vpw, _, _, eva', evpw, cmul⟩ := evalExpr_call2_inv k3
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
  obtain ⟨vp', _, evp', cff⟩ := evalExpr_call1_inv evpw
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evp'
  obtain ⟨n, hn, hpeq, hnVal, rfl⟩ := u32.from_field _ _ _ _ cff
  have hpowLt32 : 2 ^ (b0 % 32) < U32.base := by
    have hle : b0 % 32 ≤ 31 := by omega
    have h1 : 2 ^ (b0 % 32) ≤ 2 ^ 31 := Nat.pow_le_pow_right (by omega) hle
    have h2 : 2 ^ 31 < U32.base := by decide
    exact lt_of_le_of_lt h1 h2
  have hpn : 2 ^ (b0 % 32) = n :=
    fc.natCast_inj (lt_trans hpowLt32 (by decide)) (lt_trans hn (by decide))
      (by simpa [Nat.cast_pow] using Value.field.inj hpeq)
  subst hpn
  obtain ⟨rfl, hres⟩ := hmulSpec a (2 ^ (b0 % 32)) va' vpw _ _ _ hwa hnVal cmul
  have hshlEq : Nat.shiftLeft a (U32.pack b0 b1 b2 b3 % 32) =
      a * 2 ^ (U32.pack b0 b1 b2 b3 % 32) := Nat.shiftLeft_eq a _
  rw [hshlEq, ← hkMod]
  exact ⟨rfl, hres⟩

/-- Operational soundness of `Prog::u32_shl` directly from `WorldHasFn` bindings. -/
theorem eval_u32_shl {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F) (hbc : ByteCheckSpec world usePair) (u32 : U32Contracts world)
    (hsplit : WorldHasFn world (qualified "split_32_24") ["x"]
      (qualifyExprF F (split32_24Fn usePair).body))
    (hu24 : WorldHasFn world (qualified "check_u24") ["x"]
      (qualifyExprF F (checkU24Fn usePair).body))
    (hu56 : WorldHasFn world (qualified "check_u56") ["x"]
      (qualifyExprF F (checkU56Fn usePair).body))
    (hsub : WorldHasFn world (qualified "sub_borrow_56") ["x", "y"]
      (qualifyExprF F (subBorrow56Fn usePair).body))
    (hmul : WorldHasFn world (qualified "mul_56") ["x", "y"]
      (qualifyExprF F mul56Fn.body))
    (hdivmod : WorldHasFn world (qualified "divmod_56") ["x", "y"]
      (qualifyExprF F divmod56Fn.body))
    (hloop : WorldHasFn world (qualified "pow_56_loop") ["base", "exp", "acc"]
      (qualifyExprF F pow56LoopFn.body))
    (hpow : WorldHasFn world (qualified "pow_56") ["base", "exp"]
      (qualifyExprF F pow56Fn.body))
    (hu32Mul : WorldHasFn world (qualified "u32_mul") ["a", "b"]
      (qualifyExprF F u32MulFn.body))
    (hfn : WorldHasFn world (qualified "u32_shl") ["a", "b"]
      (qualifyExprF F u32ShlFn.body))
    {a b : Nat} {wa wb r : SourceValue F} {h h' : Heap F}
    (hwa : isU32Val a wa) (hwb : isU32Val b wb)
    (ev : EvalFn world (qualified "u32_shl") [wa, wb] h r h') :
    h' = h ∧ isU32Val ((Nat.shiftLeft a (b % 32)) % U32.base) r :=
  eval_u32_shl_of_contracts fc u32 hfn
    (fun _ _ _ _ _ hx hy e => eval_divmod_56 fc hbc hsplit hu24 hu56 hsub hmul hdivmod hx hy e)
    (fun _ _ _ _ _ hx hy e =>
      eval_pow_56 fc hbc hsplit hu24 hu56 hsub hmul hdivmod hloop hpow hx hy e)
    (fun _ _ _ _ _ _ _ ha hb e => eval_u32_mul fc u32 hu32Mul ha hb e)
    hwa hwb ev

end U32MulShl

/-! ## Section 2: Typed Value Relation (`TVR` & `TVRDataFields`) -/

section TypedValueRel

variable {F : Type} [Field F]

mutual

/-- Typed value relation connecting a Fir runtime value `v` to its unboxed Aiur
representation `w` on heap `h` at representation `r : Rep`. -/
inductive TVR (P : Program) (cert : ShapeCert) (feat : Features) (h : Heap F) :
    Rep → Fir.Val → SourceValue F → Prop where
  | irr :
      TVR P cert feat h .irr .erased (.tuple [])
  | nat {b n : Nat} (hsmall : n < min b natLimit) :
      TVR P cert feat h (.nat b) (.lit (.nat n)) (.field (n : F))
  | w8 {n : Nat} (hsmall : n < 256) :
      TVR P cert feat h .w8 (.lit (.nat n)) (.field (n : F))
  | w16 {n : Nat} (hsmall : n < 65536) :
      TVR P cert feat h .w16 (.lit (.nat n)) (.field (n : F))
  | w32 {n : Nat} {w : SourceValue F} (hw : isU32Val n w) :
      TVR P cert feat h .w32 (.lit (.nat n)) w
  | w64 {n : Nat} {w : SourceValue F} (hw : isU64Val n w) :
      TVR P cert feat h .w64 (.lit (.nat n)) w
  | enumVal {ind : Src.CId} {ks : List CtorKey} {c : CtorInfo} {idx : Nat} {entry : Lam.CtorInfo}
      (henum : cert.enum? ind = some ks)
      (hmem : c.key ∈ ks)
      (atIdx : P.ctors[idx]? = some entry)
      (keyEq : entry.key = c.key)
      (harity : entry.arity = 0) :
      TVR P cert feat h (.enum ind) (.ctor c [])
        (.construct (enumQName ind) (ctorNameOf idx c.key) [])
  | dataVal {d : Nat} {D : DataDecl CtorKey} {c : CtorInfo}
      {fl : List Shape} {idx : Nat} {entry : Lam.CtorInfo}
      {fs : List Fir.Val} {ws : List (SourceValue F)}
      (hdata : cert.data? d = some D)
      (hctor : (c.key, fl) ∈ D.ctors)
      (atIdx : P.ctors[idx]? = some entry)
      (keyEq : entry.key = c.key)
      (arityEq : fs.length = entry.arity)
      (flLen : fl.length = entry.arity)
      (fields : TVRDataFields P cert feat h d fl fs ws) :
      TVR P cert feat h (.data d) (.ctor c fs)
        (.construct (dataQName d) (ctorNameOf idx c.key) ws)
  | obj {v : Fir.Val} {w : SourceValue F}
      (hvr : VR P objQName bytesQName h v w) :
      TVR P cert feat h .obj v w

/-- Field-list relation for dedicated inductive enum `D<owner>`: each field lives
inline unboxed or behind a heap pointer according to `dataFieldNeedsPtr`. -/
inductive TVRDataFields (P : Program) (cert : ShapeCert) (feat : Features) (h : Heap F) :
    Nat → List Shape → List Fir.Val → List (SourceValue F) → Prop where
  | nil {owner : Nat} :
      TVRDataFields P cert feat h owner [] [] []
  | consInline {owner : Nat} {sh : Shape} {fl : List Shape} {v : Fir.Val} {vs : List Fir.Val}
      {w : SourceValue F} {ws : List (SourceValue F)}
      (hnoPtr : dataFieldNeedsPtr P cert feat owner (repOf P cert feat sh) = false)
      (head : TVR P cert feat h (repOf P cert feat sh) v w)
      (tail : TVRDataFields P cert feat h owner fl vs ws) :
      TVRDataFields P cert feat h owner (sh :: fl) (v :: vs) (w :: ws)
  | consPtr {owner : Nat} {sh : Shape} {fl : List Shape} {v : Fir.Val} {vs : List Fir.Val}
      {addr : Nat} {w : SourceValue F} {ws : List (SourceValue F)}
      (hptr : dataFieldNeedsPtr P cert feat owner (repOf P cert feat sh) = true)
      (atAddr : h[addr]? = some w)
      (head : TVR P cert feat h (repOf P cert feat sh) v w)
      (tail : TVRDataFields P cert feat h owner fl vs ws) :
      TVRDataFields P cert feat h owner (sh :: fl) (v :: vs) (.ptr w.type addr :: ws)

end

mutual

theorem TVR.extend {P : Program} {cert : ShapeCert} {feat : Features}
    {h h' : Heap F} (ext : Heap.Extends h h') :
    ∀ {r : Rep} {v : Fir.Val} {w : SourceValue F},
      TVR P cert feat h r v w → TVR P cert feat h' r v w
  | _, _, _, .irr => .irr
  | _, _, _, .nat hs => .nat hs
  | _, _, _, .w8 hs => .w8 hs
  | _, _, _, .w16 hs => .w16 hs
  | _, _, _, .w32 hw => .w32 hw
  | _, _, _, .w64 hw => .w64 hw
  | _, _, _, .enumVal he hm hi hk ha => .enumVal he hm hi hk ha
  | _, _, _, .dataVal hd hc hi hk ha hfl hfs =>
    .dataVal hd hc hi hk ha hfl (TVRDataFields.extend ext hfs)
  | _, _, _, .obj hvr => .obj (hvr.extend ext)

theorem TVRDataFields.extend {P : Program} {cert : ShapeCert} {feat : Features}
    {h h' : Heap F} (ext : Heap.Extends h h') :
    ∀ {owner : Nat} {fl : List Shape} {vs : List Fir.Val} {ws : List (SourceValue F)},
      TVRDataFields P cert feat h owner fl vs ws →
      TVRDataFields P cert feat h' owner fl vs ws
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .consInline hnp hd tl =>
    .consInline hnp (TVR.extend ext hd) (TVRDataFields.extend ext tl)
  | _, _, _, _, .consPtr hp ha hd tl =>
    .consPtr hp (ext.getElem?_eq ha) (TVR.extend ext hd) (TVRDataFields.extend ext tl)

end

theorem TVRDataFields.length_eq {P : Program} {cert : ShapeCert} {feat : Features}
    {h : Heap F} {owner : Nat} :
    ∀ {fl : List Shape} {vs : List Fir.Val} {ws : List (SourceValue F)},
      TVRDataFields P cert feat h owner fl vs ws →
      vs.length = fl.length ∧ ws.length = fl.length
  | _, _, _, .nil => ⟨rfl, rfl⟩
  | _, _, _, .consInline _ _ tl =>
    let ⟨h1, h2⟩ := tl.length_eq
    ⟨congrArg Nat.succ h1, congrArg Nat.succ h2⟩
  | _, _, _, .consPtr _ _ _ tl =>
    let ⟨h1, h2⟩ := tl.length_eq
    ⟨congrArg Nat.succ h1, congrArg Nat.succ h2⟩

theorem TVRDataFields.getElem?_some {P : Program} {cert : ShapeCert} {feat : Features}
    {h : Heap F} {owner : Nat} :
    ∀ {i : Nat} {fl : List Shape} {vs : List Fir.Val} {ws : List (SourceValue F)} {sh : Shape},
      TVRDataFields P cert feat h owner fl vs ws →
      fl[i]? = some sh →
      ∃ v wRaw,
        vs[i]? = some v ∧
        ws[i]? = some wRaw ∧
        ((dataFieldNeedsPtr P cert feat owner (repOf P cert feat sh) = false ∧
            TVR P cert feat h (repOf P cert feat sh) v wRaw) ∨
         (dataFieldNeedsPtr P cert feat owner (repOf P cert feat sh) = true ∧
            ∃ addr w, wRaw = .ptr w.type addr ∧ h[addr]? = some w ∧
              TVR P cert feat h (repOf P cert feat sh) v w))
  | 0, _ :: _, _ :: _, _ :: _, _, .consInline hnp hd _, hget => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget
    exact ⟨_, _, rfl, rfl, Or.inl ⟨hnp, hd⟩⟩
  | 0, _ :: _, _ :: _, _ :: _, _, .consPtr hp ha hd _, hget => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget
    exact ⟨_, _, rfl, rfl, Or.inr ⟨hp, _, _, rfl, ha, hd⟩⟩
  | _ + 1, _ :: _, _ :: _, _ :: _, _, .consInline _ _ tl, hget =>
    tl.getElem?_some hget
  | _ + 1, _ :: _, _ :: _, _ :: _, _, .consPtr _ _ _ tl, hget =>
    tl.getElem?_some hget
  | _, [], [], [], _, .nil, hget => by simp at hget

/-! ### Inversion Lemmas for `TVR` -/

theorem TVR_irr_inv {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F}
    {v : Fir.Val} {w : SourceValue F} (hr : TVR P cert feat h .irr v w) :
    v = .erased ∧ w = .tuple [] := by
  cases hr; exact ⟨rfl, rfl⟩

theorem TVR_nat_inv {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F}
    {b : Nat} {v : Fir.Val} {w : SourceValue F} (hr : TVR P cert feat h (.nat b) v w) :
    ∃ n : Nat, n < min b natLimit ∧ n < natLimit ∧ v = .lit (.nat n) ∧ w = .field (n : F) := by
  cases hr with
  | nat hsmall =>
    exact ⟨_, hsmall, lt_of_lt_of_le hsmall (Nat.min_le_right _ _), rfl, rfl⟩

theorem TVR_w8_inv {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F}
    {v : Fir.Val} {w : SourceValue F} (hr : TVR P cert feat h .w8 v w) :
    ∃ n : Nat, n < 256 ∧ v = .lit (.nat n) ∧ w = .field (n : F) := by
  cases hr with
  | w8 hsmall => exact ⟨_, hsmall, rfl, rfl⟩

theorem TVR_w16_inv {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F}
    {v : Fir.Val} {w : SourceValue F} (hr : TVR P cert feat h .w16 v w) :
    ∃ n : Nat, n < 65536 ∧ v = .lit (.nat n) ∧ w = .field (n : F) := by
  cases hr with
  | w16 hsmall => exact ⟨_, hsmall, rfl, rfl⟩

theorem TVR_w32_inv {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F}
    {v : Fir.Val} {w : SourceValue F} (hr : TVR P cert feat h .w32 v w) :
    ∃ n : Nat, isU32Val n w ∧ v = .lit (.nat n) := by
  cases hr with
  | w32 hw => exact ⟨_, hw, rfl⟩

theorem TVR_w64_inv {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F}
    {v : Fir.Val} {w : SourceValue F} (hr : TVR P cert feat h .w64 v w) :
    ∃ n : Nat, isU64Val n w ∧ v = .lit (.nat n) := by
  cases hr with
  | w64 hw => exact ⟨_, hw, rfl⟩

theorem TVR_enum_inv {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F}
    {ind : Src.CId} {v : Fir.Val} {w : SourceValue F}
    (hr : TVR P cert feat h (.enum ind) v w) :
    ∃ ks c idx entry,
      cert.enum? ind = some ks ∧ c.key ∈ ks ∧ P.ctors[idx]? = some entry ∧
      entry.key = c.key ∧ entry.arity = 0 ∧
      v = .ctor c [] ∧ w = .construct (enumQName ind) (ctorNameOf idx c.key) [] := by
  cases hr with
  | enumVal he hm hi hk ha => exact ⟨_, _, _, _, he, hm, hi, hk, ha, rfl, rfl⟩

theorem TVR_data_inv {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F}
    {d : Nat} {v : Fir.Val} {w : SourceValue F}
    (hr : TVR P cert feat h (.data d) v w) :
    ∃ D c fl idx entry fs ws,
      cert.data? d = some D ∧ (c.key, fl) ∈ D.ctors ∧ P.ctors[idx]? = some entry ∧
      entry.key = c.key ∧ fs.length = entry.arity ∧ fl.length = entry.arity ∧
      TVRDataFields P cert feat h d fl fs ws ∧
      v = .ctor c fs ∧ w = .construct (dataQName d) (ctorNameOf idx c.key) ws := by
  cases hr with
  | dataVal hd hc hi hk ha hfl hfs =>
    exact ⟨_, _, _, _, _, _, _, hd, hc, hi, hk, ha, hfl, hfs, rfl, rfl⟩

theorem TVR_obj_inv {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F}
    {v : Fir.Val} {w : SourceValue F} (hr : TVR P cert feat h .obj v w) :
    VR P objQName bytesQName h v w := by
  cases hr with
  | obj hvr => exact hvr

theorem TVR.fieldNat_inv {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F}
    {r : Rep} {v : Fir.Val} {w : SourceValue F}
    (hfn : r.isFieldNat = true) (hr : TVR P cert feat h r v w) :
    ∃ n : Nat, n < r.fieldBound ∧ n < natLimit ∧ v = .lit (.nat n) ∧ w = .field (n : F) := by
  cases r with
  | nat b =>
    obtain ⟨n, hsm, hlt, rfl, rfl⟩ := TVR_nat_inv hr
    exact ⟨n, hsm, hlt, rfl, rfl⟩
  | w8 =>
    obtain ⟨n, hsm, rfl, rfl⟩ := TVR_w8_inv hr
    exact ⟨n, hsm, lt_trans hsm (by decide), rfl, rfl⟩
  | w16 =>
    obtain ⟨n, hsm, rfl, rfl⟩ := TVR_w16_inv hr
    exact ⟨n, hsm, lt_trans hsm (by decide), rfl, rfl⟩
  | irr | w32 | w64 | «enum» _ | data _ | obj => simp [Rep.isFieldNat] at hfn

theorem TVR.of_fieldNat {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F}
    {r : Rep} {n : Nat} (hfn : r.isFieldNat = true) (hlt : n < r.fieldBound) :
    TVR P cert feat h r (.lit (.nat n)) (.field (n : F)) := by
  cases r with
  | nat b => exact .nat hlt
  | w8 => exact .w8 hlt
  | w16 => exact .w16 hlt
  | irr | w32 | w64 | «enum» _ | data _ | obj => simp [Rep.isFieldNat] at hfn

end TypedValueRel

/-! ## Section 3: Qualification, `tTrapE` Elimination, Demand Monotonicity, and `TypedLoweredWorld` -/

section WorldAndDemand

variable {F : Type} [Field F] [DecidableEq F]

private theorem digitChar_ne_colon {a : Nat} (ha : a < 10) : Nat.digitChar a ≠ ':' := by
  have : ∀ x : Fin 10, Nat.digitChar x.1 ≠ ':' := by decide
  exact this ⟨a, ha⟩

private theorem natDigits_no_colon : ∀ n c, c ∈ natDigits n → c ≠ ':' := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro c hc
    unfold natDigits at hc
    split at hc
    · simp only [List.mem_singleton] at hc
      subst hc
      exact digitChar_ne_colon ‹_›
    · simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hl | rfl
      · exact ih (n / 10) (by omega) c hl
      · exact digitChar_ne_colon (Nat.mod_lt n (by omega))

@[simp] theorem qualifyName_enumName (ind : Src.CId) :
    qualifyName (enumName ind) = enumQName ind := by
  unfold qualifyName enumQName
  have h : Lower.hasDoubleColon (enumName ind).toList = false := by
    apply Lower.hasDoubleColon_false_of_no_colon
    intro c hc
    simp only [enumName, String.toList_ofList, List.mem_cons] at hc
    rcases hc with rfl | hd
    · decide
    · exact natDigits_no_colon ind c hd
  simp [h]

@[simp] theorem qualifyName_dataName (d : Nat) :
    qualifyName (dataName d) = dataQName d := by
  unfold qualifyName dataQName
  have h : Lower.hasDoubleColon (dataName d).toList = false := by
    apply Lower.hasDoubleColon_false_of_no_colon
    intro c hc
    simp only [dataName, String.toList_ofList, List.mem_cons] at hc
    rcases hc with rfl | hd
    · decide
    · exact natDigits_no_colon d c hd
  simp [h]

/-- Any `seqE (assertEq(0, 1)) dv` expression (as emitted by `TypedLower.tTrapE`)
admits no `EvalExprN` derivation. -/
theorem evalExprN_assert01_elim {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {msg : String} {dv : Lower.Expr}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals
      (qualifyExprF F (seqE (.builtin (.assertEq (assertion msg)) [litE 0, litE 1]) dv)) h r h') :
    False := by
  simp only [seqE, litE, qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
    Aiur.Generic.Pattern.map, List.map] at ev
  obtain ⟨_, _, hass, _⟩ := evalExprN_let_wildcard_inv ev
  obtain ⟨vl, vr, _, ev0, ev1, heq, _⟩ := evalExpr_assertEq_inv hass.toEvalExpr
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
  exact (zero_ne_one (α := F)) (by simpa using Value.field.inj heq)

/-- Partial order on `TypedLower.Demand`: every demand bit set in `d1` is also set in `d2`. -/
structure DemandLe (d1 d2 : Demand) : Prop where
  needObj : d1.needObj = true → d2.needObj = true
  needBytes : d1.needBytes = true → d2.needBytes = true
  needCheckU56 : d1.needCheckU56 = true → d2.needCheckU56 = true
  needCheckU16 : d1.needCheckU16 = true → d2.needCheckU16 = true
  needCheckU24 : d1.needCheckU24 = true → d2.needCheckU24 = true
  needSubBorrow56 : d1.needSubBorrow56 = true → d2.needSubBorrow56 = true
  needMul56 : d1.needMul56 = true → d2.needMul56 = true
  needDivMod56 : d1.needDivMod56 = true → d2.needDivMod56 = true
  needPow56 : d1.needPow56 = true → d2.needPow56 = true
  needGcd56 : d1.needGcd56 = true → d2.needGcd56 = true
  needShl56 : d1.needShl56 = true → d2.needShl56 = true
  needShr56 : d1.needShr56 = true → d2.needShr56 = true
  needU32Mul : d1.needU32Mul = true → d2.needU32Mul = true
  needU32Comp : d1.needU32Comp = true → d2.needU32Comp = true
  needU32Div : d1.needU32Div = true → d2.needU32Div = true
  needU32Mod : d1.needU32Mod = true → d2.needU32Mod = true
  needU32Shl : d1.needU32Shl = true → d2.needU32Shl = true
  needU32Shr : d1.needU32Shr = true → d2.needU32Shr = true
  needU32OfField : d1.needU32OfField = true → d2.needU32OfField = true
  needU64Bitwise : d1.needU64Bitwise = true → d2.needU64Bitwise = true
  needU64Shl : d1.needU64Shl = true → d2.needU64Shl = true
  needU64Shr : d1.needU64Shr = true → d2.needU64Shr = true

theorem DemandLe.refl (d : Demand) : DemandLe d d :=
  ⟨id, id, id, id, id, id, id, id, id, id, id, id, id, id, id, id, id, id, id, id, id, id⟩

theorem DemandLe.trans {d1 d2 d3 : Demand} (h12 : DemandLe d1 d2) (h23 : DemandLe d2 d3) :
    DemandLe d1 d3 :=
  ⟨fun h => h23.needObj (h12.needObj h),
   fun h => h23.needBytes (h12.needBytes h),
   fun h => h23.needCheckU56 (h12.needCheckU56 h),
   fun h => h23.needCheckU16 (h12.needCheckU16 h),
   fun h => h23.needCheckU24 (h12.needCheckU24 h),
   fun h => h23.needSubBorrow56 (h12.needSubBorrow56 h),
   fun h => h23.needMul56 (h12.needMul56 h),
   fun h => h23.needDivMod56 (h12.needDivMod56 h),
   fun h => h23.needPow56 (h12.needPow56 h),
   fun h => h23.needGcd56 (h12.needGcd56 h),
   fun h => h23.needShl56 (h12.needShl56 h),
   fun h => h23.needShr56 (h12.needShr56 h),
   fun h => h23.needU32Mul (h12.needU32Mul h),
   fun h => h23.needU32Comp (h12.needU32Comp h),
   fun h => h23.needU32Div (h12.needU32Div h),
   fun h => h23.needU32Mod (h12.needU32Mod h),
   fun h => h23.needU32Shl (h12.needU32Shl h),
   fun h => h23.needU32Shr (h12.needU32Shr h),
   fun h => h23.needU32OfField (h12.needU32OfField h),
   fun h => h23.needU64Bitwise (h12.needU64Bitwise h),
   fun h => h23.needU64Shl (h12.needU64Shl h),
   fun h => h23.needU64Shr (h12.needU64Shr h)⟩

/-- World hypothesis for a typed lowered program `lp`:
* `TypedLower.lowerProgram P cert sched = .ok lp`;
* whenever `lp.tier ≠ .none`, `world` satisfies `ByteCheckSpec world (lp.tier == .u32 || lp.tier == .u64)`;
* whenever `lp.tier = .u64`, `world` satisfies `U64Contracts world`;
* every function in `lp.program.functions` is bound in `world` under `Prog::<name>` with its qualified body. -/
structure TypedLoweredWorld (P : Program) (cert : ShapeCert) (sched : CircuitSchedule)
    (lp : LoweredProgram) (world : World F) : Prop where
  lowered : TypedLower.lowerProgram P cert sched = .ok lp
  byteCheck : lp.tier ≠ .none → ByteCheckSpec world (lp.tier == .u32 || lp.tier == .u64)
  u64 : lp.tier = .u64 → U64Contracts world
  hasFn : ∀ g ∈ lp.program.functions,
    WorldHasFn world (Lower.qualified g.name) (g.params.map Prod.fst) (qualifyExprF F g.body)

/-- Discharge `TypedLoweredWorld` directly from the executable `TypedWorld.checkTypedWorld`
check (plus `checkU8FromFields` only in the `.u32` tier). -/
theorem typedLoweredWorld_of_check (fc : FieldCompatible64 F)
    {P : Program} {cert : ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    (hlow : TypedLower.lowerProgram P cert sched = .ok lp)
    (s : Generic.Source F)
    (hchk : checkTypedWorld s lp = true)
    (hu8f : lp.tier = .u32 → checkU8FromFields s = true) :
    TypedLoweredWorld P cert sched lp s.world := by
  unfold checkTypedWorld at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨htables, hfuncs⟩ := hchk
  have hall : ∀ g ∈ lp.program.functions, checkFunction s g = true := List.all_eq_true.mp hfuncs
  refine ⟨hlow, ?_, ?_, ?_⟩
  · intro hne
    cases ht : lp.tier with
    | none => exact False.elim (hne ht)
    | byte256 =>
      rw [ht] at htables
      exact byteCheckSpec_false_of_check htables
    | u32 =>
      rw [ht] at htables
      exact byteCheckSpec_true_of_check htables (hu8f ht)
    | u64 =>
      rw [ht] at htables
      simp only [Bool.and_eq_true] at htables
      exact byteCheckSpec_true_of_u64LibraryWorld
        (u64LibraryWorld_of_check s (u8TablesMatch_of_check htables.1) htables.2)
  · intro hu64
    rw [hu64] at htables
    simp only [Bool.and_eq_true] at htables
    exact U64Contracts.ofLibraryWorld
      (u64LibraryWorld_of_check s (u8TablesMatch_of_check htables.1) htables.2)
      fc.toFieldCompatible
  · intro g hg
    obtain ⟨f, hfind, htp, hparams, hbody⟩ := checkFunction_sound (hall g hg)
    have hnoDollar : (Lower.qualified g.name).toList.head? ≠ some '$' := by
      simp [Lower.qualified, moduleName]
    have hwf := worldHasFn_of_findFunction? s hnoDollar hfind htp
    rwa [hparams, hbody] at hwf

/-- Discharge `TypedLoweredWorld` solely from `checkTypedWorld` when `lp.tier ≠ .u32`
(holds automatically for all `.none`, `.byte256`, and `.u64` programs). -/
theorem typedLoweredWorld_of_check_noU32 (fc : FieldCompatible64 F)
    {P : Program} {cert : ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    (hlow : TypedLower.lowerProgram P cert sched = .ok lp)
    (hne32 : lp.tier ≠ .u32)
    (s : Generic.Source F)
    (hchk : checkTypedWorld s lp = true) :
    TypedLoweredWorld P cert sched lp s.world :=
  typedLoweredWorld_of_check fc hlow s hchk (fun h => False.elim (hne32 h))

/-! ### Unpacking `TypedLower.lowerProgram` and Helper Membership -/

/-- Exact structural unpacking of `TypedLower.lowerProgram P cert sched = .ok lp`. -/
theorem typedLowerProgram_inv {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} (h : TypedLower.lowerProgram P cert sched = .ok lp) :
    let feat := scanFeatures P
    let cx : TCx := { P, cert, feat, sched }
    (P.ctors.map (·.key)).Nodup ∧
    (objCtorNames P).Nodup ∧
    ∃ (stDatas stFuns stFinal : TState) (fnGroups : List (List Fn)) (entries : List (Fn × Rep)),
      stDatas.lifted = [] ∧
      P.funList.mapM (m := TLowerM) (fun (f, fd) => tFunE cx f fd) stDatas = .ok (fnGroups, stFuns) ∧
      ((List.range P.exports.length).zip P.exports).mapM (m := TLowerM) (fun (i, f) => tEntryE cx i f) stFuns =
        .ok (entries, stFinal) ∧
      lp.demand = stFinal.demand ∧
      lp.cert = cert ∧
      lp.exportReps = entries.map Prod.snd ∧
      (let d := stFinal.demand
       let usesRangeCheck :=
         d.needCheckU56 || d.needCheckU16 || d.needCheckU24 || d.needSubBorrow56 ||
         d.needMul56 || d.needDivMod56
       lp.tier =
         (if !sched.demandLink then .u64
          else if d.needU64Bitwise then .u64
          else tableTier feat sched usesRangeCheck)) ∧
      lp.program.functions =
        entries.map Prod.fst ++
        fnGroups.flatten.map IxCC.AiurBackend.Peephole.rewriteFn ++
        demandedHelpers stFinal.demand (lp.tier == .u32 || lp.tier == .u64) := by
  have hStep :
      ∀ (fMark : Rep → TLowerM Unit),
        (∀ r s, ∃ s', fMark r s = .ok ((), s') ∧ s'.lifted = s.lifted) →
        (do
          unless allDistinct (P.ctors.map (·.key)) do
            throw "duplicate constructor key in constructor table"
          unless allDistinct (objCtorNames P) do
            throw "duplicate constructor name in constructor table"
          let feat := scanFeatures P
          let cx : TCx := { P, cert, feat, sched }
          let ((fns, entriesWithReps), st) ← (do
            for entry in cx.cert.datas.zipIdx do
              let D : IxCC.Shape.DataDecl CtorKey := entry.1
              let d : Nat := entry.2
              if validData cx.P cx.cert d then
                for (_, fl) in D.ctors do
                  for sh in fl do
                    fMark (cx.rep sh)
            let fnGroups ← P.funList.mapM fun (f, fd) => tFunE cx f fd
            let entries ← ((List.range P.exports.length).zip P.exports).mapM fun (i, f) => tEntryE cx i f
            pure (fnGroups.flatten, entries) : TLowerM _).run {}
          let d := st.demand
          let usesRangeCheck :=
            d.needCheckU56 || d.needCheckU16 || d.needCheckU24 || d.needSubBorrow56 ||
            d.needMul56 || d.needDivMod56
          let tier :=
            if !sched.demandLink then .u64
            else if d.needU64Bitwise then .u64
            else tableTier feat sched usesRangeCheck
          let usePair := tier == .u32 || tier == .u64
          let helpers := demandedHelpers d usePair
          let enums :=
            enumDecls cx ++
            dataDecls cx ++
            (if d.needBytes || d.needObj then [Lower.bytesEnumDecl] else []) ++
            (if d.needObj then [Lower.objEnumDecl P] else [])
          let fns := fns.map IxCC.AiurBackend.Peephole.rewriteFn
          return {
            program := { functions := entriesWithReps.map Prod.fst ++ fns ++ helpers, enums }
            tier
            exportReps := entriesWithReps.map Prod.snd
            demand := d
            cert
          } : Except String LoweredProgram) = .ok lp →
        let feat := scanFeatures P
        let cx : TCx := { P, cert, feat, sched }
        (P.ctors.map (·.key)).Nodup ∧
        (objCtorNames P).Nodup ∧
        ∃ (stDatas stFuns stFinal : TState) (fnGroups : List (List Fn)) (entries : List (Fn × Rep)),
          stDatas.lifted = [] ∧
          P.funList.mapM (m := TLowerM) (fun (f, fd) => tFunE cx f fd) stDatas = .ok (fnGroups, stFuns) ∧
          ((List.range P.exports.length).zip P.exports).mapM (m := TLowerM) (fun (i, f) => tEntryE cx i f) stFuns =
            .ok (entries, stFinal) ∧
          lp.demand = stFinal.demand ∧
          lp.cert = cert ∧
          lp.exportReps = entries.map Prod.snd ∧
          (let d := stFinal.demand
           let usesRangeCheck :=
             d.needCheckU56 || d.needCheckU16 || d.needCheckU24 || d.needSubBorrow56 ||
             d.needMul56 || d.needDivMod56
           lp.tier =
             (if !sched.demandLink then .u64
              else if d.needU64Bitwise then .u64
              else tableTier feat sched usesRangeCheck)) ∧
          lp.program.functions =
            entries.map Prod.fst ++
            fnGroups.flatten.map IxCC.AiurBackend.Peephole.rewriteFn ++
            demandedHelpers stFinal.demand (lp.tier == .u32 || lp.tier == .u64) := by
    intro fMark hMark hrun
    by_cases hk : allDistinct (P.ctors.map (·.key)) = true
    · simp only [hk, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hrun
      by_cases hn : allDistinct (objCtorNames P) = true
      · simp only [hn, ↓reduceIte] at hrun
        set feat := scanFeatures P
        set cx : TCx := { P, cert, feat, sched }
        have hDatas : ∃ stDatas : TState,
            (forIn (cert.datas.zipIdx) PUnit.unit fun entry _ =>
              if validData P cert entry.2 = true then
                StateT.bind
                  (forIn entry.1.ctors PUnit.unit fun x _ =>
                    StateT.bind
                      (forIn x.2 PUnit.unit fun sh _ =>
                        StateT.bind (fMark (cx.rep sh)) fun _ =>
                          StateT.pure (ForInStep.yield PUnit.unit))
                      fun _ => StateT.pure (ForInStep.yield PUnit.unit))
                  fun _ => StateT.pure (ForInStep.yield PUnit.unit)
              else StateT.pure (ForInStep.yield PUnit.unit) : TLowerM PUnit) {} =
              .ok (PUnit.unit, stDatas) ∧
            stDatas.lifted = [] := by
          have hForS : ∀ {α : Type} (xs : List α) (body : α → TLowerM (ForInStep PUnit)),
              (∀ a s, ∃ s', body a s = .ok (ForInStep.yield PUnit.unit, s') ∧ s'.lifted = s.lifted) →
              ∀ s, ∃ s', (forIn xs PUnit.unit (fun a _ => body a) : TLowerM PUnit) s =
                .ok (PUnit.unit, s') ∧ s'.lifted = s.lifted := by
            intro α xs body hbody
            induction xs with
            | nil => intro s; exact ⟨s, rfl, rfl⟩
            | cons a tl ih =>
              intro s
              obtain ⟨s1, h1, hlf1⟩ := hbody a s
              obtain ⟨s2, h2, hlf2⟩ := ih s1
              refine ⟨s2, ?_, hlf2.trans hlf1⟩
              simp only [forIn, List.forIn'_cons, bind, StateT.bind, Except.bind, h1]
              exact h2
          apply hForS (cert.datas.zipIdx)
          intro entry s
          by_cases hv : validData P cert entry.2 = true
          · simp only [hv, ↓reduceIte]
            have h1 := hForS entry.1.ctors
              (fun x => StateT.bind
                (forIn x.2 PUnit.unit fun sh _ =>
                  StateT.bind (fMark (cx.rep sh)) fun _ =>
                    StateT.pure (ForInStep.yield PUnit.unit))
                fun _ => StateT.pure (ForInStep.yield PUnit.unit))
              (fun x s0 => by
                have h2 := hForS x.2
                  (fun sh => StateT.bind (fMark (cx.rep sh)) fun _ =>
                    StateT.pure (ForInStep.yield PUnit.unit))
                  (fun sh s1 => by
                    obtain ⟨s2, hm, hlf⟩ := hMark (cx.rep sh) s1
                    exact ⟨s2, by simp [StateT.bind, StateT.pure, hm], hlf⟩) s0
                obtain ⟨s2, h2eq, hlf⟩ := h2
                exact ⟨s2, by simp [StateT.bind, StateT.pure, h2eq], hlf⟩) s
            obtain ⟨s2, h2eq, hlf⟩ := h1
            exact ⟨s2, by simp [StateT.bind, StateT.pure, h2eq], hlf⟩
          · simp only [hv]
            exact ⟨s, rfl, rfl⟩
        obtain ⟨stDatas, hDatasEq, hDatasLifted⟩ := hDatas
        simp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure] at hrun
        rw [hDatasEq] at hrun
        simp only at hrun
        cases hfg : P.funList.mapM (m := TLowerM) (fun (f, fd) => tFunE cx f fd) stDatas with
        | error err => simp [hfg] at hrun
        | ok res1 =>
          rcases res1 with ⟨fnGroups, stFuns⟩
          simp only [hfg] at hrun
          cases hen : ((List.range P.exports.length).zip P.exports).mapM (m := TLowerM) (fun (i, f) => tEntryE cx i f) stFuns with
          | error err => simp [hen] at hrun
          | ok res2 =>
            rcases res2 with ⟨entries, stFinal⟩
            simp only [hen, Except.ok.injEq] at hrun
            subst hrun
            exact ⟨(Lower.allDistinct_iff_nodup _).mp hk, (Lower.allDistinct_iff_nodup _).mp hn,
              stDatas, stFuns, stFinal, fnGroups, entries, hDatasLifted, hfg, hen,
              rfl, rfl, rfl, rfl, rfl⟩
      · have hnf : allDistinct (objCtorNames P) = false := Bool.eq_false_iff.mpr hn
        simp [hnf, throw, throwThe, MonadExceptOf.throw] at hrun
    · have hkf : allDistinct (P.ctors.map (·.key)) = false := Bool.eq_false_iff.mpr hk
      simp [hkf, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hrun
  exact hStep _ (fun r s => by cases r <;> exact ⟨_, rfl, rfl⟩) h

/-- Whenever any 56-bit/16-bit/24-bit range-check or subtraction/mul/divmod bit is
set in `lp.demand`, `lp.tier ≠ .none`. -/
theorem tier_ne_none_of_usesRangeCheck {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram}
    (h : TypedLower.lowerProgram P cert sched = .ok lp)
    (hrc : (lp.demand.needCheckU56 || lp.demand.needCheckU16 || lp.demand.needCheckU24 ||
            lp.demand.needSubBorrow56 || lp.demand.needMul56 || lp.demand.needDivMod56) = true) :
    lp.tier ≠ .none := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hdem, _, _, htier, _⟩ := typedLowerProgram_inv h
  rw [htier, ← hdem, hrc]
  by_cases hdl : sched.demandLink = true
  · simp only [hdl, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases hu64 : lp.demand.needU64Bitwise = true
    · simp [hu64]
    · simp only [hu64, Bool.false_eq_true, ↓reduceIte, tableTier]
      split
      · simp
      · split
        · simp
        · simp only [Bool.or_true, ↓reduceIte]
          cases sched.rangeCheck <;> simp
  · have hdlf : sched.demandLink = false := Bool.eq_false_iff.mpr hdl
    simp [hdlf]

/-- Whenever `lp.demand.needU64Bitwise = true`, `lp.tier = .u64`. -/
theorem tier_eq_u64_of_needU64Bitwise {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram}
    (h : TypedLower.lowerProgram P cert sched = .ok lp)
    (hu64 : lp.demand.needU64Bitwise = true) :
    lp.tier = .u64 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hdem, _, _, htier, _⟩ := typedLowerProgram_inv h
  rw [htier, ← hdem, hu64]
  cases sched.demandLink <;> simp

/-- Helper: `lp.tier ≠ .u32` whenever `(scanFeatures P).usesW32 = false`. -/
theorem tier_ne_u32_of_not_usesW32 {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram}
    (h : TypedLower.lowerProgram P cert sched = .ok lp)
    (hw32 : (scanFeatures P).usesW32 = false) :
    lp.tier ≠ .u32 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, htier, _⟩ := typedLowerProgram_inv h
  rw [htier]
  cases sched.demandLink
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split
    · simp
    · unfold tableTier
      simp only [hw32, Bool.false_eq_true, ↓reduceIte]
      split
      · simp
      · split
        · cases sched.rangeCheck <;> simp
        · simp

/-! ### Helper Membership in `demandedHelpers` & `TypedLoweredWorld` -/

private theorem mem_demandedHelpers_of_flag {d : Demand} {usePair : Bool} {g : Fn}
    (h : g ∈ demandedHelpers d usePair) :
    ∀ {P cert sched lp} {world : World F},
      TypedLoweredWorld P cert sched lp world →
      lp.demand = d → (lp.tier == .u32 || lp.tier == .u64) = usePair →
      WorldHasFn world (Lower.qualified g.name) (g.params.map Prod.fst) (qualifyExprF F g.body) := by
  intro P cert sched lp world lw hdem hpair
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hdem', _, _, _, hfuncs⟩ := typedLowerProgram_inv lw.lowered
  apply lw.hasFn g
  rw [hfuncs]
  apply List.mem_append_right
  rw [← hdem', hdem, hpair]
  exact h

theorem TypedLoweredWorld.hasCheckU8 {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram} {world : World F}
    (lw : TypedLoweredWorld P cert sched lp world)
    (hd : lp.demand.needCheckU56 = true ∨ lp.demand.needMul56 = true ∨ lp.demand.needDivMod56 = true) :
    WorldHasFn world (Lower.qualified "check_u8") ["x"]
      (qualifyExprF F (checkU8Fn (lp.tier == .u32 || lp.tier == .u64)).body) := by
  have hcond : (lp.demand.needCheckU56 || lp.demand.needMul56 || lp.demand.needDivMod56) = true := by
    rcases hd with h | h | h <;> simp [h]
  have hmem : checkU8Fn (lp.tier == .u32 || lp.tier == .u64) ∈
      demandedHelpers lp.demand (lp.tier == .u32 || lp.tier == .u64) := by
    unfold demandedHelpers
    simp [hcond]
  simpa [checkU8Fn] using mem_demandedHelpers_of_flag hmem lw rfl rfl

theorem TypedLoweredWorld.hasCheckU56 {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram} {world : World F}
    (lw : TypedLoweredWorld P cert sched lp world)
    (hd : lp.demand.needCheckU56 = true ∨ lp.demand.needMul56 = true ∨ lp.demand.needDivMod56 = true) :
    WorldHasFn world (Lower.qualified "check_u56") ["x"]
      (qualifyExprF F (checkU56Fn (lp.tier == .u32 || lp.tier == .u64)).body) := by
  have hcond : (lp.demand.needCheckU56 || lp.demand.needMul56 || lp.demand.needDivMod56) = true := by
    rcases hd with h | h | h <;> simp [h]
  have hmem : checkU56Fn (lp.tier == .u32 || lp.tier == .u64) ∈
      demandedHelpers lp.demand (lp.tier == .u32 || lp.tier == .u64) := by
    unfold demandedHelpers
    simp [hcond]
  simpa [checkU56Fn] using mem_demandedHelpers_of_flag hmem lw rfl rfl

theorem TypedLoweredWorld.hasCheckU16 {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram} {world : World F}
    (lw : TypedLoweredWorld P cert sched lp world) (hd : lp.demand.needCheckU16 = true) :
    WorldHasFn world (Lower.qualified "check_u16") ["x"]
      (qualifyExprF F (checkU16Fn (lp.tier == .u32 || lp.tier == .u64)).body) := by
  have hmem : checkU16Fn (lp.tier == .u32 || lp.tier == .u64) ∈
      demandedHelpers lp.demand (lp.tier == .u32 || lp.tier == .u64) := by
    unfold demandedHelpers
    simp [hd]
  simpa [checkU16Fn] using mem_demandedHelpers_of_flag hmem lw rfl rfl

theorem TypedLoweredWorld.hasCheckU24 {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram} {world : World F}
    (lw : TypedLoweredWorld P cert sched lp world)
    (hd : lp.demand.needCheckU24 = true ∨ lp.demand.needMul56 = true) :
    WorldHasFn world (Lower.qualified "check_u24") ["x"]
      (qualifyExprF F (checkU24Fn (lp.tier == .u32 || lp.tier == .u64)).body) := by
  have hcond : (lp.demand.needCheckU24 || lp.demand.needMul56) = true := by
    rcases hd with h | h <;> simp [h]
  have hmem : checkU24Fn (lp.tier == .u32 || lp.tier == .u64) ∈
      demandedHelpers lp.demand (lp.tier == .u32 || lp.tier == .u64) := by
    unfold demandedHelpers
    simp [hcond]
  simpa [checkU24Fn] using mem_demandedHelpers_of_flag hmem lw rfl rfl

theorem TypedLoweredWorld.hasSubBorrow56 {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram} {world : World F}
    (lw : TypedLoweredWorld P cert sched lp world) (hd : lp.demand.needSubBorrow56 = true) :
    WorldHasFn world (Lower.qualified "sub_borrow_56") ["x", "y"]
      (qualifyExprF F (subBorrow56Fn (lp.tier == .u32 || lp.tier == .u64)).body) := by
  have hmem : subBorrow56Fn (lp.tier == .u32 || lp.tier == .u64) ∈
      demandedHelpers lp.demand (lp.tier == .u32 || lp.tier == .u64) := by
    unfold demandedHelpers
    simp [hd]
  simpa [subBorrow56Fn] using mem_demandedHelpers_of_flag hmem lw rfl rfl

theorem TypedLoweredWorld.hasSplit32_24 {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram} {world : World F}
    (lw : TypedLoweredWorld P cert sched lp world) (hd : lp.demand.needMul56 = true) :
    WorldHasFn world (Lower.qualified "split_32_24") ["x"]
      (qualifyExprF F (split32_24Fn (lp.tier == .u32 || lp.tier == .u64)).body) := by
  have hmem : split32_24Fn (lp.tier == .u32 || lp.tier == .u64) ∈
      demandedHelpers lp.demand (lp.tier == .u32 || lp.tier == .u64) := by
    unfold demandedHelpers
    simp [hd]
  simpa [split32_24Fn] using mem_demandedHelpers_of_flag hmem lw rfl rfl

theorem TypedLoweredWorld.hasMul56 {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram} {world : World F}
    (lw : TypedLoweredWorld P cert sched lp world) (hd : lp.demand.needMul56 = true) :
    WorldHasFn world (Lower.qualified "mul_56") ["x", "y"] (qualifyExprF F mul56Fn.body) := by
  have hmem : mul56Fn ∈ demandedHelpers lp.demand (lp.tier == .u32 || lp.tier == .u64) := by
    unfold demandedHelpers; simp [hd]
  simpa [mul56Fn] using mem_demandedHelpers_of_flag hmem lw rfl rfl

theorem TypedLoweredWorld.hasDivMod56 {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram} {world : World F}
    (lw : TypedLoweredWorld P cert sched lp world) (hd : lp.demand.needDivMod56 = true) :
    WorldHasFn world (Lower.qualified "divmod_56") ["x", "y"] (qualifyExprF F divmod56Fn.body) := by
  have hmem : divmod56Fn ∈ demandedHelpers lp.demand (lp.tier == .u32 || lp.tier == .u64) := by
    unfold demandedHelpers; simp [hd]
  simpa [divmod56Fn] using mem_demandedHelpers_of_flag hmem lw rfl rfl

theorem TypedLoweredWorld.hasPow56Loop {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram} {world : World F}
    (lw : TypedLoweredWorld P cert sched lp world) (hd : lp.demand.needPow56 = true) :
    WorldHasFn world (Lower.qualified "pow_56_loop") ["base", "exp", "acc"]
      (qualifyExprF F pow56LoopFn.body) := by
  have hmem : pow56LoopFn ∈ demandedHelpers lp.demand (lp.tier == .u32 || lp.tier == .u64) := by
    unfold demandedHelpers; simp [hd]
  simpa [pow56LoopFn] using mem_demandedHelpers_of_flag hmem lw rfl rfl

theorem TypedLoweredWorld.hasPow56 {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram} {world : World F}
    (lw : TypedLoweredWorld P cert sched lp world) (hd : lp.demand.needPow56 = true) :
    WorldHasFn world (Lower.qualified "pow_56") ["base", "exp"] (qualifyExprF F pow56Fn.body) := by
  have hmem : pow56Fn ∈ demandedHelpers lp.demand (lp.tier == .u32 || lp.tier == .u64) := by
    unfold demandedHelpers; simp [hd]
  simpa [pow56Fn] using mem_demandedHelpers_of_flag hmem lw rfl rfl

theorem TypedLoweredWorld.hasGcd56 {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram} {world : World F}
    (lw : TypedLoweredWorld P cert sched lp world) (hd : lp.demand.needGcd56 = true) :
    WorldHasFn world (Lower.qualified "gcd_56") ["a", "b"] (qualifyExprF F gcd56Fn.body) := by
  have hmem : gcd56Fn ∈ demandedHelpers lp.demand (lp.tier == .u32 || lp.tier == .u64) := by
    unfold demandedHelpers; simp [hd]
  simpa [gcd56Fn] using mem_demandedHelpers_of_flag hmem lw rfl rfl

theorem TypedLoweredWorld.hasShl56 {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram} {world : World F}
    (lw : TypedLoweredWorld P cert sched lp world) (hd : lp.demand.needShl56 = true) :
    WorldHasFn world (Lower.qualified "shl_56") ["x", "k"] (qualifyExprF F shl56Fn.body) := by
  have hmem : shl56Fn ∈ demandedHelpers lp.demand (lp.tier == .u32 || lp.tier == .u64) := by
    unfold demandedHelpers; simp [hd]
  simpa [shl56Fn] using mem_demandedHelpers_of_flag hmem lw rfl rfl

theorem TypedLoweredWorld.hasShr56 {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram} {world : World F}
    (lw : TypedLoweredWorld P cert sched lp world) (hd : lp.demand.needShr56 = true) :
    WorldHasFn world (Lower.qualified "shr_56") ["x", "k"] (qualifyExprF F shr56Fn.body) := by
  have hmem : shr56Fn ∈ demandedHelpers lp.demand (lp.tier == .u32 || lp.tier == .u64) := by
    unfold demandedHelpers; simp [hd]
  simpa [shr56Fn] using mem_demandedHelpers_of_flag hmem lw rfl rfl

end WorldAndDemand

/-! ## Section 4: `Peephole.rewriteExpr` Backward Simulation on `noU32Calls` Expressions -/

section PeepholeSim

/-- Names of `UInt32` helpers inspected by `IxCC.AiurBackend.Peephole`. -/
def isPeepholeU32Name (nm : String) : Bool :=
  nm == "UInt32::add" || nm == "UInt32::sub" || nm == "UInt32::or" || nm == "UInt32::xor" ||
  nm == "UInt32::from_field" || nm == "UInt32::from_fields" ||
  nm == "u32_of_field" || nm == "Prog::u32_of_field" ||
  nm == "u32_shr" || nm == "Prog::u32_shr" ||
  nm == "u32_shl" || nm == "Prog::u32_shl"

mutual

/-- Patterns emitted by `TypedLower` (no `.global`, `.orElse`, `.load`, `.repeat`, `.record`, `.constructAs`). -/
def isSimplePat : Lower.Pat → Bool
  | .literal _ | .wildcard | .bind _ => true
  | .tuple ps | .array ps | .construct _ _ ps => isSimplePatList ps
  | _ => false

def isSimplePatList : List Lower.Pat → Bool
  | [] => true
  | p :: ps => isSimplePat p && isSimplePatList ps

end

mutual

/-- Expressions that are plain (`isPlainExpr`), use only simple patterns, and contain
no `UInt32` calls inspected by `Peephole`. -/
def isCleanNoU32 : Lower.Expr → Bool
  | .control .. | .global .. => false
  | .literal _ | .var _ => true
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs => isCleanNoU32List xs
  | .call nm _ xs => !isPeepholeU32Name nm && isCleanNoU32List xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x => isCleanNoU32 x
  | .binary _ l r => isCleanNoU32 l && isCleanNoU32 r
  | .letValue p v b => isSimplePat p && isCleanNoU32 v && isCleanNoU32 b
  | .matchValue s arms => isCleanNoU32 s && isCleanNoU32Arms arms

def isCleanNoU32List : List Lower.Expr → Bool
  | [] => true
  | x :: xs => isCleanNoU32 x && isCleanNoU32List xs

def isCleanNoU32Arms : List (Lower.Pat × Lower.Expr) → Bool
  | [] => true
  | (p, b) :: rest => isSimplePat p && isCleanNoU32 b && isCleanNoU32Arms rest

end

theorem isSimplePatList_iff {ps : List Lower.Pat} :
    isSimplePatList ps = true ↔ ∀ p ∈ ps, isSimplePat p = true := by
  induction ps with
  | nil => simp [isSimplePatList]
  | cons p tl ih =>
    simp only [isSimplePatList, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp, ih]

theorem isCleanNoU32List_iff {xs : List Lower.Expr} :
    isCleanNoU32List xs = true ↔ ∀ x ∈ xs, isCleanNoU32 x = true := by
  induction xs with
  | nil => simp [isCleanNoU32List]
  | cons x tl ih =>
    simp only [isCleanNoU32List, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp, ih]

theorem isCleanNoU32Arms_iff {arms : List (Lower.Pat × Lower.Expr)} :
    isCleanNoU32Arms arms = true ↔ ∀ a ∈ arms, isSimplePat a.1 = true ∧ isCleanNoU32 a.2 = true := by
  induction arms with
  | nil => simp [isCleanNoU32Arms]
  | cons a tl ih =>
    rcases a with ⟨p, b⟩
    simp only [isCleanNoU32Arms, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp, ih]

mutual

theorem isPlainExpr_of_isCleanNoU32 : ∀ {e : Lower.Expr}, isCleanNoU32 e = true → isPlainExpr e = true
  | .control .., h | .global .., h => by simp [isCleanNoU32] at h
  | .literal _, _ | .var _, _ => rfl
  | .tuple xs, h | .array xs, h | .construct _ _ _ xs, h | .constructAs _ _ _ xs, h
  | .record _ xs, h | .update _ xs, h | .builtin _ xs, h =>
    isPlainList_of_isCleanNoU32List h
  | .call _ _ xs, h => by
    simp only [isCleanNoU32, Bool.and_eq_true] at h
    exact isPlainList_of_isCleanNoU32List h.2
  | .repeat x _, h | .index x _, h | .slice x _ _, h | .member x _, h | .project x _, h
  | .store x, h | .load x, h | .hint _ x _, h | .neg x, h =>
    isPlainExpr_of_isCleanNoU32 (e := x) h
  | .binary _ l r, h => by
    simp only [isCleanNoU32, Bool.and_eq_true] at h
    simp [isPlainExpr, isPlainExpr_of_isCleanNoU32 h.1, isPlainExpr_of_isCleanNoU32 h.2]
  | .letValue _ v b, h => by
    simp only [isCleanNoU32, Bool.and_eq_true] at h
    simp [isPlainExpr, isPlainExpr_of_isCleanNoU32 h.1.2, isPlainExpr_of_isCleanNoU32 h.2]
  | .matchValue s arms, h => by
    simp only [isCleanNoU32, Bool.and_eq_true] at h
    simp [isPlainExpr, isPlainExpr_of_isCleanNoU32 h.1, isPlainArms_of_isCleanNoU32Arms h.2]

theorem isPlainList_of_isCleanNoU32List :
    ∀ {xs : List Lower.Expr}, isCleanNoU32List xs = true → isPlainList xs = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [isCleanNoU32List, Bool.and_eq_true] at h
    simp [isPlainList, isPlainExpr_of_isCleanNoU32 h.1, isPlainList_of_isCleanNoU32List h.2]

theorem isPlainArms_of_isCleanNoU32Arms :
    ∀ {arms : List (Lower.Pat × Lower.Expr)}, isCleanNoU32Arms arms = true → isPlainArms arms = true
  | [], _ => rfl
  | (_, b) :: rest, h => by
    simp only [isCleanNoU32Arms, Bool.and_eq_true] at h
    simp [isPlainArms, isPlainExpr_of_isCleanNoU32 h.1.2, isPlainArms_of_isCleanNoU32Arms h.2]

end

private theorem extractU32Const?_of_clean {env : Peephole.ConstEnv} {e : Lower.Expr} {k : Nat}
    (hc : isCleanNoU32 e = true) (h : Peephole.extractU32Const? env e = some k) :
    (∃ c, e = .literal c) ∨ (∃ nm, e = .var nm ∧ env.lookup nm = some k) := by
  unfold Peephole.extractU32Const? at h
  split at h
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl, h⟩
  · next nm c =>
    simp only [isCleanNoU32, Bool.and_eq_true, Bool.not_eq_true'] at hc
    split at h
    · next hnm =>
      simp only [Peephole.isU32OfFieldName, Bool.or_eq_true, beq_iff_eq] at hnm
      rcases hnm with (rfl | rfl) | rfl <;> simp [isPeepholeU32Name] at hc
    · cases h
  · simp [isCleanNoU32, isPeepholeU32Name] at hc
  · simp [isCleanNoU32, isPeepholeU32Name] at hc
  · cases h

private theorem matchAdd_eq_none_of_clean {e : Lower.Expr} (hc : isCleanNoU32 e = true) :
    Peephole.matchAdd e = none := by
  unfold Peephole.matchAdd
  split
  · simp [isCleanNoU32, isPeepholeU32Name] at hc
  · rfl

private theorem matchXor_eq_none_of_clean {e : Lower.Expr} (hc : isCleanNoU32 e = true) :
    Peephole.matchXor e = none := by
  unfold Peephole.matchXor
  split
  · simp [isCleanNoU32, isPeepholeU32Name] at hc
  · rfl

private theorem matchShiftConst_eq_none_of_clean {env : Peephole.ConstEnv} {e : Lower.Expr}
    (hc : isCleanNoU32 e = true) :
    Peephole.matchShiftConst env e = none := by
  unfold Peephole.matchShiftConst
  split
  · next nm _ _ =>
    simp only [isCleanNoU32, Bool.and_eq_true, Bool.not_eq_true'] at hc
    by_cases h1 : Peephole.isShrName nm = true
    · simp only [Peephole.isShrName, Bool.or_eq_true, beq_iff_eq] at h1
      rcases h1 with rfl | rfl <;> simp [isPeepholeU32Name] at hc
    · by_cases h2 : Peephole.isShlName nm = true
      · simp only [Peephole.isShlName, Bool.or_eq_true, beq_iff_eq] at h2
        rcases h2 with rfl | rfl <;> simp [isPeepholeU32Name] at hc
      · simp [h1, h2]
  · rfl

private theorem tryFuseCall_eq_none_of_clean {env : Peephole.ConstEnv} {nm : String}
    {ts : Option (List Lower.Ty)} {xs : List Lower.Expr}
    (hnm : isPeepholeU32Name nm = false) :
    Peephole.tryFuseCall env nm ts xs = none := by
  unfold Peephole.tryFuseCall
  split
  · have hadd : (nm == "UInt32::add") = false := by
      cases h : nm == "UInt32::add"
      · rfl
      · exfalso; rw [beq_iff_eq] at h; subst h; simp [isPeepholeU32Name] at hnm
    have hor : (nm == "UInt32::or") = false := by
      cases h : nm == "UInt32::or"
      · rfl
      · exfalso; rw [beq_iff_eq] at h; subst h; simp [isPeepholeU32Name] at hnm
    have hsh : (Peephole.isShrName nm || Peephole.isShlName nm) = false := by
      cases h : Peephole.isShrName nm || Peephole.isShlName nm
      · rfl
      · exfalso
        simp only [Bool.or_eq_true, Peephole.isShrName, Peephole.isShlName, beq_iff_eq] at h
        rcases h with (rfl | rfl) | (rfl | rfl) <;> simp [isPeepholeU32Name] at hnm
    simp [hadd, hor, hsh]
  · rfl

private theorem tryLowerByteShift_eq_none_of_clean {env : Peephole.ConstEnv} {nm : String}
    {ts : Option (List Lower.Ty)} {xs : List Lower.Expr}
    (hnm : isPeepholeU32Name nm = false) :
    Peephole.tryLowerByteShift env nm ts xs = none := by
  unfold Peephole.tryLowerByteShift
  split
  · have h1 : Peephole.isShrName nm = false := by
      cases h : Peephole.isShrName nm
      · rfl
      · exfalso; simp only [Peephole.isShrName, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with rfl | rfl <;> simp [isPeepholeU32Name] at hnm
    have h2 : Peephole.isShlName nm = false := by
      cases h : Peephole.isShlName nm
      · rfl
      · exfalso; simp only [Peephole.isShlName, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with rfl | rfl <;> simp [isPeepholeU32Name] at hnm
    simp [h1, h2]
  · rfl

private theorem tryFuseLet_of_clean {env : Peephole.ConstEnv} {nm : String} {v b : Lower.Expr}
    (hv : isCleanNoU32 v = true) :
    Peephole.tryFuseLet env nm v b = Peephole.tryDropDeadConst env nm v b := by
  unfold Peephole.tryFuseLet
  cases hd : Peephole.tryDropDeadConst env nm v b with
  | some e => rfl
  | none =>
    have hadd : Peephole.tryFuseLetAdd3 nm v b = none := by
      unfold Peephole.tryFuseLetAdd3; rw [matchAdd_eq_none_of_clean hv]
    have hrot : Peephole.tryFuseLetRotr env nm v b = none := by
      unfold Peephole.tryFuseLetRotr; rw [matchShiftConst_eq_none_of_clean hv]
    have hxr4 : Peephole.tryFuseLetXorRotr4 env nm v b = none := by
      unfold Peephole.tryFuseLetXorRotr4; rw [matchXor_eq_none_of_clean hv]
    have hxrh : Peephole.tryFuseLetXorRotrHalf env nm v b = none := by
      unfold Peephole.tryFuseLetXorRotrHalf; rw [matchXor_eq_none_of_clean hv]
    simp [hadd, hrot, hxr4, hxrh]

mutual

theorem isCleanNoU32_fuseExpr (env : Peephole.ConstEnv) :
    ∀ {e : Lower.Expr}, isCleanNoU32 e = true → isCleanNoU32 (Peephole.fuseExpr env e) = true
  | .control .., h | .global .., h => by simp [isCleanNoU32] at h
  | .literal _, _ | .var _, _ => rfl
  | .tuple xs, h | .array xs, h | .construct _ _ _ xs, h | .constructAs _ _ _ xs, h
  | .record _ xs, h | .update _ xs, h | .builtin _ xs, h =>
    isCleanNoU32List_fuseList env h
  | .repeat x _, h | .index x _, h | .slice x _ _, h | .member x _, h | .project x _, h
  | .store x, h | .load x, h | .hint _ x _, h | .neg x, h =>
    isCleanNoU32_fuseExpr env (e := x) h
  | .binary _ l r, h => by
    simp only [isCleanNoU32, Bool.and_eq_true] at h
    simp [Peephole.fuseExpr, isCleanNoU32,
      isCleanNoU32_fuseExpr env h.1, isCleanNoU32_fuseExpr env h.2]
  | .call nm ts xs, h => by
    simp only [isCleanNoU32, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [Peephole.fuseExpr, tryFuseCall_eq_none_of_clean h.1, Option.getD_none,
      isCleanNoU32, h.1, Bool.not_false, Bool.true_and]
    exact isCleanNoU32List_fuseList env h.2
  | .letValue p v b, h => by
    simp only [isCleanNoU32, Bool.and_eq_true] at h
    obtain ⟨⟨hp, hv⟩, hb⟩ := h
    have hv' := isCleanNoU32_fuseExpr env hv
    cases p with
    | bind nm =>
      simp only [Peephole.fuseExpr]
      rw [tryFuseLet_of_clean hv']
      unfold Peephole.tryDropDeadConst
      cases hce : Peephole.extractU32Const? env (Peephole.fuseExpr env v) with
      | none =>
        have hb' := isCleanNoU32_fuseExpr (Peephole.envRemove [nm] env) hb
        simp [isCleanNoU32, isSimplePat, hv', hb']
      | some k0 =>
        have hb' := isCleanNoU32_fuseExpr ((nm, k0) :: Peephole.envRemove [nm] env) hb
        dsimp only
        split
        · exact hb'
        · simp [isCleanNoU32, isSimplePat, hv', hb']
    | literal _ | wildcard | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      simp only [Peephole.fuseExpr, isCleanNoU32, hp, hv', Bool.true_and]
      exact isCleanNoU32_fuseExpr _ hb
  | .matchValue s arms, h => by
    simp only [isCleanNoU32, Bool.and_eq_true] at h
    simp [Peephole.fuseExpr, isCleanNoU32,
      isCleanNoU32_fuseExpr env h.1, isCleanNoU32Arms_fuseArms env h.2]

theorem isCleanNoU32List_fuseList (env : Peephole.ConstEnv) :
    ∀ {xs : List Lower.Expr},
      isCleanNoU32List xs = true → isCleanNoU32List (Peephole.fuseList env xs) = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [isCleanNoU32List, Bool.and_eq_true] at h
    simp [Peephole.fuseList, isCleanNoU32List,
      isCleanNoU32_fuseExpr env h.1, isCleanNoU32List_fuseList env h.2]

theorem isCleanNoU32Arms_fuseArms (env : Peephole.ConstEnv) :
    ∀ {arms : List (Lower.Pat × Lower.Expr)},
      isCleanNoU32Arms arms = true → isCleanNoU32Arms (Peephole.fuseArms env arms) = true
  | [], _ => rfl
  | (p, b) :: rest, h => by
    simp only [isCleanNoU32Arms, Bool.and_eq_true] at h
    simp [Peephole.fuseArms, isCleanNoU32Arms, h.1.1,
      isCleanNoU32_fuseExpr _ h.1.2, isCleanNoU32Arms_fuseArms env h.2]

end

mutual

theorem lowerByteShifts_eq_self_of_clean (env : Peephole.ConstEnv) :
    ∀ {e : Lower.Expr}, isCleanNoU32 e = true → Peephole.lowerByteShifts env e = e
  | .control .., h | .global .., h => by simp [isCleanNoU32] at h
  | .literal _, _ | .var _, _ => rfl
  | .tuple xs, h | .array xs, h | .construct _ _ _ xs, h | .constructAs _ _ _ xs, h
  | .record _ xs, h | .update _ xs, h | .builtin _ xs, h => by
    simp [Peephole.lowerByteShifts, lowerByteShiftsList_eq_self_of_clean env h]
  | .repeat x _, h | .index x _, h | .slice x _ _, h | .member x _, h | .project x _, h
  | .store x, h | .load x, h | .hint _ x _, h | .neg x, h => by
    simp [Peephole.lowerByteShifts, lowerByteShifts_eq_self_of_clean env (e := x) h]
  | .binary _ l r, h => by
    simp only [isCleanNoU32, Bool.and_eq_true] at h
    simp [Peephole.lowerByteShifts,
      lowerByteShifts_eq_self_of_clean env h.1, lowerByteShifts_eq_self_of_clean env h.2]
  | .call nm ts xs, h => by
    simp only [isCleanNoU32, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [Peephole.lowerByteShifts, tryLowerByteShift_eq_none_of_clean h.1,
      lowerByteShiftsList_eq_self_of_clean env h.2]
  | .letValue p v b, h => by
    simp only [isCleanNoU32, Bool.and_eq_true] at h
    have hv := lowerByteShifts_eq_self_of_clean env h.1.2
    cases p with
    | bind nm =>
      simp only [Peephole.lowerByteShifts, hv]
      rw [lowerByteShifts_eq_self_of_clean _ h.2]
    | literal _ | wildcard | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      simp only [Peephole.lowerByteShifts, hv]
      rw [lowerByteShifts_eq_self_of_clean _ h.2]
  | .matchValue s arms, h => by
    simp only [isCleanNoU32, Bool.and_eq_true] at h
    simp [Peephole.lowerByteShifts,
      lowerByteShifts_eq_self_of_clean env h.1, lowerByteShiftsArms_eq_self_of_clean env h.2]

theorem lowerByteShiftsList_eq_self_of_clean (env : Peephole.ConstEnv) :
    ∀ {xs : List Lower.Expr},
      isCleanNoU32List xs = true → Peephole.lowerByteShiftsList env xs = xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [isCleanNoU32List, Bool.and_eq_true] at h
    simp [Peephole.lowerByteShiftsList,
      lowerByteShifts_eq_self_of_clean env h.1, lowerByteShiftsList_eq_self_of_clean env h.2]

theorem lowerByteShiftsArms_eq_self_of_clean (env : Peephole.ConstEnv) :
    ∀ {arms : List (Lower.Pat × Lower.Expr)},
      isCleanNoU32Arms arms = true → Peephole.lowerByteShiftsArms env arms = arms
  | [], _ => rfl
  | (p, b) :: rest, h => by
    simp only [isCleanNoU32Arms, Bool.and_eq_true] at h
    simp [Peephole.lowerByteShiftsArms,
      lowerByteShifts_eq_self_of_clean _ h.1.2, lowerByteShiftsArms_eq_self_of_clean env h.2]

end

section EvalPeephole

variable {F : Type} [Field F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
private theorem matchListWith_map {α β : Type}
    (f : β → SourceValue F → Except EvalError (Option (Environment F Nat))) (g : α → β) :
    ∀ (l : List α) (vs : List (SourceValue F)),
      matchListWith f (l.map g) vs = matchListWith (fun a v => f (g a) v) l vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: tl, v :: vt => by
    simp only [List.map_cons, matchListWith, bind, Except.bind]
    cases f (g a) v with
    | error _ => rfl
    | ok o => cases o <;> simp [matchListWith_map]

omit [Field F] [DecidableEq F] in
private theorem matchListWith_attach {α : Type}
    (f : α → SourceValue F → Except EvalError (Option (Environment F Nat))) :
    ∀ (l : List α) (vs : List (SourceValue F)),
      matchListWith (fun p val => f p.val val) l.attach vs = matchListWith f l vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: tl, v :: vt => by
    simp only [List.attach_cons, matchListWith, bind, Except.bind]
    cases f a v with
    | error _ => rfl
    | ok o =>
      cases o with
      | none => rfl
      | some b1 =>
        rw [matchListWith_map]
        rw [matchListWith_attach f tl vt]

mutual

/-- Every simple pattern binds the exact list of variable names reported by `Peephole.patBoundNames`. -/
private theorem matchPattern_names_of_simple {world : World F} {h : Heap F} :
    ∀ {p : Lower.Pat} {v : SourceValue F} {bs : Environment F Nat},
      isSimplePat p = true →
      world.matchPattern [] h (qualifyPatF F p) v = .ok (some bs) →
      bs.map Prod.fst = Peephole.patBoundNames p
  | .literal c, v, bs, _, hm => by
    simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
      matchPatternWith, pure, Except.pure, Except.ok.injEq] at hm
    cases v with
    | field x =>
      by_cases hx : (c : F) = x
      · subst hx
        simp [Aiur.Pattern.bindings] at hm
        subst hm; rfl
      · simp [Aiur.Pattern.bindings, hx] at hm
    | tuple _ | ptr _ _ | construct _ _ _ => simp [Aiur.Pattern.bindings] at hm
  | .wildcard, _, bs, _, hm => by
    simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
      matchPatternWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hm
    subst hm; rfl
  | .bind x, _, bs, _, hm => by
    simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
      matchPatternWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hm
    subst hm; rfl
  | .tuple ps, v, bs, hs, hm => by
    cases v with
    | field _ | ptr _ _ | construct _ _ _ =>
      simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, pure, Except.pure] at hm
    | tuple vals =>
      simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, List.length_map] at hm
      by_cases hlen : (ps.length != vals.length) = true
      · simp [hlen, pure, Except.pure] at hm
      · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hm
        rw [matchListWith_attach, matchListWith_map, matchListWith_map] at hm
        exact matchPatternList_names_of_simple hs hm
  | .array ps, v, bs, hs, hm => by
    cases v with
    | field _ | ptr _ _ | construct _ _ _ =>
      simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, pure, Except.pure] at hm
    | tuple vals =>
      simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, List.length_map] at hm
      by_cases hlen : (ps.length != vals.length) = true
      · simp [hlen, pure, Except.pure] at hm
      · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hm
        rw [matchListWith_attach, matchListWith_map, matchListWith_map] at hm
        exact matchPatternList_names_of_simple hs hm
  | .construct ty ctor ps, v, bs, hs, hm => by
    cases v with
    | field _ | ptr _ _ | tuple _ =>
      simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, pure, Except.pure] at hm
    | construct nm c vals =>
      simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, List.length_map] at hm
      by_cases htest : (nm != constructorName [] (qualifyTy ty) || c != ctor || (ps.length != vals.length)) = true
      · simp [htest, pure, Except.pure] at hm
      · simp only [htest, Bool.false_eq_true, ↓reduceIte] at hm
        rw [matchListWith_attach, matchListWith_map, matchListWith_map] at hm
        exact matchPatternList_names_of_simple hs hm
  | .global .., _, _, hs, _ | .load _, _, _, hs, _ | .orElse .., _, _, hs, _
  | .repeat .., _, _, hs, _ | .record .., _, _, hs, _ | .constructAs .., _, _, hs, _ => by
    simp [isSimplePat] at hs

private theorem matchPatternList_names_of_simple {world : World F} {h : Heap F} :
    ∀ {qs : List Lower.Pat} {vs : List (SourceValue F)} {bs : Environment F Nat},
      isSimplePatList qs = true →
      matchListWith (fun q val => world.matchPattern [] h (qualifyPatF F q) val) qs vs = .ok (some bs) →
      bs.map Prod.fst = Peephole.patBoundNamesList qs
  | [], [], bs, _, hml => by
    simp only [matchListWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hml
    subst hml; rfl
  | [], _ :: _, _, _, hml | _ :: _, [], _, _, hml => by
    simp [matchListWith, pure, Except.pure] at hml
  | q :: qt, v :: vt, bs, hsp, hml => by
    simp only [isSimplePatList, Bool.and_eq_true] at hsp
    simp only [matchListWith, bind, Except.bind] at hml
    cases h1 : world.matchPattern [] h (qualifyPatF F q) v with
    | error _ => simp [h1] at hml
    | ok o1 =>
      cases o1 with
      | none => simp [h1, pure, Except.pure] at hml
      | some b1 =>
        simp only [h1] at hml
        cases h2 : matchListWith (fun q val => world.matchPattern [] h (qualifyPatF F q) val) qt vt with
        | error _ => simp [h2] at hml
        | ok o2 =>
          cases o2 with
          | none => simp [h2, pure, Except.pure] at hml
          | some b2 =>
            simp only [h2, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hml
            subst hml
            simp [Peephole.patBoundNamesList,
              matchPattern_names_of_simple hsp.1 h1,
              matchPatternList_names_of_simple hsp.2 h2]

end

private theorem selectArm_map_inv {world : World F} {h : Heap F} {v : SourceValue F} :
    ∀ {arms : List (Lower.Pat × Lower.Expr)} {bs : Environment F Nat} {bodyF : Aiur.Generic.Expr F},
      SourceSemantics.selectArm world [] h v
        (arms.map fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2)) = .ok (some (bs, bodyF)) →
      ∃ p b, (p, b) ∈ arms ∧ bodyF = qualifyExprF F b ∧
        world.matchPattern [] h (qualifyPatF F p) v = .ok (some bs)
  | [], _, _, hsel => by simp [SourceSemantics.selectArm, pure, Except.pure] at hsel
  | (p, b) :: rest, bs, bodyF, hsel => by
    simp only [List.map_cons, SourceSemantics.selectArm, bind, Except.bind] at hsel
    cases hm : world.matchPattern [] h (qualifyPatF F p) v with
    | error _ => simp [hm] at hsel
    | ok o =>
      cases o with
      | some bs' =>
        simp only [hm, pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hsel
        obtain ⟨rfl, rfl⟩ := hsel
        exact ⟨p, b, List.mem_cons_self, rfl, hm⟩
      | none =>
        simp only [hm] at hsel
        obtain ⟨p', b', hmem, heq, hm'⟩ := selectArm_map_inv hsel
        exact ⟨p', b', List.mem_cons_of_mem _ hmem, heq, hm'⟩

omit [Field F] [DecidableEq F] in
private theorem find?_append_agree {bs loc1 loc2 : Environment F Nat} {x : String}
    (h : x ∉ bs.map Prod.fst → loc1.find? (·.1 == x) = loc2.find? (·.1 == x)) :
    (bs ++ loc1).find? (·.1 == x) = (bs ++ loc2).find? (·.1 == x) := by
  rw [List.find?_append, List.find?_append]
  cases hf : bs.find? (·.1 == x) with
  | some p => rfl
  | none =>
    simp only [Option.none_or]
    apply h
    intro hmem
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
    have hnone := List.find?_eq_none.mp hf p hp
    simp at hnone

omit [DecidableEq F] in
private theorem map_qualifyExprF (xs : List Lower.Expr) :
    List.map (Aiur.Generic.Expr.map (Nat.cast : Nat → F)) (List.map qualifyExpr xs) =
      xs.map (qualifyExprF F) := by
  simp [qualifyExprF, List.map_map, Function.comp_def]

omit [DecidableEq F] in
private theorem map_qualifyArmsF (arms : List (Lower.Pat × Lower.Expr)) :
    List.map (fun arm => (Aiur.Generic.Pattern.map (Nat.cast : Nat → F) arm.1,
        Aiur.Generic.Expr.map (Nat.cast : Nat → F) arm.2))
      (List.map (fun arm => (qualifyPat arm.1, qualifyExpr arm.2)) arms) =
    arms.map fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2) := by
  simp [qualifyPatF, qualifyExprF, List.map_map, Function.comp_def]

mutual

/-- Local-environment congruence for `EvalExprN`: if `loc1` and `loc2` agree on all
free variables of a clean expression `e`, any derivation in `loc1` transfers to `loc2`. -/
theorem evalExprN_localsAgree {world : World F} {d : Nat} :
    ∀ {e : Lower.Expr} {loc1 loc2 : Environment F Nat} {h h' : Heap F} {r : SourceValue F},
      isCleanNoU32 e = true →
      (∀ x, Peephole.occursFree x e = true → loc1.find? (·.1 == x) = loc2.find? (·.1 == x)) →
      EvalExprN world d [] loc1 (qualifyExprF F e) h r h' →
      EvalExprN world d [] loc2 (qualifyExprF F e) h r h'
  | .control .., _, _, _, _, _, hc, _, _ | .global .., _, _, _, _, _, hc, _, _ => by
    simp [isCleanNoU32] at hc
  | .literal _, _, _, _, _, _, _, _, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    obtain ⟨rfl, rfl⟩ := evalExprN_literal_inv ev
    exact .literal
  | .var nm, _, _, _, _, _, _, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    obtain ⟨hl, rfl⟩ := evalExprN_var_inv ev
    exact .var (by rw [← hag nm (by simp [Peephole.occursFree])]; exact hl)
  | .tuple xs, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | tuple items => exact .tuple (evalArgsN_localsAgree hc (fun x hx => hag x hx) items)
  | .array xs, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | array items => exact .array (evalArgsN_localsAgree hc (fun x hx => hag x hx) items)
  | .repeat x n, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | «repeat» item => exact .repeat (evalExprN_localsAgree hc hag item)
  | .index x i, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | index item hp => exact .index (evalExprN_localsAgree hc hag item) hp
  | .slice x s t, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | slice item hs => exact .slice (evalExprN_localsAgree hc hag item) hs
  | .builtin op xs, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | builtin items ha => exact .builtin (evalArgsN_localsAgree hc (fun x hx => hag x hx) items) ha
  | .update ps xs, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | update items ha => exact .update (evalArgsN_localsAgree hc (fun x hx => hag x hx) items) ha
  | .record hd xs, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | record items => exact .record (evalArgsN_localsAgree hc (fun x hx => hag x hx) items)
  | .member x f, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | member item hp => exact .member (evalExprN_localsAgree hc hag item) hp
  | .construct n ts c xs, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | construct items => exact .construct (evalArgsN_localsAgree hc (fun x hx => hag x hx) items)
  | .constructAs ps t c xs, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | constructAs items => exact .constructAs (evalArgsN_localsAgree hc (fun x hx => hag x hx) items)
  | .project x i, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | project item hp => exact .project (evalExprN_localsAgree hc hag item) hp
  | .store x, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | store item => exact .store (evalExprN_localsAgree hc hag item)
  | .load x, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | load item hl => exact .load (evalExprN_localsAgree hc hag item) hl
  | .hint t x ch, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | hint item ht => exact .hint (evalExprN_localsAgree hc hag item) ht
  | .neg x, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | neg item hop => exact .neg (evalExprN_localsAgree hc hag item) hop
  | .binary op l r, _, _, _, _, _, hc, hag, ev => by
    simp only [isCleanNoU32, Bool.and_eq_true] at hc
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | binary el er hop =>
      exact .binary
        (evalExprN_localsAgree hc.1 (fun x hx => hag x (by simp [Peephole.occursFree, hx])) el)
        (evalExprN_localsAgree hc.2 (fun x hx => hag x (by simp [Peephole.occursFree, hx])) er) hop
  | .call nm ts xs, _, _, _, _, _, hc, hag, ev => by
    simp only [isCleanNoU32, Bool.and_eq_true] at hc
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | call hlt items hcal => exact .call hlt (evalArgsN_localsAgree hc.2 (fun x hx => hag x hx) items) hcal
  | .letValue p v b, _, _, _, _, _, hc, hag, ev => by
    simp only [isCleanNoU32, Bool.and_eq_true] at hc
    obtain ⟨⟨hp, hv⟩, hb⟩ := hc
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | letValue evV hm evB =>
      have hnames := matchPattern_names_of_simple hp hm
      refine .letValue
        (evalExprN_localsAgree hv (fun x hx => hag x (by simp [Peephole.occursFree, hx])) evV) hm ?_
      apply evalExprN_localsAgree hb _ evB
      intro x hx
      apply find?_append_agree
      intro hnotmem
      rw [hnames] at hnotmem
      exact hag x (by simp [Peephole.occursFree, hnotmem, hx])
  | .matchValue s arms, _, _, _, _, _, hc, hag, ev => by
    simp only [isCleanNoU32, Bool.and_eq_true] at hc
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | matchValue evS hsel evB =>
      have hsel' := hsel
      rw [map_qualifyArmsF] at hsel'
      obtain ⟨p, b, hmem, rfl, hm⟩ := selectArm_map_inv hsel'
      have hpa := (isCleanNoU32Arms_iff.mp hc.2) (p, b) hmem
      have hnames := matchPattern_names_of_simple hpa.1 hm
      refine .matchValue
        (evalExprN_localsAgree hc.1 (fun x hx => hag x (by simp [Peephole.occursFree, hx])) evS)
        hsel ?_
      apply evalExprN_localsAgree hpa.2 _ evB
      intro x hx
      apply find?_append_agree
      intro hnotmem
      rw [hnames] at hnotmem
      have hmemArm : Peephole.occursFreeArms x arms = true := by
        clear evS hsel hsel' evB hm hnames hc hag
        induction arms with
        | nil => cases hmem
        | cons hd tl ih =>
          rcases List.mem_cons.mp hmem with rfl | htl
          · simp [Peephole.occursFreeArms, hnotmem, hx]
          · simp [Peephole.occursFreeArms, ih htl]
      exact hag x (by simp [Peephole.occursFree, hmemArm])
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem hmem; simp only [Prod.mk.sizeOf_spec] at this; omega)

theorem evalArgsN_localsAgree {world : World F} {d : Nat} :
    ∀ {xs : List Lower.Expr} {loc1 loc2 : Environment F Nat} {h h' : Heap F} {ws : List (SourceValue F)},
      isCleanNoU32List xs = true →
      (∀ x, Peephole.occursFreeList x xs = true → loc1.find? (·.1 == x) = loc2.find? (·.1 == x)) →
      EvalArgsN world d [] loc1 (xs.map (qualifyExprF F)) h ws h' →
      EvalArgsN world d [] loc2 (xs.map (qualifyExprF F)) h ws h'
  | [], _, _, _, _, _, _, _, ev => by cases ev; exact .nil
  | a :: tl, _, _, _, _, _, hc, hag, ev => by
    simp only [isCleanNoU32List, Bool.and_eq_true] at hc
    cases ev with
    | cons hd rest =>
      exact .cons
        (evalExprN_localsAgree hc.1 (fun x hx => hag x (by simp [Peephole.occursFreeList, hx])) hd)
        (evalArgsN_localsAgree hc.2 (fun x hx => hag x (by simp [Peephole.occursFreeList, hx])) rest)
termination_by xs => sizeOf xs

end

/-- Every variable tracked in `Peephole.ConstEnv` is bound in `locals`. -/
def PeepEnvBound (env : Peephole.ConstEnv) (locals : Environment F Nat) : Prop :=
  ∀ nm k, env.lookup nm = some k → ∃ v, locals.find? (·.1 == nm) = some (nm, v)

private theorem lookup_envRemove {names : List String} {env : Peephole.ConstEnv} {nm : String} {k : Nat}
    (h : (Peephole.envRemove names env).lookup nm = some k) :
    nm ∉ names ∧ env.lookup nm = some k := by
  induction env with
  | nil => simp [Peephole.envRemove] at h
  | cons p tl ih =>
    rcases p with ⟨a, va⟩
    simp only [Peephole.envRemove, List.filter_cons] at h
    by_cases ha : names.contains a = true
    · simp only [ha, Bool.not_true] at h
      obtain ⟨hnm, htl⟩ := ih h
      have hne : nm ≠ a := fun heq => hnm (heq ▸ List.contains_iff_mem.mp ha)
      exact ⟨hnm, by simp [List.lookup, beq_false_of_ne hne, htl]⟩
    · have haf : names.contains a = false := Bool.eq_false_iff.mpr ha
      simp only [haf, Bool.not_false, ite_true, List.lookup] at h
      by_cases heq : nm = a
      · subst heq
        simp only [beq_self_eq_true, Option.some.injEq] at h
        subst h
        exact ⟨fun hm => ha (List.contains_iff_mem.mpr hm), by simp [List.lookup]⟩
      · simp only [beq_false_of_ne heq] at h
        obtain ⟨hnm, htl⟩ := ih h
        exact ⟨hnm, by simp [List.lookup, beq_false_of_ne heq, htl]⟩

omit [Field F] [DecidableEq F] in
private theorem peepEnvBound_append_remove {env : Peephole.ConstEnv} {bs locals : Environment F Nat}
    {names : List String} (hb : PeepEnvBound env locals) (hnames : bs.map Prod.fst = names) :
    PeepEnvBound (Peephole.envRemove names env) (bs ++ locals) := by
  intro nm k hlook
  obtain ⟨hni, hlook'⟩ := lookup_envRemove hlook
  obtain ⟨v, hv⟩ := hb nm k hlook'
  refine ⟨v, ?_⟩
  rw [List.find?_append]
  have hnone : bs.find? (·.1 == nm) = none := by
    rw [List.find?_eq_none]
    intro p hp
    simp only [beq_iff_eq]
    intro heq
    exact hni (hnames ▸ List.mem_map.mpr ⟨p, hp, heq⟩)
  rw [hnone]; exact hv

mutual

/-- Backward simulation of `Peephole.fuseExpr` on clean non-`UInt32` expressions:
any `EvalExprN` derivation of `fuseExpr env e` lifts to an `EvalExprN` derivation of `e`
at the exact same call depth `d` and final heap `h'`. -/
theorem evalExprN_of_fuseExpr_clean {world : World F} {d : Nat} :
    ∀ {env : Peephole.ConstEnv} {e : Lower.Expr} {locals : Environment F Nat}
      {h h' : Heap F} {r : SourceValue F},
      isCleanNoU32 e = true →
      PeepEnvBound env locals →
      EvalExprN world d [] locals (qualifyExprF F (Peephole.fuseExpr env e)) h r h' →
      EvalExprN world d [] locals (qualifyExprF F e) h r h'
  | _, .control .., _, _, _, _, hc, _, _ | _, .global .., _, _, _, _, hc, _, _ => by
    simp [isCleanNoU32] at hc
  | _, .literal _, _, _, _, _, _, _, ev => ev
  | _, .var _, _, _, _, _, _, _, ev => ev
  | _, .tuple xs, _, _, _, _, hc, hb, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | tuple items => exact .tuple (evalArgsN_of_fuseList_clean hc hb items)
  | _, .array xs, _, _, _, _, hc, hb, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | array items => exact .array (evalArgsN_of_fuseList_clean hc hb items)
  | _, .repeat x n, _, _, _, _, hc, hb, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | «repeat» item => exact .repeat (evalExprN_of_fuseExpr_clean hc hb item)
  | _, .index x i, _, _, _, _, hc, hb, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | index item hp => exact .index (evalExprN_of_fuseExpr_clean hc hb item) hp
  | _, .slice x s t, _, _, _, _, hc, hb, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | slice item hs => exact .slice (evalExprN_of_fuseExpr_clean hc hb item) hs
  | _, .builtin op xs, _, _, _, _, hc, hb, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | builtin items ha => exact .builtin (evalArgsN_of_fuseList_clean hc hb items) ha
  | _, .update ps xs, _, _, _, _, hc, hb, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | update items ha => exact .update (evalArgsN_of_fuseList_clean hc hb items) ha
  | _, .record hd xs, _, _, _, _, hc, hb, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | record items => exact .record (evalArgsN_of_fuseList_clean hc hb items)
  | _, .member x f, _, _, _, _, hc, hb, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | member item hp => exact .member (evalExprN_of_fuseExpr_clean hc hb item) hp
  | _, .construct n ts c xs, _, _, _, _, hc, hb, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | construct items => exact .construct (evalArgsN_of_fuseList_clean hc hb items)
  | _, .constructAs ps t c xs, _, _, _, _, hc, hb, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | constructAs items => exact .constructAs (evalArgsN_of_fuseList_clean hc hb items)
  | _, .project x i, _, _, _, _, hc, hb, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | project item hp => exact .project (evalExprN_of_fuseExpr_clean hc hb item) hp
  | _, .store x, _, _, _, _, hc, hb, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | store item => exact .store (evalExprN_of_fuseExpr_clean hc hb item)
  | _, .load x, _, _, _, _, hc, hb, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | load item hl => exact .load (evalExprN_of_fuseExpr_clean hc hb item) hl
  | _, .hint t x ch, _, _, _, _, hc, hb, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | hint item ht => exact .hint (evalExprN_of_fuseExpr_clean hc hb item) ht
  | _, .neg x, _, _, _, _, hc, hb, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | neg item hop => exact .neg (evalExprN_of_fuseExpr_clean hc hb item) hop
  | _, .binary op l r, _, _, _, _, hc, hb, ev => by
    simp only [isCleanNoU32, Bool.and_eq_true] at hc
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | binary el er hop =>
      exact .binary (evalExprN_of_fuseExpr_clean hc.1 hb el)
        (evalExprN_of_fuseExpr_clean hc.2 hb er) hop
  | _, .call nm ts xs, _, _, _, _, hc, hb, ev => by
    simp only [isCleanNoU32, Bool.and_eq_true, Bool.not_eq_true'] at hc
    simp only [Peephole.fuseExpr, tryFuseCall_eq_none_of_clean hc.1, Option.getD_none,
      qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | call hlt items hcal => exact .call hlt (evalArgsN_of_fuseList_clean hc.2 hb items) hcal
  | env, .letValue p v b, locals, h, h', r, hc, hb, ev => by
    simp only [isCleanNoU32, Bool.and_eq_true] at hc
    obtain ⟨⟨hp, hv⟩, hcb⟩ := hc
    have hv' : isCleanNoU32 (Peephole.fuseExpr env v) = true := isCleanNoU32_fuseExpr env hv
    cases p with
    | bind nm =>
      simp only [Peephole.fuseExpr] at ev
      rw [tryFuseLet_of_clean hv'] at ev
      unfold Peephole.tryDropDeadConst at ev
      cases hce : Peephole.extractU32Const? env (Peephole.fuseExpr env v) with
      | none =>
        simp only [hce, Option.getD_none, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
          qualifyPat, Aiur.Generic.Pattern.map] at ev ⊢
        obtain ⟨w1, hm, evV, evB⟩ := evalExprN_let_bind_inv ev
        have hbEnv' : PeepEnvBound (Peephole.envRemove [nm] env) ((nm, w1) :: locals) :=
          peepEnvBound_append_remove (bs := [(nm, w1)]) hb rfl
        exact .letValue (bindings := [(nm, w1)]) (evalExprN_of_fuseExpr_clean hv hb evV)
          (by simp [World.matchPattern, matchPatternWith])
          (evalExprN_of_fuseExpr_clean hcb hbEnv' evB)
      | some k0 =>
        have hcb' : isCleanNoU32 (Peephole.fuseExpr ((nm, k0) :: Peephole.envRemove [nm] env) b) = true :=
          isCleanNoU32_fuseExpr _ hcb
        have hbEnv' : ∀ w1, PeepEnvBound ((nm, k0) :: Peephole.envRemove [nm] env) ((nm, w1) :: locals) := by
          intro w1 y ky hly
          by_cases hyn : y = nm
          · subst hyn; exact ⟨w1, by simp⟩
          · simp only [List.lookup, beq_false_of_ne hyn] at hly
            exact peepEnvBound_append_remove (bs := [(nm, w1)]) hb rfl y ky hly
        simp only [hce] at ev
        by_cases hfree : Peephole.occursFree nm (Peephole.fuseExpr ((nm, k0) :: Peephole.envRemove [nm] env) b) = false
        · simp only [hfree, Bool.not_false, ↓reduceIte, Option.getD_some] at ev
          have hvPure : ∃ w1, EvalExprN world d [] locals (qualifyExprF F (Peephole.fuseExpr env v)) h w1 h := by
            rcases extractU32Const?_of_clean hv' hce with ⟨c, hveq⟩ | ⟨y, hveq, hly⟩
            · rw [hveq]; exact ⟨.field (c : F), by simp [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]; exact .literal⟩
            · obtain ⟨vy, hvy⟩ := hb y k0 hly
              rw [hveq]; exact ⟨vy, by simp [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]; exact .var hvy⟩
          obtain ⟨w1, evV'⟩ := hvPure
          have evV : EvalExprN world d [] locals (qualifyExprF F v) h w1 h :=
            evalExprN_of_fuseExpr_clean hv hb evV'
          have evB' : EvalExprN world d [] ((nm, w1) :: locals)
              (qualifyExprF F (Peephole.fuseExpr ((nm, k0) :: Peephole.envRemove [nm] env) b)) h r h' := by
            apply evalExprN_localsAgree hcb' _ ev
            intro x hx
            have hne : nm ≠ x := fun heq => by subst heq; rw [hx] at hfree; cases hfree
            simp [beq_false_of_ne hne]
          have evB : EvalExprN world d [] ((nm, w1) :: locals) (qualifyExprF F b) h r h' :=
            evalExprN_of_fuseExpr_clean hcb (hbEnv' w1) evB'
          simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
            qualifyPat, Aiur.Generic.Pattern.map]
          exact .letValue (bindings := [(nm, w1)]) evV
            (by simp [World.matchPattern, matchPatternWith]) evB
        · have hft : Peephole.occursFree nm (Peephole.fuseExpr ((nm, k0) :: Peephole.envRemove [nm] env) b) = true :=
            Bool.eq_true_of_not_eq_false hfree
          simp only [hft, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
            qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, qualifyPat, Aiur.Generic.Pattern.map] at ev ⊢
          obtain ⟨w1, hm, evV, evB⟩ := evalExprN_let_bind_inv ev
          exact .letValue (bindings := [(nm, w1)]) (evalExprN_of_fuseExpr_clean hv hb evV)
            (by simp [World.matchPattern, matchPatternWith])
            (evalExprN_of_fuseExpr_clean hcb (hbEnv' w1) evB)
    | literal _ | wildcard | tuple _ | array _ | construct _ _ _ =>
      simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
      cases ev with
      | letValue evV hm evB =>
        have hnames := matchPattern_names_of_simple hp hm
        exact .letValue (evalExprN_of_fuseExpr_clean hv hb evV) hm
          (evalExprN_of_fuseExpr_clean hcb (peepEnvBound_append_remove hb hnames) evB)
    | global _ _ | load _ | orElse _ _ _ | «repeat» _ _ | record _ _ | constructAs _ _ _ _ =>
      simp [isSimplePat] at hp
  | env, .matchValue s arms, locals, h, h', r, hc, hb, ev => by
    simp only [isCleanNoU32, Bool.and_eq_true] at hc
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | matchValue evS hsel evB =>
      have evS' := evalExprN_of_fuseExpr_clean hc.1 hb evS
      have hselMap :
          ∀ (as : List (Lower.Pat × Lower.Expr)) (v : SourceValue F) (hm : Heap F)
            (bs : Environment F Nat) (bodyF : Aiur.Generic.Expr F),
            isCleanNoU32Arms as = true →
            SourceSemantics.selectArm world [] hm v
              ((Peephole.fuseArms env as).map fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2)) =
              .ok (some (bs, bodyF)) →
            ∃ p b, (p, b) ∈ as ∧
              bodyF = qualifyExprF F (Peephole.fuseExpr (Peephole.envRemove (Peephole.patBoundNames p) env) b) ∧
              world.matchPattern [] hm (qualifyPatF F p) v = .ok (some bs) ∧
              SourceSemantics.selectArm world [] hm v
                (as.map fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2)) =
                .ok (some (bs, qualifyExprF F b)) := by
        intro as v hm bs bodyF hca hsel0
        induction as with
        | nil => simp [Peephole.fuseArms, SourceSemantics.selectArm, pure, Except.pure] at hsel0
        | cons hd tl ih =>
          rcases hd with ⟨p, b⟩
          simp only [isCleanNoU32Arms, Bool.and_eq_true] at hca
          simp only [Peephole.fuseArms, List.map_cons, SourceSemantics.selectArm, bind, Except.bind] at hsel0 ⊢
          cases hmp : world.matchPattern [] hm (qualifyPatF F p) v with
          | error _ => simp [hmp] at hsel0
          | ok o =>
            cases o with
            | some bs' =>
              simp only [hmp, pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hsel0 ⊢
              obtain ⟨rfl, rfl⟩ := hsel0
              exact ⟨p, b, List.mem_cons_self, rfl, hmp, rfl, rfl⟩
            | none =>
              simp only [hmp] at hsel0 ⊢
              obtain ⟨p', b', hm', hbf, hmp', hs'⟩ := ih hca.2 hsel0
              exact ⟨p', b', List.mem_cons_of_mem _ hm', hbf, hmp', hs'⟩
      have hsel0 := hsel
      rw [map_qualifyArmsF] at hsel0
      obtain ⟨p, b, hmem, rfl, hmp, hselOrig⟩ := hselMap arms _ _ _ _ hc.2 hsel0
      have hpa := (isCleanNoU32Arms_iff.mp hc.2) (p, b) hmem
      have hnames := matchPattern_names_of_simple hpa.1 hmp
      have evB' := evalExprN_of_fuseExpr_clean hpa.2 (peepEnvBound_append_remove hb hnames) evB
      refine .matchValue evS' ?_ evB'
      rw [map_qualifyArmsF]
      exact hselOrig
termination_by _ e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem hmem; simp only [Prod.mk.sizeOf_spec] at this; omega)

theorem evalArgsN_of_fuseList_clean {world : World F} {d : Nat} :
    ∀ {env : Peephole.ConstEnv} {xs : List Lower.Expr} {locals : Environment F Nat}
      {h h' : Heap F} {ws : List (SourceValue F)},
      isCleanNoU32List xs = true →
      PeepEnvBound env locals →
      EvalArgsN world d [] locals ((Peephole.fuseList env xs).map (qualifyExprF F)) h ws h' →
      EvalArgsN world d [] locals (xs.map (qualifyExprF F)) h ws h'
  | _, [], _, _, _, _, _, _, ev => by cases ev; exact .nil
  | env, a :: tl, _, _, _, _, hc, hb, ev => by
    simp only [isCleanNoU32List, Bool.and_eq_true] at hc
    simp only [Peephole.fuseList, List.map_cons] at ev
    cases ev with
    | cons hd rest =>
      exact .cons (evalExprN_of_fuseExpr_clean hc.1 hb hd)
        (evalArgsN_of_fuseList_clean hc.2 hb rest)
termination_by _ xs => sizeOf xs

end

/-- **Main Peephole Backward Simulation Theorem (`noU32Calls`)**:
for any clean non-`UInt32` expression `e`, an `EvalExprN` derivation of
`Peephole.rewriteExpr e` lifts to `EvalExprN` of `e` at identical depth `d` and heap `h'`. -/
theorem evalExprN_of_rewriteExpr_clean {world : World F} {d : Nat} {e : Lower.Expr}
    {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F}
    (hc : isCleanNoU32 e = true)
    (ev : EvalExprN world d [] locals (qualifyExprF F (Peephole.rewriteExpr e)) h r h') :
    EvalExprN world d [] locals (qualifyExprF F e) h r h' := by
  unfold Peephole.rewriteExpr at ev
  rw [lowerByteShifts_eq_self_of_clean [] (isCleanNoU32_fuseExpr [] hc)] at ev
  exact evalExprN_of_fuseExpr_clean hc (fun _ _ hl => by cases hl) ev

end EvalPeephole

end PeepholeSim

/-! ## Section 5: Certified `Nat`-Core Fragment, `ValOk`↔`Rep`, `TLowerM` Inversions & Cleanliness -/

section NatCoreAndInversions

/-- Empty array reader used when invoking `Fir.Proof.Shape` soundness on the
array-free core fragment. -/
def dummyEnc : Fir.Shape.ArrEnc := ⟨fun _ => none⟩

/-- Representations belonging to the certified `Nat`/enum/data/obj core fragment
(everything except multi-limb `.w32` and `.w64` words). -/
def isNatCoreRep : Rep → Bool
  | .irr | .nat _ | .w8 | .w16 | .enum _ | .data _ | .obj => true
  | .w32 | .w64 => false

/-- Every exported function's parameters accept arbitrary `< 2^56` naturals under `cert`. -/
def exportParamsOk (P : Program) (cert : ShapeCert) : Bool :=
  P.exports.all fun f =>
    match P.fun? f with
    | some fd => (fd.params.map Prod.fst).all fun p =>
        (Shape.natLt natLimit).le ((cert.fn f).var p)
    | none => true

mutual

def codeParamsNodup : Code → Bool
  | .bind _ _ k => codeParamsNodup k
  | .jp _ ps _ b k => allDistinct ps && codeParamsNodup b && codeParamsNodup k
  | .jmp _ _ | .ret _ | .tcall _ _ | .trap => true
  | .case _ alts d => altsParamsNodup alts && optParamsNodup d

def altsParamsNodup : List Alt → Bool
  | [] => true
  | .mk _ b :: rest => codeParamsNodup b && altsParamsNodup rest

def optParamsNodup : Option Code → Bool
  | none => true
  | some c => codeParamsNodup c

end

/-- Every function and join point in `P` has pairwise-distinct parameter names. -/
def paramsNodup (P : Program) : Bool :=
  P.funList.all fun (_, fd) =>
    allDistinct (fd.params.map Prod.fst) && codeParamsNodup fd.body

/-- If both `Nat.zero` and `Nat.succ` are pinned in `P`, they have distinct keys. -/
def natPinsDistinct (P : Program) : Bool :=
  match P.known.natZero, P.known.natSucc with
  | some kz, some ks => kz != ks
  | _, _ => true

mutual

def codeNoWordPrims : Code → Bool
  | .bind _ r k =>
    (match r with | .prim op _ => !op.isWord | _ => true) && codeNoWordPrims k
  | .jp _ _ _ b k => codeNoWordPrims b && codeNoWordPrims k
  | .jmp _ _ | .ret _ | .tcall _ _ | .trap => true
  | .case _ alts d => altsNoWordPrims alts && optNoWordPrims d

def altsNoWordPrims : List Alt → Bool
  | [] => true
  | .mk _ b :: rest => codeNoWordPrims b && altsNoWordPrims rest

def optNoWordPrims : Option Code → Bool
  | none => true
  | some c => codeNoWordPrims c

end

/-- No function in `P` invokes a fixed-width word primitive (`UInt8/16/32/64`). -/
def noWordPrims (P : Program) : Bool :=
  P.funList.all fun (_, fd) => codeNoWordPrims fd.body

mutual

def codeNatCoreReps (P : Program) (cert : ShapeCert) (feat : Features) (fsh : FunShapes) :
    Code → Bool
  | .bind x _ k =>
    isNatCoreRep (repOf P cert feat (fsh.var x)) && codeNatCoreReps P cert feat fsh k
  | .jp _ ps _ b k =>
    ps.all (fun p => isNatCoreRep (repOf P cert feat (fsh.var p))) &&
    codeNatCoreReps P cert feat fsh b &&
    codeNatCoreReps P cert feat fsh k
  | .jmp _ _ | .ret _ | .tcall _ _ | .trap => true
  | .case _ alts d =>
    altsNatCoreReps P cert feat fsh alts && optNatCoreReps P cert feat fsh d

def altsNatCoreReps (P : Program) (cert : ShapeCert) (feat : Features) (fsh : FunShapes) :
    List Alt → Bool
  | [] => true
  | .mk _ b :: rest =>
    codeNatCoreReps P cert feat fsh b && altsNatCoreReps P cert feat fsh rest

def optNatCoreReps (P : Program) (cert : ShapeCert) (feat : Features) (fsh : FunShapes) :
    Option Code → Bool
  | none => true
  | some c => codeNatCoreReps P cert feat fsh c

end

/-- Every constructor field in `cert.datas` lowers to a core representation. -/
def datasNatCoreReps (P : Program) (cert : ShapeCert) (feat : Features) : Bool :=
  cert.datas.all fun D =>
    D.ctors.all fun (_, fl) =>
      fl.all fun sh => isNatCoreRep (repOf P cert feat sh)

/-- Every function signature, binding, join parameter, and data field uses a core rep. -/
def natCoreRepsOk (P : Program) (cert : ShapeCert) : Bool :=
  let feat := scanFeatures P
  datasNatCoreReps P cert feat &&
  P.funList.all fun (f, fd) =>
    let fsh := cert.fn f
    isNatCoreRep (repOf P cert feat fsh.ret) &&
    (fd.params.map Prod.fst).all (fun p => isNatCoreRep (repOf P cert feat (fsh.var p))) &&
    codeNatCoreReps P cert feat fsh fd.body

/-- **Checkable predicate for the certified typed `Nat`/enum/data/obj core fragment.**
Satisfied by every K1 benchmark (`fib`, `sum-loop`, `ackermann`, `tak`, `gcd`,
`collatz`, `prime-count`, `even-odd`, `sfib`) and `P2Test.entry` under
`TypedRep.inferCheckedShapes`. -/
def natCoreProgram (P : Program) (cert : ShapeCert) : Bool :=
  Fir.Shape.check P cert &&
  exportParamsOk P cert &&
  paramsNodup P &&
  natPinsDistinct P &&
  noWordPrims P &&
  !(scanFeatures P).usesW32 &&
  natCoreRepsOk P cert

/-! ### Projections from `natCoreProgram` -/

theorem natCoreProgram_checked {P : Program} {cert : ShapeCert}
    (h : natCoreProgram P cert = true) : Checked P cert := by
  simp only [natCoreProgram, Bool.and_eq_true] at h
  exact Fir.Proof.Shape.check_checked h.1.1.1.1.1.1

theorem natCoreProgram_exportParamsOk {P : Program} {cert : ShapeCert}
    (h : natCoreProgram P cert = true) : exportParamsOk P cert = true := by
  simp only [natCoreProgram, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

theorem natCoreProgram_paramsNodup {P : Program} {cert : ShapeCert}
    (h : natCoreProgram P cert = true) : paramsNodup P = true := by
  simp only [natCoreProgram, Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem natCoreProgram_natPinsDistinct {P : Program} {cert : ShapeCert}
    (h : natCoreProgram P cert = true) : natPinsDistinct P = true := by
  simp only [natCoreProgram, Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem natCoreProgram_noWordPrims {P : Program} {cert : ShapeCert}
    (h : natCoreProgram P cert = true) : noWordPrims P = true := by
  simp only [natCoreProgram, Bool.and_eq_true] at h
  exact h.1.1.2

theorem natCoreProgram_not_usesW32 {P : Program} {cert : ShapeCert}
    (h : natCoreProgram P cert = true) : (scanFeatures P).usesW32 = false := by
  simp only [natCoreProgram, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1.2

theorem natCoreProgram_natCoreRepsOk {P : Program} {cert : ShapeCert}
    (h : natCoreProgram P cert = true) : natCoreRepsOk P cert = true := by
  simp only [natCoreProgram, Bool.and_eq_true] at h
  exact h.2

theorem natCoreProgram_datasNatCoreReps {P : Program} {cert : ShapeCert}
    (h : natCoreProgram P cert = true) :
    datasNatCoreReps P cert (scanFeatures P) = true := by
  have hr := natCoreProgram_natCoreRepsOk h
  simp only [natCoreRepsOk, Bool.and_eq_true] at hr
  exact hr.1

theorem datasNatCoreReps_field {P : Program} {cert : ShapeCert} {feat : Features}
    (h : datasNatCoreReps P cert feat = true) {d : Nat} {D : DataDecl CtorKey}
    (hD : cert.data? d = some D) {c : CtorKey} {fl : List Shape}
    (hc : (c, fl) ∈ D.ctors) {sh : Shape} (hsh : sh ∈ fl) :
    isNatCoreRep (repOf P cert feat sh) = true := by
  have hmemD : D ∈ cert.datas := List.mem_of_getElem? hD
  have h1 := List.all_eq_true.mp h D hmemD
  have h2 := List.all_eq_true.mp h1 (c, fl) hc
  exact List.all_eq_true.mp h2 sh hsh

theorem funList_mem_of_fun? {P : Program} {f : FunId} {fd : Fun}
    (hfun : P.fun? f = some fd) (hsz : f < P.size) : (f, fd) ∈ P.funList := by
  simp only [Fir.Program.funList, List.mem_filterMap, List.mem_range]
  exact ⟨f, hsz, by simp [hfun]⟩

theorem natCoreProgram_funInfo {P : Program} {cert : ShapeCert}
    (h : natCoreProgram P cert = true) {f : FunId} {fd : Fun}
    (hfun : P.fun? f = some fd) (hsz : f < P.size) :
    (fd.params.map Prod.fst).Nodup ∧
    codeParamsNodup fd.body = true ∧
    codeNoWordPrims fd.body = true ∧
    isNatCoreRep (repOf P cert (scanFeatures P) (cert.fn f).ret) = true ∧
    (∀ p ∈ fd.params.map Prod.fst,
      isNatCoreRep (repOf P cert (scanFeatures P) ((cert.fn f).var p)) = true) ∧
    codeNatCoreReps P cert (scanFeatures P) (cert.fn f) fd.body = true := by
  have hmem := funList_mem_of_fun? hfun hsz
  have hpn := List.all_eq_true.mp (natCoreProgram_paramsNodup h) (f, fd) hmem
  simp only [Bool.and_eq_true] at hpn
  have hnw := List.all_eq_true.mp (natCoreProgram_noWordPrims h) (f, fd) hmem
  have hr := natCoreProgram_natCoreRepsOk h
  simp only [natCoreRepsOk, Bool.and_eq_true] at hr
  have hfr := List.all_eq_true.mp hr.2 (f, fd) hmem
  simp only [Bool.and_eq_true] at hfr
  exact ⟨(Lower.allDistinct_iff_nodup _).mp hpn.1, hpn.2, hnw,
    hfr.1.1, fun p hp => List.all_eq_true.mp hfr.1.2 p hp, hfr.2⟩

theorem natCoreProgram_exportParam_le {P : Program} {cert : ShapeCert}
    (h : natCoreProgram P cert = true) {i : Nat} {f : FunId} {fd : Fun}
    (hexp : P.exports[i]? = some f) (hfun : P.fun? f = some fd) :
    ∀ p ∈ fd.params.map Prod.fst, (Shape.natLt natLimit).le ((cert.fn f).var p) = true := by
  have hmem : f ∈ P.exports := List.mem_of_getElem? hexp
  have hall := List.all_eq_true.mp (natCoreProgram_exportParamsOk h) f hmem
  simp only [hfun] at hall
  intro p hp
  exact List.all_eq_true.mp hall p hp

/-! ### `ValOk` ↔ `repOf` Bridge Lemmas -/

theorem valOk_nat_bound {P : Program} {cert : ShapeCert} {feat : Features}
    {s : Shape} {b n : Nat}
    (hrep : repOf P cert feat s = .nat b)
    (hok : ValOk cert dummyEnc s (.lit (.nat n)))
    (hlt : n < natLimit) :
    n < min b natLimit := by
  cases s with
  | nat =>
    simp only [repOf, Rep.nat.injEq] at hrep
    subst hrep; omega
  | natLt a =>
    simp only [repOf] at hrep
    split at hrep
    · cases hrep
    · split at hrep
      · cases hrep
      · split at hrep
        · cases hrep
          obtain ⟨m, heq, hm⟩ := Fir.Proof.Shape.valOk_natLt_inv hok
          cases heq; omega
        · cases hrep; omega
  | «enum» ind => simp only [repOf] at hrep; split at hrep <;> cases hrep
  | data d => simp only [repOf] at hrep; split at hrep <;> cases hrep
  | word w => cases w <;> simp [repOf] at hrep
  | irr | any | «fn» _ _ | inter _ _ | arr _ _ => simp [repOf] at hrep

theorem valOk_w8_bound {P : Program} {cert : ShapeCert} {feat : Features}
    {s : Shape} {v : Fir.Val}
    (hrep : repOf P cert feat s = .w8)
    (hok : ValOk cert dummyEnc s v) :
    ∃ n < 256, v = .lit (.nat n) := by
  cases s with
  | word w =>
    cases w <;> simp [repOf] at hrep
    obtain ⟨n, rfl, hn⟩ := Fir.Proof.Shape.valOk_word_inv hok
    exact ⟨n, hn, rfl⟩
  | natLt a =>
    simp only [repOf] at hrep
    split at hrep
    · cases hrep
    · split at hrep
      · cases hrep
      · split at hrep <;> cases hrep
  | «enum» ind => simp only [repOf] at hrep; split at hrep <;> cases hrep
  | data d => simp only [repOf] at hrep; split at hrep <;> cases hrep
  | irr | nat | any | «fn» _ _ | inter _ _ | arr _ _ => simp [repOf] at hrep

theorem valOk_w16_bound {P : Program} {cert : ShapeCert} {feat : Features}
    {s : Shape} {v : Fir.Val}
    (hrep : repOf P cert feat s = .w16)
    (hok : ValOk cert dummyEnc s v) :
    ∃ n < 65536, v = .lit (.nat n) := by
  cases s with
  | word w =>
    cases w <;> simp [repOf] at hrep
    obtain ⟨n, rfl, hn⟩ := Fir.Proof.Shape.valOk_word_inv hok
    exact ⟨n, hn, rfl⟩
  | natLt a =>
    simp only [repOf] at hrep
    split at hrep
    · cases hrep
    · split at hrep
      · cases hrep
      · split at hrep <;> cases hrep
  | «enum» ind => simp only [repOf] at hrep; split at hrep <;> cases hrep
  | data d => simp only [repOf] at hrep; split at hrep <;> cases hrep
  | irr | nat | any | «fn» _ _ | inter _ _ | arr _ _ => simp [repOf] at hrep

theorem valOk_irr_inv {P : Program} {cert : ShapeCert} {feat : Features}
    {s : Shape} {v : Fir.Val}
    (hrep : repOf P cert feat s = .irr)
    (hok : ValOk cert dummyEnc s v) :
    v = .erased := by
  cases s with
  | irr => cases hok; rfl
  | natLt a =>
    simp only [repOf] at hrep
    split at hrep
    · cases hrep
    · split at hrep
      · cases hrep
      · split at hrep <;> cases hrep
  | «enum» ind => simp only [repOf] at hrep; split at hrep <;> cases hrep
  | data d => simp only [repOf] at hrep; split at hrep <;> cases hrep
  | word w => cases w <;> simp [repOf] at hrep
  | nat | any | «fn» _ _ | inter _ _ | arr _ _ => simp [repOf] at hrep

theorem valOk_enum_inv {P : Program} {cert : ShapeCert} {feat : Features}
    {s : Shape} {ind : Src.CId} {v : Fir.Val}
    (hrep : repOf P cert feat s = .enum ind)
    (hok : ValOk cert dummyEnc s v) :
    validEnum P cert ind = true ∧
    ∃ ks c, cert.enum? ind = some ks ∧ c.key ∈ ks ∧ v = .ctor c [] := by
  cases s with
  | «enum» ind' =>
    simp only [repOf] at hrep
    split at hrep
    · rename_i hval
      cases hrep
      cases hok with
      | «enum» he hmem => exact ⟨hval, _, _, he, hmem, rfl⟩
    · cases hrep
  | natLt a =>
    simp only [repOf] at hrep
    split at hrep
    · cases hrep
    · split at hrep
      · cases hrep
      · split at hrep <;> cases hrep
  | data d => simp only [repOf] at hrep; split at hrep <;> cases hrep
  | word w => cases w <;> simp [repOf] at hrep
  | irr | nat | any | «fn» _ _ | inter _ _ | arr _ _ => simp [repOf] at hrep

theorem valOk_data_inv {P : Program} {cert : ShapeCert} {feat : Features}
    {s : Shape} {d : Nat} {v : Fir.Val}
    (hrep : repOf P cert feat s = .data d)
    (hok : ValOk cert dummyEnc s v) :
    validData P cert d = true ∧
    ∃ D c fl fs, cert.data? d = some D ∧ (c.key, fl) ∈ D.ctors ∧
      ValsOk cert dummyEnc fl fs ∧ v = .ctor c fs := by
  cases s with
  | data d' =>
    simp only [repOf] at hrep
    split at hrep
    · rename_i hval
      cases hrep
      cases hok with
      | data hD hmem hfs => exact ⟨hval, _, _, _, _, hD, hmem, hfs, rfl⟩
    · cases hrep
  | natLt a =>
    simp only [repOf] at hrep
    split at hrep
    · cases hrep
    · split at hrep
      · cases hrep
      · split at hrep <;> cases hrep
  | «enum» ind => simp only [repOf] at hrep; split at hrep <;> cases hrep
  | word w => cases w <;> simp [repOf] at hrep
  | irr | nat | any | «fn» _ _ | inter _ _ | arr _ _ => simp [repOf] at hrep

theorem valOk_fieldNat_bound {P : Program} {cert : ShapeCert} {feat : Features}
    {s : Shape} {n : Nat}
    (hfn : (repOf P cert feat s).isFieldNat = true)
    (hok : ValOk cert dummyEnc s (.lit (.nat n)))
    (hlt : n < natLimit) :
    n < (repOf P cert feat s).fieldBound := by
  cases hrep : repOf P cert feat s with
  | nat b => exact valOk_nat_bound hrep hok hlt
  | w8 =>
    obtain ⟨m, hm, heq⟩ := valOk_w8_bound hrep hok
    cases heq; exact hm
  | w16 =>
    obtain ⟨m, hm, heq⟩ := valOk_w16_bound hrep hok
    cases heq; exact hm
  | irr | w32 | w64 | «enum» _ | data _ | obj => simp [hrep, Rep.isFieldNat] at hfn

/-! ### `TState` Monotonicity and Public Mirrors of Private `TypedLower` Helpers -/

/-- State monotonicity for non-lifting `TLowerM` steps (`lifted` unchanged). -/
structure TStateLe (s₁ s₂ : TState) : Prop where
  nextLocal : s₁.nextLocal ≤ s₂.nextLocal
  nextJp : s₁.nextJp ≤ s₂.nextJp
  lifted : s₂.lifted = s₁.lifted
  demand : DemandLe s₁.demand s₂.demand

theorem TStateLe.refl (s : TState) : TStateLe s s where
  nextLocal := Nat.le_refl _
  nextJp := Nat.le_refl _
  lifted := rfl
  demand := DemandLe.refl _

theorem TStateLe.trans {s₁ s₂ s₃ : TState} (h1 : TStateLe s₁ s₂) (h2 : TStateLe s₂ s₃) :
    TStateLe s₁ s₃ where
  nextLocal := Nat.le_trans h1.nextLocal h2.nextLocal
  nextJp := Nat.le_trans h1.nextJp h2.nextJp
  lifted := h2.lifted.trans h1.lifted
  demand := h1.demand.trans h2.demand

/-- General state monotonicity for `tCodeE`/`tAltsE`/`tOptE` (`lifted` grows monotonically). -/
structure TCodeStateLe (s₁ s₂ : TState) : Prop where
  nextLocal : s₁.nextLocal ≤ s₂.nextLocal
  nextJp : s₁.nextJp ≤ s₂.nextJp
  lifted : ∀ g ∈ s₁.lifted, g ∈ s₂.lifted
  demand : DemandLe s₁.demand s₂.demand

theorem TCodeStateLe.refl (s : TState) : TCodeStateLe s s where
  nextLocal := Nat.le_refl _
  nextJp := Nat.le_refl _
  lifted _ h := h
  demand := DemandLe.refl _

theorem TCodeStateLe.trans {s₁ s₂ s₃ : TState} (h1 : TCodeStateLe s₁ s₂) (h2 : TCodeStateLe s₂ s₃) :
    TCodeStateLe s₁ s₃ where
  nextLocal := Nat.le_trans h1.nextLocal h2.nextLocal
  nextJp := Nat.le_trans h1.nextJp h2.nextJp
  lifted g hg := h2.lifted g (h1.lifted g hg)
  demand := h1.demand.trans h2.demand

theorem TStateLe.toCodeLe {s₁ s₂ : TState} (h : TStateLe s₁ s₂) : TCodeStateLe s₁ s₂ where
  nextLocal := h.nextLocal
  nextJp := h.nextJp
  lifted _ hg := h.lifted ▸ hg
  demand := h.demand

/-- Public mirror of `TypedLower.tBindVm`. -/
def bindTVm (vm : TVarMap) : List Var → List (String × Rep) → TVarMap
  | x :: xs, nr :: nrs => bindTVm ((x, nr) :: vm) xs nrs
  | _, _ => vm

/-- Public mirror of `TypedLower.constSubMatch`. -/
def constSubMatchE (xExpr : Lower.Expr) (k : Nat) : Lower.Expr :=
  let zeroArms := (List.range k).map fun i => (.literal i, litE 0)
  matchE xExpr (zeroArms ++ [(.wildcard, subE xExpr (litE k))])

/-- An expression of the unsatisfiable trap shape `let _ = assertEq 0 1; dv`. -/
def isTrapExpr (e : Lower.Expr) : Prop :=
  ∃ msg dv, e = seqE (.builtin (.assertEq (assertion msg)) [litE 0, litE 1]) dv

theorem evalExprN_of_isTrapExpr {F : Type} [Field F] [DecidableEq F]
    {world : World F} {d : Nat} {locals : Environment F Nat}
    {e : Lower.Expr} {h h' : Heap F} {r : SourceValue F}
    (ht : isTrapExpr e)
    (ev : EvalExprN world d [] locals (qualifyExprF F e) h r h') : False := by
  obtain ⟨msg, dv, rfl⟩ := ht
  exact evalExprN_assert01_elim ev

private theorem mem_mapM_stateT {α β : Type} {f : α → TLowerM β} :
    ∀ {xs : List α} {st st' : TState} {ys : List β},
      (∀ a ∈ xs, ∀ s b s', f a s = .ok (b, s') → TStateLe s s') →
      xs.mapM (m := TLowerM) f st = .ok (ys, st') →
      TStateLe st st' ∧ ys.length = xs.length ∧
      ∀ a ∈ xs, ∃ b st1 st2, b ∈ ys ∧ f a st1 = .ok (b, st2) ∧
        TStateLe st st1 ∧ TStateLe st2 st'
  | [], st, st', ys, _, h => by
    simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨TStateLe.refl _, rfl, fun _ hm => by cases hm⟩
  | a :: tl, st, st', ys, hle, h => by
    have hcons : (a :: tl).mapM (m := TLowerM) f st =
        (do let b ← f a; let bs ← tl.mapM (m := TLowerM) f; pure (b :: bs)) st := by
      simp [List.mapM_cons]
    rw [hcons] at h
    simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure] at h
    cases h1 : f a st with
    | error _ => simp [h1] at h
    | ok r1 =>
      rcases r1 with ⟨b, st1⟩
      simp only [h1] at h
      cases h2 : tl.mapM (m := TLowerM) f st1 with
      | error _ => simp [h2] at h
      | ok r2 =>
        rcases r2 with ⟨bs, st2⟩
        simp only [h2, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hle1 := hle a List.mem_cons_self st b st1 h1
        obtain ⟨hle2, hlen, hall⟩ :=
          mem_mapM_stateT (fun x hx => hle x (List.mem_cons_of_mem _ hx)) h2
        refine ⟨hle1.trans hle2, by simp [hlen], ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | htl
        · exact ⟨b, st, st1, List.mem_cons_self, h1, TStateLe.refl _, hle2⟩
        · obtain ⟨y, s1, s2, hym, hfy, hs1, hs2⟩ := hall x htl
          exact ⟨y, s1, s2, List.mem_cons_of_mem _ hym, hfy, hle1.trans hs1, hs2⟩

private theorem getElem?_mapM_stateT {α β : Type} {f : α → TLowerM β} :
    ∀ {xs : List α} {st st' : TState} {ys : List β},
      (∀ a ∈ xs, ∀ s b s', f a s = .ok (b, s') → TStateLe s s') →
      xs.mapM (m := TLowerM) f st = .ok (ys, st') →
      ∀ (i : Nat) (a : α), xs[i]? = some a →
        ∃ b st1 st2, ys[i]? = some b ∧ f a st1 = .ok (b, st2) ∧
          TStateLe st st1 ∧ TStateLe st2 st'
  | [], _, _, _, _, _, _, _, hx => by simp at hx
  | a :: tl, st, st', ys, hle, h, i, x, hx => by
    have hcons : (a :: tl).mapM (m := TLowerM) f st =
        (do let b ← f a; let bs ← tl.mapM (m := TLowerM) f; pure (b :: bs)) st := by
      simp [List.mapM_cons]
    rw [hcons] at h
    simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure] at h
    cases h1 : f a st with
    | error _ => simp [h1] at h
    | ok r1 =>
      rcases r1 with ⟨b, st1⟩
      simp only [h1] at h
      cases h2 : tl.mapM (m := TLowerM) f st1 with
      | error _ => simp [h2] at h
      | ok r2 =>
        rcases r2 with ⟨bs, st2⟩
        simp only [h2, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hle1 := hle a List.mem_cons_self st b st1 h1
        have hleTl := fun x hx => hle x (List.mem_cons_of_mem _ hx)
        obtain ⟨hle2, _, _⟩ := mem_mapM_stateT hleTl h2
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          exact ⟨b, st, st1, rfl, h1, TStateLe.refl _, hle2⟩
        | succ i' =>
          simp only [List.getElem?_cons_succ] at hx ⊢
          obtain ⟨y, s1, s2, hy, hfy, hs1, hs2⟩ := getElem?_mapM_stateT hleTl h2 i' x hx
          exact ⟨y, s1, s2, hy, hfy, hle1.trans hs1, hs2⟩

/-! ### Reusable Polymorphic Unlock Lemmas for Private `TypedLower` Helpers -/

private theorem freshLocals_poly
    (fFL : Nat → TLowerM (List String))
    (h0 : ∀ st, fFL 0 st = .ok ([], st))
    (hS : ∀ n st, fFL (n + 1) st =
      (fFL n { st with nextLocal := st.nextLocal + 1 }).bind fun (t, s') =>
        .ok (localName st.nextLocal :: t, s')) :
    ∀ n st, fFL n st =
      .ok ((List.range n).map (fun i => localName (st.nextLocal + i)),
        { st with nextLocal := st.nextLocal + n }) := by
  intro n
  induction n with
  | zero => intro st; simpa using h0 st
  | succ n ih =>
    intro st
    rw [hS, ih]
    simp only [Except.bind, Except.ok.injEq, Prod.mk.injEq, TState.mk.injEq, and_true]
    constructor
    · rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp [Nat.add_assoc, Nat.add_comm 1 i]
    · omega

private theorem bindTVm_poly
    (fBV : TVarMap → List Var → List (String × Rep) → TVarMap)
    (hCons : ∀ vm x xs nr nrs, fBV vm (x :: xs) (nr :: nrs) = fBV ((x, nr) :: vm) xs nrs)
    (hNil1 : ∀ vm nrs, fBV vm [] nrs = vm)
    (hNil2 : ∀ vm x xs, fBV vm (x :: xs) [] = vm) :
    ∀ vm ps nrs, fBV vm ps nrs = bindTVm vm ps nrs := by
  intro vm ps
  induction ps generalizing vm with
  | nil => intro nrs; exact hNil1 vm nrs
  | cons x xs ih =>
    intro nrs
    cases nrs with
    | nil => exact hNil2 vm x xs
    | cons nr nrs =>
      rw [hCons, ih]
      rfl

private theorem markRep_poly
    (fMR : Rep → TLowerM Unit)
    (hObj : ∀ st, fMR .obj st = .ok ((), { st with demand := { st.demand with needObj := true } }))
    (hW64 : ∀ st, fMR .w64 st = .ok ((), { st with demand := { st.demand with needU64Bitwise := true } }))
    (hOther : ∀ r st, r ≠ .obj → r ≠ .w64 → fMR r st = .ok ((), st)) :
    ∀ r st, ∃ st', fMR r st = .ok ((), st') ∧
      st'.nextLocal = st.nextLocal ∧ st'.nextJp = st.nextJp ∧
      st'.lifted = st.lifted ∧ DemandLe st.demand st'.demand := by
  intro r st
  cases r with
  | obj =>
    exact ⟨_, hObj st, rfl, rfl, rfl, by constructor <;> first | exact id | (intro _; rfl)⟩
  | w64 =>
    exact ⟨_, hW64 st, rfl, rfl, rfl, by constructor <;> first | exact id | (intro _; rfl)⟩
  | irr | nat _ | w8 | w16 | w32 | «enum» _ | data _ =>
    exact ⟨st, hOther _ st (by simp) (by simp), rfl, rfl, rfl, DemandLe.refl _⟩

private theorem forIn_markRep_poly {α : Type} (g : α → Rep)
    (fMR : Rep → TLowerM Unit)
    (hMR : ∀ r st, ∃ st', fMR r st = .ok ((), st') ∧
      st'.nextLocal = st.nextLocal ∧ st'.nextJp = st.nextJp ∧
      st'.lifted = st.lifted ∧ DemandLe st.demand st'.demand) :
    ∀ (xs : List α) (st : TState),
      ∃ st',
        (forIn xs PUnit.unit (fun x _ => StateT.bind (fMR (g x)) fun _ =>
          StateT.pure (ForInStep.yield PUnit.unit)) : TLowerM PUnit) st = .ok (PUnit.unit, st') ∧
        st'.nextLocal = st.nextLocal ∧ st'.nextJp = st.nextJp ∧
        st'.lifted = st.lifted ∧ DemandLe st.demand st'.demand
  | [], st => ⟨st, rfl, rfl, rfl, rfl, DemandLe.refl _⟩
  | x :: xs, st => by
    obtain ⟨st1, h1, hnl1, hnj1, hlf1, hd1⟩ := hMR (g x) st
    obtain ⟨st2, h2, hnl2, hnj2, hlf2, hd2⟩ := forIn_markRep_poly g fMR hMR xs st1
    refine ⟨st2, ?_, hnl2.trans hnl1, hnj2.trans hnj1, hlf2.trans hlf1, hd1.trans hd2⟩
    simp only [forIn, List.forIn'_cons, bind, StateT.bind, StateT.pure, Except.bind, h1]
    exact h2

private theorem dedupByFst_spec :
    ∀ (xs acc : List (String × Rep)),
      (acc.map Prod.fst).Nodup →
      let res := xs.foldl (init := acc) fun a p => if a.any (·.1 == p.1) then a else a ++ [p]
      (res.map Prod.fst).Nodup ∧ (∀ p ∈ res, p ∈ acc ∨ p ∈ xs)
  | [], acc, hnd => ⟨hnd, fun _ hp => Or.inl hp⟩
  | p :: xs, acc, hnd => by
    simp only [List.foldl_cons]
    by_cases hany : acc.any (·.1 == p.1) = true
    · simp only [hany, ↓reduceIte]
      obtain ⟨hnd', hmem⟩ := dedupByFst_spec xs acc hnd
      exact ⟨hnd', fun q hq => (hmem q hq).imp id (List.mem_cons_of_mem p)⟩
    · simp only [hany, Bool.false_eq_true, ↓reduceIte]
      have hni : p.1 ∉ acc.map Prod.fst := by
        intro hm
        obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hm
        exact hany (List.any_eq_true.mpr ⟨q, hq, by simp [hqp]⟩)
      have hnd1 : ((acc ++ [p]).map Prod.fst).Nodup := by
        rw [List.map_append, List.map_singleton, List.nodup_append]
        refine ⟨hnd, List.nodup_singleton _, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        intro heq; subst heq; exact hni ha
      obtain ⟨hnd', hmem⟩ := dedupByFst_spec xs (acc ++ [p]) hnd1
      refine ⟨hnd', fun q hq => ?_⟩
      rcases hmem q hq with h1 | h2
      · rcases List.mem_append.mp h1 with ha | hp'
        · exact Or.inl ha
        · simp only [List.mem_singleton] at hp'; subst hp'; exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem p h2)

private theorem collectJpCaptures_poly
    (fCap : TVarMap → List TJEntry → List Var → JoinId → Bool → Code → Bool → List (String × Rep))
    (fFree : TVarMap → List Var → List (JoinId × List String) → Code → List String)
    (hDef : ∀ (vm : TVarMap) (jenv : List TJEntry) (ps : List Var) (j : JoinId)
        (isRec : Bool) (body : Code) (fc : Bool),
      fCap vm jenv ps j isRec body fc =
        let allScope : List (String × Rep) :=
          ((vm.map fun (p : Var × String × Rep) => p.2) ++ jenv.flatMap TJEntry.capVars).foldl (init := [])
            fun (acc : List (String × Rep)) (p : String × Rep) => if acc.any (·.1 == p.1) then acc else acc ++ [p]
        if !fc then allScope
        else
          let initJmap :=
            let base := jenv.map fun (je : TJEntry) => (je.id, je.capVars.map Prod.fst)
            if isRec then (j, []) :: base else base
          let needed := fFree vm ps initJmap body
          allScope.filter fun (p : String × Rep) => needed.contains p.1) :
    ∀ vm jenv ps j isRec body fc,
      ((fCap vm jenv ps j isRec body fc).map Prod.fst).Nodup ∧
      ∀ p ∈ fCap vm jenv ps j isRec body fc,
        p ∈ (vm.map fun (q : Var × String × Rep) => q.2) ++ jenv.flatMap TJEntry.capVars := by
  intro vm jenv ps j isRec body fc
  rw [hDef]
  set src := (vm.map fun (q : Var × String × Rep) => q.2) ++ jenv.flatMap TJEntry.capVars
  obtain ⟨hnd, hmem⟩ := dedupByFst_spec src [] List.nodup_nil
  have hmem' : ∀ p ∈ src.foldl (init := [])
      (fun a p => if a.any (·.1 == p.1) then a else a ++ [p]), p ∈ src := by
    intro p hp; rcases hmem p hp with h1 | h2
    · cases h1
    · exact h2
  cases fc
  · exact ⟨hnd, hmem'⟩
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    constructor
    · exact List.Nodup.sublist (List.Sublist.map Prod.fst (List.filter_sublist)) hnd
    · intro p hp
      exact hmem' p (List.mem_of_mem_filter hp)

/-! ### `isCleanNoU32` Combinator Lemmas -/

private theorem isCleanNoU32_bytesE : ∀ bs, isCleanNoU32 (bytesE bs) = true
  | [] => rfl
  | _ :: rest => by
    simp [bytesE, Lower.bytesConsE, isCleanNoU32, isCleanNoU32List, isCleanNoU32_bytesE rest]

private theorem isCleanNoU32_strE (s : String) : isCleanNoU32 (strE s) = true := by
  simpa [strE, mk, isCleanNoU32, isCleanNoU32List] using isCleanNoU32_bytesE s.toUTF8.toList

private theorem isCleanNoU32_trapE (msg : String) : isCleanNoU32 (trapE msg) = true := by
  simp [trapE, seqE, erasedE, mk, litE, isCleanNoU32, isCleanNoU32List, isSimplePat]

private theorem isCleanNoU32Arms_append {a b : List (Lower.Pat × Lower.Expr)}
    (ha : isCleanNoU32Arms a = true) (hb : isCleanNoU32Arms b = true) :
    isCleanNoU32Arms (a ++ b) = true := by
  rw [isCleanNoU32Arms_iff] at ha hb ⊢
  intro x hx
  rcases List.mem_append.mp hx with h1 | h2
  · exact ha x h1
  · exact hb x h2

private theorem isCleanNoU32_projE (cx : Lower.Cx) (nx : String) (c : CtorKey) (i : Nat) :
    isCleanNoU32 (Lower.projE cx nx c i) = true := by
  unfold Lower.projE
  have hsp : ∀ (l : List Nat), isSimplePatList (l.map fun j =>
      if j = i then .bind "q" else .wildcard) = true := by
    intro l; induction l with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.map_cons, isSimplePatList, ih, Bool.and_true]
      split <;> rfl
  have htab : isCleanNoU32Arms (match cx.ctorEntry? c with
      | some (idx, entry) =>
        if i < entry.arity then
          [(pC (ctorNameOf idx entry.key)
              ((List.range entry.arity).map fun j => if j = i then .bind "q" else .wildcard),
            .load (vE "q"))]
        else []
      | none => []) = true := by
    cases cx.ctorEntry? c with
    | none => rfl
    | some ie =>
      rcases ie with ⟨idx, entry⟩
      by_cases hlt : i < entry.arity
      · simp [hlt, isCleanNoU32Arms, pC, isSimplePat, hsp, isCleanNoU32, vE]
      · simp [hlt]; rfl
  have hnat : isCleanNoU32Arms (if cx.P.known.natSucc == some c && i == 0 then
      [(pN (.bind "q"),
        matchE (vE "q")
          [(.literal 0, trapE "Nat.zero has no field"),
           (.wildcard, natE (subE (vE "q") (litE 1)))])]
      else []) = true := by
    by_cases hns : (cx.P.known.natSucc == some c && i == 0) = true
    · simp [hns, isCleanNoU32Arms, pN, matchE, natE, mk, subE, vE, litE, isSimplePat,
        isSimplePatList, isCleanNoU32, isCleanNoU32List, isCleanNoU32_trapE]
    · simp [hns]; rfl
  set tableArm : List (Lower.Pat × Lower.Expr) := match cx.ctorEntry? c with
    | some (idx, entry) =>
      if i < entry.arity then
        [(pC (ctorNameOf idx entry.key)
            ((List.range entry.arity).map fun j => if j = i then .bind "q" else .wildcard),
          .load (vE "q"))]
      else []
    | none => []
  set natArm : List (Lower.Pat × Lower.Expr) :=
    if cx.P.known.natSucc == some c && i == 0 then
      [(pN (.bind "q"),
        matchE (vE "q")
          [(.literal 0, trapE "Nat.zero has no field"),
           (.wildcard, natE (subE (vE "q") (litE 1)))])]
    else []
  have harms : isCleanNoU32Arms (tableArm ++ natArm) = true := isCleanNoU32Arms_append htab hnat
  change isCleanNoU32 (if (tableArm ++ natArm).isEmpty then trapE "projection of a missing field"
    else matchE (vE nx) (tableArm ++ natArm)) = true
  by_cases hemp : (tableArm ++ natArm).isEmpty = true
  · simp only [hemp, ↓reduceIte]; exact isCleanNoU32_trapE _
  · simp only [hemp, Bool.false_eq_true, ↓reduceIte, matchE, vE, isCleanNoU32, Bool.true_and]
    exact harms

private theorem isCleanNoU32Arms_ctorArms (cx : Lower.Cx) :
    ∀ {alts : List (CtorKey × Lower.Expr)},
      (∀ p ∈ alts, isCleanNoU32 p.2 = true) →
      isCleanNoU32Arms (Lower.ctorArms cx alts) = true
  | [], _ => rfl
  | (k, b) :: rest, hall => by
    have hb : isCleanNoU32 b = true := hall (k, b) List.mem_cons_self
    have hr : isCleanNoU32Arms (Lower.ctorArms cx rest) = true :=
      isCleanNoU32Arms_ctorArms cx fun p hp => hall p (List.mem_cons_of_mem _ hp)
    unfold Lower.ctorArms
    cases hce : cx.ctorEntry? k with
    | none => simpa using hr
    | some ie =>
      have hrep : ∀ n, isSimplePatList (List.replicate n (.wildcard : Lower.Pat)) = true := by
        intro n; induction n with
        | zero => rfl
        | succ n ih => simp [List.replicate_succ, isSimplePatList, isSimplePat, ih]
      simp [isCleanNoU32Arms, pC, isSimplePat, hrep, hb, hr]

private theorem isCleanNoU32_constSubMatchE {e : Lower.Expr} (he : isCleanNoU32 e = true) (k : Nat) :
    isCleanNoU32 (constSubMatchE e k) = true := by
  unfold constSubMatchE
  simp only [matchE, isCleanNoU32, he, Bool.true_and]
  have hzero : ∀ l : List Nat,
      isCleanNoU32Arms (l.map (fun i => (Aiur.Generic.Pattern.literal i, litE 0)) ++
        [(Aiur.Generic.Pattern.wildcard, subE e (litE k))]) = true := by
    intro l
    induction l with
    | nil => simp [isCleanNoU32Arms, isSimplePat, subE, litE, isCleanNoU32, he]
    | cons hd tl ih =>
      simp only [List.map_cons, List.cons_append, isCleanNoU32Arms, isSimplePat, ih,
        Bool.true_and, Bool.and_true]
      rfl
  exact hzero (List.range k)

private theorem isCleanNoU32_mk {nm : String} {xs : List Lower.Expr}
    (h : isCleanNoU32List xs = true) : isCleanNoU32 (mk nm xs) = true := by
  simpa [mk, isCleanNoU32] using h

private theorem isCleanNoU32_letE {nm : String} {v b : Lower.Expr}
    (hv : isCleanNoU32 v = true) (hb : isCleanNoU32 b = true) :
    isCleanNoU32 (letE nm v b) = true := by
  simp [letE, isCleanNoU32, isSimplePat, hv, hb]

private theorem isCleanNoU32_seqE {a b : Lower.Expr}
    (ha : isCleanNoU32 a = true) (hb : isCleanNoU32 b = true) :
    isCleanNoU32 (seqE a b) = true := by
  simp [seqE, isCleanNoU32, isSimplePat, ha, hb]

private theorem isCleanNoU32_callE {nm : String} {xs : List Lower.Expr}
    (hnm : isPeepholeU32Name nm = false) (hxs : isCleanNoU32List xs = true) :
    isCleanNoU32 (callE nm xs) = true := by
  simp [callE, isCleanNoU32, hnm, hxs]

private theorem isPeepholeU32Name_false_of_head {s : String}
    (hU : s.toList.head? ≠ some 'U') (hu : s.toList.head? ≠ some 'u')
    (hP : s.toList.head? ≠ some 'P') : isPeepholeU32Name s = false := by
  have hne : ∀ t : String,
      (t.toList.head? = some 'U' ∨ t.toList.head? = some 'u' ∨ t.toList.head? = some 'P') →
      s ≠ t := by
    intro t ht heq; subst heq; rcases ht with h | h | h
    · exact hU h
    · exact hu h
    · exact hP h
  unfold isPeepholeU32Name
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
    exact hne _ (by decide)

private theorem isPeepholeU32Name_funName (f : FunId) :
    isPeepholeU32Name (funName f) = false :=
  isPeepholeU32Name_false_of_head (by simp [funName]) (by simp [funName]) (by simp [funName])

private theorem isPeepholeU32Name_jpFunName (f : FunId) (uid : Nat) :
    isPeepholeU32Name (jpFunName f uid) = false :=
  isPeepholeU32Name_false_of_head (by simp [jpFunName]) (by simp [jpFunName]) (by simp [jpFunName])

/-! ### `dummyOfRepAux` / `tTrapE` Polymorphic Spec -/

private theorem dummySpec_poly
    (fDummy : Nat → TCx → Rep → TLowerM Lower.Expr)
    (hDef : ∀ fuel cx r, fDummy fuel cx r =
      match r with
      | .irr => pure (.tuple [])
      | .nat _ | .w8 | .w16 => pure (litE 0)
      | .w32 => pure (callE "UInt32::from_field" [litE 0])
      | .w64 => fun st => .ok (callE "UInt64::from_field" [litE 0],
          { st with demand := { st.demand with needU64Bitwise := true } })
      | .enum ind => fun st =>
        match cx.cert.enum? ind with
        | some (k :: _) =>
          match cx.ctorEntry? k with
          | some (idx, e) => .ok (.construct (enumName ind) (some []) (ctorNameOf idx e.key) [], st)
          | none => .error "dummy: missing enum ctor"
        | _ => .error s!"dummy: empty enum {ind}"
      | .data d =>
        match fuel with
        | 0 => fun _ => .error s!"dummy: data {d} exceeded depth"
        | fuel' + 1 => fun st =>
          match cx.cert.data? d with
          | none => .error s!"dummy: missing data {d}"
          | some D =>
            match D.ctors.find? (fun (_, fl) => fl.all fun s => cx.rep s != .data d) with
            | none => .error s!"dummy: data {d} has no base constructor"
            | some (k, fl) =>
              match cx.ctorEntry? k with
              | none => .error "dummy: missing data ctor"
              | some (idx, e) =>
                match (fl.mapM (m := TLowerM) fun s => do
                  let fr := cx.rep s
                  let dv ← fDummy fuel' cx fr
                  return if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .store dv else dv) st with
                | .error err => .error err
                | .ok (args, st') =>
                  .ok (.construct (dataName d) (some []) (ctorNameOf idx e.key) args, st')
      | .obj => fun st => .ok (erasedE, { st with demand := { st.demand with needObj := true } })) :
    ∀ fuel cx r st e st',
      fDummy fuel cx r st = .ok (e, st') →
      TStateLe st st' ∧
      (isNatCoreRep r = true → datasNatCoreReps cx.P cx.cert cx.feat = true →
        isCleanNoU32 e = true) := by
  intro fuel
  induction fuel with
  | zero =>
    intro cx r st e st' h
    rw [hDef] at h
    cases r with
    | irr | nat _ | w8 | w16 =>
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨TStateLe.refl _, fun _ _ => rfl⟩
    | w32 =>
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨TStateLe.refl _, fun hr _ => by simp [isNatCoreRep] at hr⟩
    | w64 =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, fun hr _ => by simp [isNatCoreRep] at hr⟩
      exact ⟨Nat.le_refl _, Nat.le_refl _, rfl,
        by constructor <;> first | exact id | (intro _; rfl)⟩
    | «enum» ind =>
      cases he : cx.cert.enum? ind with
      | none => simp [he] at h
      | some ks =>
        cases ks with
        | nil => simp [he] at h
        | cons k _ =>
          simp only [he] at h
          cases hc : cx.ctorEntry? k with
          | none => simp [hc] at h
          | some ie =>
            simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨TStateLe.refl _, fun _ _ => rfl⟩
    | data d => cases h
    | obj =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, fun _ _ => rfl⟩
      exact ⟨Nat.le_refl _, Nat.le_refl _, rfl,
        by constructor <;> first | exact id | (intro _; rfl)⟩
  | succ fuel' ih =>
    intro cx r st e st' h
    rw [hDef] at h
    cases r with
    | irr | nat _ | w8 | w16 =>
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨TStateLe.refl _, fun _ _ => rfl⟩
    | w32 =>
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨TStateLe.refl _, fun hr _ => by simp [isNatCoreRep] at hr⟩
    | w64 =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, fun hr _ => by simp [isNatCoreRep] at hr⟩
      exact ⟨Nat.le_refl _, Nat.le_refl _, rfl,
        by constructor <;> first | exact id | (intro _; rfl)⟩
    | «enum» ind =>
      cases he : cx.cert.enum? ind with
      | none => simp [he] at h
      | some ks =>
        cases ks with
        | nil => simp [he] at h
        | cons k _ =>
          simp only [he] at h
          cases hc : cx.ctorEntry? k with
          | none => simp [hc] at h
          | some ie =>
            simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨TStateLe.refl _, fun _ _ => rfl⟩
    | obj =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, fun _ _ => rfl⟩
      exact ⟨Nat.le_refl _, Nat.le_refl _, rfl,
        by constructor <;> first | exact id | (intro _; rfl)⟩
    | data d =>
      cases hD : cx.cert.data? d with
      | none => simp [hD] at h
      | some D =>
        simp only [hD] at h
        cases hfind : D.ctors.find? (fun (_, fl) => fl.all fun s => cx.rep s != .data d) with
        | none => simp [hfind] at h
        | some kfl =>
          rcases kfl with ⟨k, fl⟩
          simp only [hfind] at h
          cases hce : cx.ctorEntry? k with
          | none => simp [hce] at h
          | some ie =>
            simp only [hce] at h
            let stepFn : Shape → TLowerM Lower.Expr := fun s => do
              let fr := cx.rep s
              let dv ← fDummy fuel' cx fr
              return if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.store dv else dv
            have hstep : ∀ s st1 a st2, stepFn s st1 = .ok (a, st2) →
                TStateLe st1 st2 ∧
                (datasNatCoreReps cx.P cx.cert cx.feat = true → s ∈ fl → isCleanNoU32 a = true) := by
              intro s st1 a st2 hs
              simp only [stepFn, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure] at hs
              cases hdum : fDummy fuel' cx (cx.rep s) st1 with
              | error _ => simp [hdum] at hs
              | ok res =>
                rcases res with ⟨dv, st1'⟩
                simp only [hdum, Except.ok.injEq, Prod.mk.injEq] at hs
                obtain ⟨rfl, rfl⟩ := hs
                obtain ⟨hle1, hcl1⟩ := ih cx (cx.rep s) st1 dv st1' hdum
                refine ⟨hle1, fun hdatas hms => ?_⟩
                have hcore : isNatCoreRep (cx.rep s) = true :=
                  datasNatCoreReps_field hdatas hD (List.mem_of_find?_eq_some hfind) hms
                have hdv := hcl1 hcore hdatas
                split <;> simpa [isCleanNoU32] using hdv
            change (match (fl.mapM (m := TLowerM) stepFn) st with
              | Except.error err => Except.error err
              | Except.ok (args, st') =>
                Except.ok (Aiur.Generic.Expr.construct (dataName d) (some []) (ctorNameOf ie.1 ie.2.key) args, st')) =
                Except.ok (e, st') at h
            cases hmap : (fl.mapM (m := TLowerM) stepFn) st with
            | error _ => rw [hmap] at h; cases h
            | ok res =>
              rcases res with ⟨args, st1⟩
              rw [hmap] at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hlist : ∀ (ls : List Shape) (s0 s1 : TState) (as : List Lower.Expr),
                  (∀ s ∈ ls, s ∈ fl) →
                  (ls.mapM (m := TLowerM) stepFn) s0 = .ok (as, s1) →
                  TStateLe s0 s1 ∧ (datasNatCoreReps cx.P cx.cert cx.feat = true →
                    isCleanNoU32List as = true) := by
                intro ls
                induction ls with
                | nil =>
                  intro s0 s1 as _ hm
                  simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
                    Except.ok.injEq, Prod.mk.injEq] at hm
                  obtain ⟨rfl, rfl⟩ := hm
                  exact ⟨TStateLe.refl _, fun _ => rfl⟩
                | cons s0' tl ihtl =>
                  intro s0 s1 as hsub hm
                  have hcons : (s0' :: tl).mapM (m := TLowerM) stepFn s0 =
                      (do let a1 ← stepFn s0'; let as2 ← tl.mapM (m := TLowerM) stepFn; pure (a1 :: as2)) s0 := by
                    simp [List.mapM_cons]
                  rw [hcons] at hm
                  simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure] at hm
                  cases h1 : stepFn s0' s0 with
                  | error _ => simp [h1] at hm
                  | ok r1 =>
                    rcases r1 with ⟨a1, sa⟩
                    simp only [h1] at hm
                    cases h2 : (tl.mapM (m := TLowerM) stepFn) sa with
                    | error _ => simp [h2] at hm
                    | ok r2 =>
                      rcases r2 with ⟨as2, sb⟩
                      simp only [h2, Except.ok.injEq, Prod.mk.injEq] at hm
                      obtain ⟨rfl, rfl⟩ := hm
                      obtain ⟨hle1, hcl1⟩ := hstep s0' s0 a1 sa h1
                      obtain ⟨hle2, hcl2⟩ := ihtl sa sb as2
                        (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) h2
                      exact ⟨hle1.trans hle2, fun hdatas => by
                        simp [isCleanNoU32List, hcl1 hdatas (hsub s0' List.mem_cons_self),
                          hcl2 hdatas]⟩
              obtain ⟨hle, hcl⟩ := hlist fl st st1 args (fun _ hx => hx) hmap
              exact ⟨hle, fun _ hdatas => by simpa [isCleanNoU32] using hcl hdatas⟩

private theorem trapSpec_poly
    (fTrap : TCx → Rep → String → TLowerM Lower.Expr)
    (fDummy : Nat → TCx → Rep → TLowerM Lower.Expr)
    (hTrap : ∀ cx r msg st, fTrap cx r msg st =
      match fDummy (cx.cert.datas.length + 2) cx r st with
      | .error err => .error err
      | .ok (dv, st') =>
        .ok (seqE (.builtin (.assertEq (assertion msg)) [litE 0, litE 1]) dv, st'))
    (hDummy : ∀ fuel cx r st e st', fDummy fuel cx r st = .ok (e, st') →
      TStateLe st st' ∧
      (isNatCoreRep r = true → datasNatCoreReps cx.P cx.cert cx.feat = true →
        isCleanNoU32 e = true)) :
    ∀ cx r msg st e st', fTrap cx r msg st = .ok (e, st') →
      isTrapExpr e ∧ TStateLe st st' ∧
      (isNatCoreRep r = true → datasNatCoreReps cx.P cx.cert cx.feat = true →
        isCleanNoU32 e = true) := by
  intro cx r msg st e st' h
  rw [hTrap] at h
  cases hd : fDummy (cx.cert.datas.length + 2) cx r st with
  | error _ => simp [hd] at h
  | ok res =>
    rcases res with ⟨dv, st1⟩
    simp only [hd, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hle, hcl⟩ := hDummy _ cx r st dv st1 hd
    refine ⟨⟨msg, dv, rfl⟩, hle, fun hr hdatas => ?_⟩
    simp [seqE, litE, isCleanNoU32, isCleanNoU32List, isSimplePat, hcl hr hdatas]

/-! ### `TStateLe` + `isCleanNoU32` for `coerceEAux`, `tArgRaw`, `tArgE`, `tPrimE`, `tRhsE`, `tCaseE`, `tCodeE` -/

private theorem tBind_step_inv {α β : Type} {m : TLowerM α} {f : α → TLowerM β}
    {st st' : TState} {b : β} (h : (m >>= f) st = .ok (b, st')) :
    ∃ a st1, m st = .ok (a, st1) ∧ f a st1 = .ok (b, st') := by
  simp only [bind, StateT.bind, Except.bind] at h
  cases h1 : m st with
  | error _ => simp [h1] at h
  | ok r1 => rcases r1 with ⟨a, st1⟩; simp only [h1] at h; exact ⟨a, st1, rfl, h⟩

private theorem coerceEAux_spec_zero :
    ∀ cx fromR toR e st res st',
      coerceEAux 0 cx fromR toR e st = .ok (res, st') →
      TStateLe st st' ∧
      (isNatCoreRep fromR = true → isNatCoreRep toR = true →
        datasNatCoreReps cx.P cx.cert cx.feat = true →
        isCleanNoU32 e = true → isCleanNoU32 res = true) := by
  intro cx fromR toR e st res st' h
  unfold coerceEAux at h
  by_cases heq : (fromR == toR) = true
  · simp only [heq, ↓reduceIte, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨TStateLe.refl _, fun _ _ _ he => he⟩
  · simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
    have go : ∀ (fL : ∀ {α : Type}, Except String α → TLowerM α)
        (fF : TLowerM String) (fM : (Demand → Demand) → TLowerM Unit),
        (∀ {α} (r : Except String α) s, fL r s = match r with | .ok a => .ok (a, s) | .error err => .error err) →
        (∀ s, fF s = .ok (localName s.nextLocal, { s with nextLocal := s.nextLocal + 1 })) →
        (∀ u s, fM u s = .ok ((), { s with demand := u s.demand })) →
        (match fromR, toR with
        | .nat a, .nat b => (if a ≤ b then pure e else pure e : TLowerM Lower.Expr)
        | .w8, .nat _ | .w8, .w16 => pure e
        | .w16, .nat _ => pure e
        | .nat a, .w8 =>
          if a ≤ 256 then pure e
          else do fM fun d => { d with needCheckU56 := true }
                  let tmp ← fF
                  return letE tmp e (seqE (callE "check_u8" [vE tmp]) (vE tmp))
        | .nat a, .w16 =>
          if a ≤ 65536 then pure e
          else do fM fun d => { d with needCheckU16 := true }
                  let tmp ← fF
                  return letE tmp e (seqE (callE "check_u16" [vE tmp]) (vE tmp))
        | .nat _, .w32 | .w8, .w32 | .w16, .w32 => do
          fM fun d => { d with needU32OfField := true }
          return callE "u32_of_field" [e]
          | .w32, .nat _ | .w32, .w8 | .w32, .w16 =>
            pure (callE "UInt32::compact_field" [callE "UInt32::compact" [e]])
          | .nat _, .w64 | .w8, .w64 | .w16, .w64 => do
            fM fun d => { d with needU64Bitwise := true }
            return callE "UInt64::from_field" [e]
          | .w64, .nat _ | .w64, .w8 | .w64, .w16 => do
            fM fun d => { d with needU64Bitwise := true }
            return callE "UInt64::to_field" [e]
          | .w32, .w64 => do
            fM fun d => { d with needU64Bitwise := true }
            return callE "UInt64::from_field" [callE "UInt32::compact_field" [callE "UInt32::compact" [e]]]
          | .w64, .w32 => do
            fM fun d => { d with needU64Bitwise := true }
            let tmp ← fF
            return letE tmp e <| callE "UInt32::from_bytes"
              [.array [.index (vE tmp) 0, .index (vE tmp) 1, .index (vE tmp) 2, .index (vE tmp) 3]]
          | .irr, .obj => do fM fun d => { d with needObj := true }; return seqE e erasedE
          | .nat _, .obj | .w8, .obj | .w16, .obj => do
            fM fun d => { d with needObj := true }; return natE e
          | .w32, .obj => do
            fM fun d => { d with needObj := true }
            return natE (callE "UInt32::compact_field" [callE "UInt32::compact" [e]])
          | .w64, .obj => do
            fM fun d => { d with needObj := true, needU64Bitwise := true }
            return natE (callE "UInt64::to_field" [e])
          | .enum ind, .obj => do
            fM fun d => { d with needObj := true }
            let some ks := cx.cert.enum? ind | fL (throw s!"coerce: unknown enum {ind}")
            let arms ← ks.mapM fun k => do
              let some (idx, entry) := cx.ctorEntry? k | fL (throw "coerce enum: missing ctor")
              let nm := ctorNameOf idx entry.key
              return (Aiur.Generic.Pattern.construct (.named (enumName ind) []) nm [], mk nm [])
            return matchE e arms
          | .data d, .obj => fL (throw s!"coerce: recursive data {d} → Obj exceeded depth")
          | .obj, .irr => do
            fM fun d => { d with needObj := true }; return matchE e [(pC "E" [], .tuple [])]
          | .obj, .nat _ | .obj, .w8 | .obj, .w16 => do
            fM fun d => { d with needObj := true }
            let tmp ← fF; return matchE e [(pN (.bind tmp), vE tmp)]
          | .obj, .w32 => do
            fM fun d => { d with needObj := true, needU32OfField := true }
            let tmp ← fF; return matchE e [(pN (.bind tmp), callE "u32_of_field" [vE tmp])]
          | .obj, .w64 => do
            fM fun d => { d with needObj := true, needU64Bitwise := true }
            let tmp ← fF; return matchE e [(pN (.bind tmp), callE "UInt64::from_field" [vE tmp])]
          | .obj, .enum ind => do
            fM fun d => { d with needObj := true }
            let some ks := cx.cert.enum? ind | fL (throw s!"coerce: unknown enum {ind}")
            let arms ← ks.mapM fun k => do
              let some (idx, entry) := cx.ctorEntry? k | fL (throw "coerce obj→enum: missing ctor")
              let nm := ctorNameOf idx entry.key
              return (pC nm [], Aiur.Generic.Expr.construct (enumName ind) (some []) nm [])
            return matchE e arms
          | .obj, .data d => fL (throw s!"coerce: recursive Obj → data {d} exceeded depth")
          | _, _ => fL (throw s!"unsupported coercion from {reprStr fromR} to {reprStr toR}")) st =
            .ok (res, st') →
          TStateLe st st' ∧
          (isNatCoreRep fromR = true → isNatCoreRep toR = true →
            datasNatCoreReps cx.P cx.cert cx.feat = true →
            isCleanNoU32 e = true → isCleanNoU32 res = true) := by
        intro fL fF fM hfL hfF hfM h0
        cases fromR <;> cases toR
        all_goals
          try simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure,
            throw, throwThe, MonadExceptOf.throw, hfL, hfF, hfM] at h0
        all_goals try (cases h0; done)
        all_goals try (
          simp only [Except.ok.injEq, Prod.mk.injEq] at h0
          obtain ⟨rfl, rfl⟩ := h0
          refine ⟨⟨by first | exact Nat.le_refl _ | exact Nat.le_succ _, Nat.le_refl _, rfl,
            by constructor <;> first | exact id | (intro _; rfl)⟩, ?_⟩
          intro hcf hct _ he
          first
          | exact absurd hcf (by decide)
          | exact absurd hct (by decide)
          | exact he
          | exact (show isCleanNoU32 _ = true by
              simp [seqE, erasedE, natE, mk, matchE, pC, pN, vE, isCleanNoU32, isCleanNoU32Arms,
                isCleanNoU32List, isSimplePat, isSimplePatList, he]))
        · -- .nat a, .nat b
          split at h0 <;> simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0 <;>
            obtain ⟨rfl, rfl⟩ := h0 <;> exact ⟨TStateLe.refl _, fun _ _ _ he => he⟩
        · -- .nat a, .w8
          split at h0
          · simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
            obtain ⟨rfl, rfl⟩ := h0; exact ⟨TStateLe.refl _, fun _ _ _ he => he⟩
          · simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure,
              hfM, hfF, Except.ok.injEq, Prod.mk.injEq] at h0
            obtain ⟨rfl, rfl⟩ := h0
            refine ⟨⟨by dsimp; omega, Nat.le_refl _, rfl,
              by constructor <;> first | exact id | (intro _; rfl)⟩, fun _ _ _ he => ?_⟩
            simp [letE, seqE, callE, vE, isCleanNoU32, isCleanNoU32List, isSimplePat,
              isPeepholeU32Name, he]
        · -- .nat a, .w16
          split at h0
          · simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
            obtain ⟨rfl, rfl⟩ := h0; exact ⟨TStateLe.refl _, fun _ _ _ he => he⟩
          · simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure,
              hfM, hfF, Except.ok.injEq, Prod.mk.injEq] at h0
            obtain ⟨rfl, rfl⟩ := h0
            refine ⟨⟨by dsimp; omega, Nat.le_refl _, rfl,
              by constructor <;> first | exact id | (intro _; rfl)⟩, fun _ _ _ he => ?_⟩
            simp [letE, seqE, callE, vE, isCleanNoU32, isCleanNoU32List, isSimplePat,
              isPeepholeU32Name, he]
        · -- .enum ind, .obj
          rename_i ind
          cases henum : cx.cert.enum? ind with
          | none => simp only [henum, hfL] at h0; cases h0
          | some ks =>
            simp only [henum] at h0
            have hstep : ∀ (ls : List CtorKey) (s0 s1 : TState) (arms : List (Lower.Pat × Lower.Expr)),
                (ls.mapM (m := TLowerM) fun k =>
                  match cx.ctorEntry? k with
                  | some (idx, entry) =>
                    StateT.pure (Aiur.Generic.Pattern.construct (.named (enumName ind) []) (ctorNameOf idx entry.key) [],
                      mk (ctorNameOf idx entry.key) [])
                  | _ => fL (Except.error "coerce enum: missing ctor")) s0 = .ok (arms, s1) →
                s1 = s0 ∧ isCleanNoU32Arms arms = true := by
              intro ls; induction ls with
              | nil =>
                intro s0 s1 arms hm
                simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
                  Except.ok.injEq, Prod.mk.injEq] at hm
                obtain ⟨rfl, rfl⟩ := hm; exact ⟨rfl, rfl⟩
              | cons k kt ihk =>
                intro s0 s1 arms hm
                rw [List.mapM_cons] at hm
                obtain ⟨arm1, sa, h1, hm⟩ := tBind_step_inv hm
                obtain ⟨at_, s2, htl, hm⟩ := tBind_step_inv hm
                simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm
                obtain ⟨rfl, rfl⟩ := hm
                cases hce : cx.ctorEntry? k with
                | none => simp [hce, hfL] at h1
                | some ie =>
                  simp only [hce, StateT.pure, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1
                  obtain ⟨rfl, rfl⟩ := h1
                  obtain ⟨rfl, hcl⟩ := ihk s0 s2 at_ htl
                  exact ⟨rfl, by simp [isCleanNoU32Arms, isSimplePat, isSimplePatList, mk,
                    isCleanNoU32, isCleanNoU32List, hcl]⟩
            obtain ⟨arms, s1, hm, h0⟩ := tBind_step_inv h0
            simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
            obtain ⟨rfl, rfl⟩ := h0
            obtain ⟨rfl, hcl⟩ := hstep ks _ s1 arms hm
            refine ⟨⟨Nat.le_refl _, Nat.le_refl _, rfl,
              by constructor <;> first | exact id | (intro _; rfl)⟩, fun _ _ _ he => ?_⟩
            simp [matchE, isCleanNoU32, he, hcl]
        · -- .obj, .enum ind
          rename_i ind
          cases henum : cx.cert.enum? ind with
          | none => simp only [henum, hfL] at h0; cases h0
          | some ks =>
            simp only [henum] at h0
            have hstep : ∀ (ls : List CtorKey) (s0 s1 : TState) (arms : List (Lower.Pat × Lower.Expr)),
                (ls.mapM (m := TLowerM) fun k =>
                  match cx.ctorEntry? k with
                  | some (idx, entry) =>
                    StateT.pure (pC (ctorNameOf idx entry.key) [],
                      Aiur.Generic.Expr.construct (enumName ind) (some []) (ctorNameOf idx entry.key) [])
                  | _ => fL (Except.error "coerce obj→enum: missing ctor")) s0 = .ok (arms, s1) →
                s1 = s0 ∧ isCleanNoU32Arms arms = true := by
              intro ls; induction ls with
              | nil =>
                intro s0 s1 arms hm
                simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
                  Except.ok.injEq, Prod.mk.injEq] at hm
                obtain ⟨rfl, rfl⟩ := hm; exact ⟨rfl, rfl⟩
              | cons k kt ihk =>
                intro s0 s1 arms hm
                rw [List.mapM_cons] at hm
                obtain ⟨arm1, sa, h1, hm⟩ := tBind_step_inv hm
                obtain ⟨at_, s2, htl, hm⟩ := tBind_step_inv hm
                simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm
                obtain ⟨rfl, rfl⟩ := hm
                cases hce : cx.ctorEntry? k with
                | none => simp [hce, hfL] at h1
                | some ie =>
                  simp only [hce, StateT.pure, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1
                  obtain ⟨rfl, rfl⟩ := h1
                  obtain ⟨rfl, hcl⟩ := ihk s0 s2 at_ htl
                  exact ⟨rfl, by simp [isCleanNoU32Arms, pC, isSimplePat, isSimplePatList,
                    isCleanNoU32, isCleanNoU32List, hcl]⟩
            obtain ⟨arms, s1, hm, h0⟩ := tBind_step_inv h0
            simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
            obtain ⟨rfl, rfl⟩ := h0
            obtain ⟨rfl, hcl⟩ := hstep ks _ s1 arms hm
            refine ⟨⟨Nat.le_refl _, Nat.le_refl _, rfl,
              by constructor <;> first | exact id | (intro _; rfl)⟩, fun _ _ _ he => ?_⟩
            simp [matchE, isCleanNoU32, he, hcl]
    exact go _ _ _ (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) h

theorem coerceEAux_spec :
    ∀ fuel cx fromR toR e st res st',
      coerceEAux fuel cx fromR toR e st = .ok (res, st') →
      TStateLe st st' ∧
      (isNatCoreRep fromR = true → isNatCoreRep toR = true →
        datasNatCoreReps cx.P cx.cert cx.feat = true →
        isCleanNoU32 e = true → isCleanNoU32 res = true) := by
  intro fuel
  induction fuel with
  | zero => exact coerceEAux_spec_zero
  | succ fuel' ih =>
    intro cx fromR toR e st res st' h
    unfold coerceEAux at h
    by_cases heq : (fromR == toR) = true
    · simp only [heq, ↓reduceIte, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨TStateLe.refl _, fun _ _ _ he => he⟩
    · simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
      -- For non-(.data/.obj) pairs, fuel' + 1 behaves identically to fuel = 0!
      cases fromR with
      | data d =>
        cases toR with
        | obj =>
          have go : ∀ (fFL : Nat → TLowerM (List String)) (fL : ∀ {α : Type}, Except String α → TLowerM α)
              (fM : (Demand → Demand) → TLowerM Unit),
              (∀ n s, fFL n s = .ok ((List.range n).map (fun i => localName (s.nextLocal + i)),
                { s with nextLocal := s.nextLocal + n })) →
              (∀ {α} (r : Except String α) s, fL r s = match r with | .ok a => .ok (a, s) | .error err => .error err) →
              (∀ u s, fM u s = .ok ((), { s with demand := u s.demand })) →
              (do fM fun d0 => { d0 with needObj := true }
                  let some D := cx.cert.data? d | fL (throw s!"coerce: unknown data {d}")
                  let arms ← D.ctors.mapM fun ((k, fl) : CtorKey × List Shape) => do
                    let some (idx, entry) := cx.ctorEntry? k | fL (throw "coerce data: missing ctor")
                    let nm := ctorNameOf idx entry.key
                    let fvars ← fFL fl.length
                    let fieldExprs ← (fl.zip fvars).mapM fun ((sh, fv) : Shape × String) => do
                      let fr := cx.rep sh
                      let raw : Lower.Expr :=
                        if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.load (vE fv) else vE fv
                      let asObj ← coerceEAux fuel' cx fr .obj raw
                      return Aiur.Generic.Expr.store asObj
                    return (Aiur.Generic.Pattern.construct (.named (dataName d) []) nm (fvars.map .bind),
                      mk nm fieldExprs)
                  return matchE e arms) st = .ok (res, st') →
              TStateLe st st' ∧
              (datasNatCoreReps cx.P cx.cert cx.feat = true → isCleanNoU32 e = true →
                isCleanNoU32 res = true) := by
            intro fFL fL fM hfFL hfL hfM h0
            simp only [bind, StateT.bind, pure, Except.bind, hfM] at h0
            cases hD : cx.cert.data? d with
            | none => simp [hD, hfL, throw, throwThe, MonadExceptOf.throw] at h0
            | some D =>
              simp only [hD] at h0
              have hle0 : TStateLe st { st with demand := { st.demand with needObj := true } } :=
                ⟨Nat.le_refl _, Nat.le_refl _, rfl,
                  by constructor <;> first | exact id | (intro _; rfl)⟩
              let armFn : CtorKey × List Shape → TLowerM (Lower.Pat × Lower.Expr) :=
                fun (k, fl) => do
                  let some (idx, entry) := cx.ctorEntry? k | fL (throw "coerce data: missing ctor")
                  let nm := ctorNameOf idx entry.key
                  let fvars ← fFL fl.length
                  let fieldExprs ← (fl.zip fvars).mapM fun ((sh, fv) : Shape × String) => do
                    let fr := cx.rep sh
                    let raw : Lower.Expr :=
                      if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.load (vE fv) else vE fv
                    let asObj ← coerceEAux fuel' cx fr .obj raw
                    return Aiur.Generic.Expr.store asObj
                  return (Aiur.Generic.Pattern.construct (.named (dataName d) []) nm (fvars.map .bind),
                    mk nm fieldExprs)
              have hfields : ∀ (fl : List Shape) (c : CtorKey), (c, fl) ∈ D.ctors →
                  ∀ (pairs : List (Shape × String)) (s0 s1 : TState) (es : List Lower.Expr),
                    (∀ p ∈ pairs, p.1 ∈ fl) →
                    (pairs.mapM (m := TLowerM) fun ((sh, fv) : Shape × String) => do
                      let fr := cx.rep sh
                      let raw : Lower.Expr :=
                        if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.load (vE fv) else vE fv
                      let asObj ← coerceEAux fuel' cx fr .obj raw
                      return Aiur.Generic.Expr.store asObj) s0 = .ok (es, s1) →
                    TStateLe s0 s1 ∧ (datasNatCoreReps cx.P cx.cert cx.feat = true →
                      isCleanNoU32List es = true) := by
                intro fl c hc pairs
                induction pairs with
                | nil =>
                  intro s0 s1 es _ hm
                  simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
                    Except.ok.injEq, Prod.mk.injEq] at hm
                  obtain ⟨rfl, rfl⟩ := hm; exact ⟨TStateLe.refl _, fun _ => rfl⟩
                | cons p pt ihp =>
                  intro s0 s1 es hsub hm
                  rcases p with ⟨sh, fv⟩
                  rw [List.mapM_cons] at hm
                  obtain ⟨e1, sa, h1, hm⟩ := tBind_step_inv hm
                  obtain ⟨es', sb, h2, hm⟩ := tBind_step_inv hm
                  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm
                  obtain ⟨rfl, rfl⟩ := hm
                  obtain ⟨asObj, sa', hco, h1⟩ := tBind_step_inv h1
                  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1
                  obtain ⟨rfl, rfl⟩ := h1
                  obtain ⟨hle1, hcl1⟩ := ih cx (cx.rep sh) .obj _ s0 asObj sa' hco
                  obtain ⟨hle2, hcl2⟩ := ihp sa' sb es'
                    (fun q hq => hsub q (List.mem_cons_of_mem _ hq)) h2
                  refine ⟨hle1.trans hle2, fun hdatas => ?_⟩
                  have hcore := datasNatCoreReps_field hdatas hD hc (hsub (sh, fv) List.mem_cons_self)
                  have hraw : isCleanNoU32
                      (if dataFieldNeedsPtr cx.P cx.cert cx.feat d (cx.rep sh)
                       then .load (vE fv) else vE fv) = true := by
                    split <;> rfl
                  simp [isCleanNoU32List, isCleanNoU32, hcl1 hcore rfl hdatas hraw, hcl2 hdatas]
              have harms : ∀ (cs : List (CtorKey × List Shape)) (s0 s1 : TState)
                  (arms : List (Lower.Pat × Lower.Expr)),
                  (∀ x ∈ cs, x ∈ D.ctors) →
                  (cs.mapM (m := TLowerM) fun (k, fl) => do
                    let some (idx, entry) := cx.ctorEntry? k | fL (throw "coerce data: missing ctor")
                    let nm := ctorNameOf idx entry.key
                    let fvars ← fFL fl.length
                    let fieldExprs ← (fl.zip fvars).mapM fun (sh, fv) => do
                      let fr := cx.rep sh
                      let raw := if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .load (vE fv) else vE fv
                      let asObj ← coerceEAux fuel' cx fr .obj raw
                      return .store asObj
                    return (.construct (.named (dataName d) []) nm (fvars.map .bind), mk nm fieldExprs)) s0 =
                    .ok (arms, s1) →
                  TStateLe s0 s1 ∧ (datasNatCoreReps cx.P cx.cert cx.feat = true →
                    isCleanNoU32Arms arms = true) := by
                intro cs; induction cs with
                | nil =>
                  intro s0 s1 arms _ hm
                  simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
                    Except.ok.injEq, Prod.mk.injEq] at hm
                  obtain ⟨rfl, rfl⟩ := hm; exact ⟨TStateLe.refl _, fun _ => rfl⟩
                | cons cf ct ihc =>
                  intro s0 s1 arms hsub hm
                  rcases cf with ⟨k, fl⟩
                  rw [List.mapM_cons] at hm
                  obtain ⟨arm1, sA, h1, hm⟩ := tBind_step_inv hm
                  obtain ⟨at_, sc, hf2, hm⟩ := tBind_step_inv hm
                  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm
                  obtain ⟨rfl, rfl⟩ := hm
                  cases hce : cx.ctorEntry? k with
                  | none => simp [hce, hfL, throw, throwThe, MonadExceptOf.throw] at h1
                  | some ie =>
                    simp only [hce] at h1
                    obtain ⟨fvars, sa, hfv, h1⟩ := tBind_step_inv h1
                    rw [hfFL] at hfv
                    simp only [Except.ok.injEq, Prod.mk.injEq] at hfv
                    obtain ⟨rfl, rfl⟩ := hfv
                    obtain ⟨fes, sb, hf1, h1⟩ := tBind_step_inv h1
                    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1
                    obtain ⟨rfl, rfl⟩ := h1
                    have hleA : TStateLe s0 { s0 with nextLocal := s0.nextLocal + fl.length } :=
                      ⟨Nat.le_add_right _ _, Nat.le_refl _, rfl, DemandLe.refl _⟩
                    obtain ⟨hleB, hclB⟩ := hfields fl k (hsub (k, fl) List.mem_cons_self)
                      _ _ sb fes (fun p hp => (List.of_mem_zip hp).1) hf1
                    obtain ⟨hleC, hclC⟩ := ihc sb sc at_
                      (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hf2
                    have hsp : ∀ vs : List String, isSimplePatList (vs.map .bind) = true := by
                      intro vs; induction vs with
                      | nil => rfl | cons _ _ ihv => simp [isSimplePatList, isSimplePat, ihv]
                    exact ⟨(hleA.trans hleB).trans hleC, fun hdatas => by
                      have hsp' := hsp ((List.range fl.length).map fun i => localName (s0.nextLocal + i))
                      rw [List.map_map] at hsp'
                      simp [isCleanNoU32Arms, isSimplePat, mk, isCleanNoU32,
                        hclB hdatas, hclC hdatas, hsp']⟩
              change (do let arms ← D.ctors.mapM (m := TLowerM) armFn; pure (matchE e arms))
                  { st with demand := { st.demand with needObj := true } } = .ok (res, st') at h0
              simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure] at h0
              cases hm : (D.ctors.mapM (m := TLowerM) armFn)
                  { st with demand := { st.demand with needObj := true } } with
              | error _ => rw [hm] at h0; cases h0
              | ok r1 =>
                rcases r1 with ⟨arms, s1⟩
                rw [hm] at h0
                simp only [Except.ok.injEq, Prod.mk.injEq] at h0
                obtain ⟨rfl, rfl⟩ := h0
                obtain ⟨hle1, hcl1⟩ := harms D.ctors _ s1 arms (fun _ hx => hx) hm
                exact ⟨hle0.trans hle1, fun hdatas he => by simp [matchE, isCleanNoU32, he, hcl1 hdatas]⟩
          have ⟨hle, hcl⟩ := go _ _ _ (freshLocals_poly _ (fun _ => rfl) (fun _ _ => rfl))
            (fun _ _ => rfl) (fun _ _ => rfl) h
          exact ⟨hle, fun _ _ hdatas he => hcl hdatas he⟩
        | irr | nat _ | w8 | w16 | w32 | w64 | «enum» _ | data _ =>
          exact coerceEAux_spec_zero cx (.data d) _ e st res st'
            (by unfold coerceEAux; simp only [heq, Bool.false_eq_true, ↓reduceIte]; exact h)
      | obj =>
        cases toR with
        | data d =>
          have go : ∀ (fFL : Nat → TLowerM (List String)) (fL : ∀ {α : Type}, Except String α → TLowerM α)
              (fM : (Demand → Demand) → TLowerM Unit),
              (∀ n s, fFL n s = .ok ((List.range n).map (fun i => localName (s.nextLocal + i)),
                { s with nextLocal := s.nextLocal + n })) →
              (∀ {α} (r : Except String α) s, fL r s = match r with | .ok a => .ok (a, s) | .error err => .error err) →
              (∀ u s, fM u s = .ok ((), { s with demand := u s.demand })) →
              (do fM fun d0 => { d0 with needObj := true }
                  let some D := cx.cert.data? d | fL (throw s!"coerce: unknown data {d}")
                  let arms ← D.ctors.mapM fun ((k, fl) : CtorKey × List Shape) => do
                    let some (idx, entry) := cx.ctorEntry? k | fL (throw "coerce obj→data: missing ctor")
                    let nm := ctorNameOf idx entry.key
                    let fvars ← fFL fl.length
                    let fieldExprs ← (fl.zip fvars).mapM fun ((sh, fv) : Shape × String) => do
                      let fr := cx.rep sh
                      let typed ← coerceEAux fuel' cx .obj fr (.load (vE fv))
                      return if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.store typed else typed
                    return (pC nm (fvars.map .bind),
                      Aiur.Generic.Expr.construct (dataName d) (some []) nm fieldExprs)
                  return matchE e arms) st = .ok (res, st') →
              TStateLe st st' ∧
              (datasNatCoreReps cx.P cx.cert cx.feat = true → isCleanNoU32 e = true →
                isCleanNoU32 res = true) := by
            intro fFL fL fM hfFL hfL hfM h0
            simp only [bind, StateT.bind, pure, Except.bind, hfM] at h0
            cases hD : cx.cert.data? d with
            | none => simp [hD, hfL, throw, throwThe, MonadExceptOf.throw] at h0
            | some D =>
              simp only [hD] at h0
              have hle0 : TStateLe st { st with demand := { st.demand with needObj := true } } :=
                ⟨Nat.le_refl _, Nat.le_refl _, rfl,
                  by constructor <;> first | exact id | (intro _; rfl)⟩
              have hfields : ∀ (fl : List Shape) (c : CtorKey), (c, fl) ∈ D.ctors →
                  ∀ (pairs : List (Shape × String)) (s0 s1 : TState) (es : List Lower.Expr),
                    (∀ p ∈ pairs, p.1 ∈ fl) →
                    (pairs.mapM (m := TLowerM) fun (sh, fv) => do
                      let fr := cx.rep sh
                      let typed ← coerceEAux fuel' cx .obj fr (.load (vE fv))
                      return if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .store typed else typed) s0 =
                      .ok (es, s1) →
                    TStateLe s0 s1 ∧ (datasNatCoreReps cx.P cx.cert cx.feat = true →
                      isCleanNoU32List es = true) := by
                intro fl c hc pairs
                induction pairs with
                | nil =>
                  intro s0 s1 es _ hm
                  simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
                    Except.ok.injEq, Prod.mk.injEq] at hm
                  obtain ⟨rfl, rfl⟩ := hm; exact ⟨TStateLe.refl _, fun _ => rfl⟩
                | cons p pt ihp =>
                  intro s0 s1 es hsub hm
                  rcases p with ⟨sh, fv⟩
                  rw [List.mapM_cons] at hm
                  obtain ⟨e1, sa, h1, hm⟩ := tBind_step_inv hm
                  obtain ⟨es', sb, h2, hm⟩ := tBind_step_inv hm
                  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm
                  obtain ⟨rfl, rfl⟩ := hm
                  obtain ⟨typed, sa', hco, h1⟩ := tBind_step_inv h1
                  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1
                  obtain ⟨rfl, rfl⟩ := h1
                  obtain ⟨hle1, hcl1⟩ := ih cx .obj (cx.rep sh) _ s0 typed sa' hco
                  obtain ⟨hle2, hcl2⟩ := ihp sa' sb es'
                    (fun q hq => hsub q (List.mem_cons_of_mem _ hq)) h2
                  refine ⟨hle1.trans hle2, fun hdatas => ?_⟩
                  have hcore := datasNatCoreReps_field hdatas hD hc (hsub (sh, fv) List.mem_cons_self)
                  have hty := hcl1 rfl hcore hdatas rfl
                  have hfld : isCleanNoU32
                      (if dataFieldNeedsPtr cx.P cx.cert cx.feat d (cx.rep sh)
                       then .store typed else typed) = true := by
                    split <;> simpa [isCleanNoU32] using hty
                  simp [isCleanNoU32List, hfld, hcl2 hdatas]
              have harms : ∀ (cs : List (CtorKey × List Shape)) (s0 s1 : TState)
                  (arms : List (Lower.Pat × Lower.Expr)),
                  (∀ x ∈ cs, x ∈ D.ctors) →
                  (cs.mapM (m := TLowerM) fun (k, fl) => do
                    let some (idx, entry) := cx.ctorEntry? k | fL (throw "coerce obj→data: missing ctor")
                    let nm := ctorNameOf idx entry.key
                    let fvars ← fFL fl.length
                    let fieldExprs ← (fl.zip fvars).mapM fun (sh, fv) => do
                      let fr := cx.rep sh
                      let typed ← coerceEAux fuel' cx .obj fr (.load (vE fv))
                      return if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .store typed else typed
                    return (pC nm (fvars.map .bind), .construct (dataName d) (some []) nm fieldExprs)) s0 =
                    .ok (arms, s1) →
                  TStateLe s0 s1 ∧ (datasNatCoreReps cx.P cx.cert cx.feat = true →
                    isCleanNoU32Arms arms = true) := by
                intro cs; induction cs with
                | nil =>
                  intro s0 s1 arms _ hm
                  simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
                    Except.ok.injEq, Prod.mk.injEq] at hm
                  obtain ⟨rfl, rfl⟩ := hm; exact ⟨TStateLe.refl _, fun _ => rfl⟩
                | cons cf ct ihc =>
                  intro s0 s1 arms hsub hm
                  rcases cf with ⟨k, fl⟩
                  rw [List.mapM_cons] at hm
                  obtain ⟨arm1, sA, h1, hm⟩ := tBind_step_inv hm
                  obtain ⟨at_, sc, hf2, hm⟩ := tBind_step_inv hm
                  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm
                  obtain ⟨rfl, rfl⟩ := hm
                  cases hce : cx.ctorEntry? k with
                  | none => simp [hce, hfL, throw, throwThe, MonadExceptOf.throw] at h1
                  | some ie =>
                    simp only [hce] at h1
                    obtain ⟨fvars, sa, hfv, h1⟩ := tBind_step_inv h1
                    rw [hfFL] at hfv
                    simp only [Except.ok.injEq, Prod.mk.injEq] at hfv
                    obtain ⟨rfl, rfl⟩ := hfv
                    obtain ⟨fes, sb, hf1, h1⟩ := tBind_step_inv h1
                    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1
                    obtain ⟨rfl, rfl⟩ := h1
                    have hleA : TStateLe s0 { s0 with nextLocal := s0.nextLocal + fl.length } :=
                      ⟨Nat.le_add_right _ _, Nat.le_refl _, rfl, DemandLe.refl _⟩
                    obtain ⟨hleB, hclB⟩ := hfields fl k (hsub (k, fl) List.mem_cons_self)
                      _ _ sb fes (fun p hp => (List.of_mem_zip hp).1) hf1
                    obtain ⟨hleC, hclC⟩ := ihc sb sc at_
                      (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hf2
                    have hsp : ∀ vs : List String, isSimplePatList (vs.map .bind) = true := by
                      intro vs; induction vs with
                      | nil => rfl | cons _ _ ihv => simp [isSimplePatList, isSimplePat, ihv]
                    exact ⟨(hleA.trans hleB).trans hleC, fun hdatas => by
                      have hsp' := hsp ((List.range fl.length).map fun i => localName (s0.nextLocal + i))
                      rw [List.map_map] at hsp'
                      simp [isCleanNoU32Arms, pC, isSimplePat, isCleanNoU32,
                        hclB hdatas, hclC hdatas, hsp']⟩
              let armFn : CtorKey × List Shape → TLowerM (Lower.Pat × Lower.Expr) :=
                fun (k, fl) => do
                  let some (idx, entry) := cx.ctorEntry? k | fL (throw "coerce obj→data: missing ctor")
                  let nm := ctorNameOf idx entry.key
                  let fvars ← fFL fl.length
                  let fieldExprs ← (fl.zip fvars).mapM fun ((sh, fv) : Shape × String) => do
                    let fr := cx.rep sh
                    let typed ← coerceEAux fuel' cx .obj fr (.load (vE fv))
                    return if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.store typed else typed
                  return (pC nm (fvars.map .bind),
                    Aiur.Generic.Expr.construct (dataName d) (some []) nm fieldExprs)
              change (do let arms ← D.ctors.mapM (m := TLowerM) armFn; pure (matchE e arms))
                  { st with demand := { st.demand with needObj := true } } = .ok (res, st') at h0
              simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure] at h0
              cases hm : (D.ctors.mapM (m := TLowerM) armFn)
                  { st with demand := { st.demand with needObj := true } } with
              | error _ => rw [hm] at h0; cases h0
              | ok r1 =>
                rcases r1 with ⟨arms, s1⟩
                rw [hm] at h0
                simp only [Except.ok.injEq, Prod.mk.injEq] at h0
                obtain ⟨rfl, rfl⟩ := h0
                obtain ⟨hle1, hcl1⟩ := harms D.ctors _ s1 arms (fun _ hx => hx) hm
                exact ⟨hle0.trans hle1, fun hdatas he => by simp [matchE, isCleanNoU32, he, hcl1 hdatas]⟩
          have ⟨hle, hcl⟩ := go _ _ _ (freshLocals_poly _ (fun _ => rfl) (fun _ _ => rfl))
            (fun _ _ => rfl) (fun _ _ => rfl) h
          exact ⟨hle, fun _ _ hdatas he => hcl hdatas he⟩
        | irr | nat _ | w8 | w16 | w32 | w64 | «enum» _ | obj =>
          exact coerceEAux_spec_zero cx .obj _ e st res st'
            (by unfold coerceEAux; simp only [heq, Bool.false_eq_true, ↓reduceIte]; exact h)
      | irr | nat _ | w8 | w16 | w32 | w64 | «enum» _ =>
        exact coerceEAux_spec_zero cx _ toR e st res st'
          (by unfold coerceEAux; simp only [heq, Bool.false_eq_true, ↓reduceIte]; cases toR <;> exact h)

theorem coerceE_spec {cx : TCx} {fromR toR : Rep} {e : Lower.Expr}
    {st st' : TState} {res : Lower.Expr}
    (h : coerceE cx fromR toR e st = .ok (res, st')) :
    TStateLe st st' ∧
    (isNatCoreRep fromR = true → isNatCoreRep toR = true →
      datasNatCoreReps cx.P cx.cert cx.feat = true →
      isCleanNoU32 e = true → isCleanNoU32 res = true) :=
  coerceEAux_spec _ cx fromR toR e st res st' h

private theorem mem_of_lookup_eq_some {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {k : α} {v : β}, l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by simp at h
  | (a, b) :: tl, k, v, h => by
    simp only [List.lookup_cons] at h
    by_cases hka : k = a
    · subst hka
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h; exact List.mem_cons_self
    · have hb : (k == a) = false := beq_false_of_ne hka
      simp only [hb] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup_eq_some h)

theorem tArgRaw_spec {cx : TCx} {vm : TVarMap} {a : Arg} {st st' : TState}
    {e : Lower.Expr} {r : Rep}
    (h : tArgRaw cx vm a st = .ok ((e, r), st')) :
    TStateLe st st' ∧ isCleanNoU32 e = true ∧
    ((∀ p ∈ vm, isNatCoreRep p.2.2 = true) → isNatCoreRep r = true) := by
  unfold tArgRaw at h
  have go : ∀ (fL : ∀ {α : Type}, Except String α → TLowerM α)
      (fM : (Demand → Demand) → TLowerM Unit),
      (∀ {α} (r : Except String α) s, fL r s = match r with | .ok a => .ok (a, s) | .error err => .error err) →
      (∀ u s, fM u s = .ok ((), { s with demand := u s.demand })) →
      (match a with
       | .var x => match vm.lookup x with
         | some (nx, r) => pure (vE nx, r)
         | none => fL (throw s!"unbound variable {x}")
       | .lit (.nat n) => if n < natLimit then pure (litE n, .nat (n + 1)) else fL (throw s!"literal {n} ≥ 2^56")
       | .lit (.str s) => do fM fun d => { d with needObj := true, needBytes := true }; return (strE s, .obj)
       | .erased => pure (.tuple [], .irr)) st = .ok ((e, r), st') →
      TStateLe st st' ∧ isCleanNoU32 e = true ∧
      ((∀ p ∈ vm, isNatCoreRep p.2.2 = true) → isNatCoreRep r = true) := by
    intro fL fM hfL hfM h0
    cases a with
    | var x =>
      cases hl : vm.lookup x with
      | none => simp [hl, hfL, throw, throwThe, MonadExceptOf.throw] at h0
      | some nr =>
        rcases nr with ⟨nx, rx⟩
        simp only [hl, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h0
        refine ⟨TStateLe.refl _, rfl, fun hvm => ?_⟩
        exact hvm (x, nx, rx) (mem_of_lookup_eq_some hl)
    | lit l =>
      cases l with
      | nat n =>
        by_cases hn : n < natLimit
        · simp only [hn, ↓reduceIte, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h0
          exact ⟨TStateLe.refl _, rfl, fun _ => rfl⟩
        · simp [hn, hfL, throw, throwThe, MonadExceptOf.throw] at h0
      | str s =>
        simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, hfM,
          Except.ok.injEq, Prod.mk.injEq] at h0
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h0
        refine ⟨⟨Nat.le_refl _, Nat.le_refl _, rfl,
          by constructor <;> first | exact id | (intro _; rfl)⟩,
          isCleanNoU32_strE s, fun _ => rfl⟩
    | erased =>
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h0
      exact ⟨TStateLe.refl _, rfl, fun _ => rfl⟩
  exact go _ _ (fun _ _ => rfl) (fun _ _ => rfl) h

theorem tArgE_spec {cx : TCx} {vm : TVarMap} {a : Arg} {target : Rep}
    {st st' : TState} {e : Lower.Expr}
    (h : tArgE cx vm a target st = .ok (e, st')) :
    TStateLe st st' ∧
    ((∀ p ∈ vm, isNatCoreRep p.2.2 = true) → isNatCoreRep target = true →
      datasNatCoreReps cx.P cx.cert cx.feat = true → isCleanNoU32 e = true) := by
  unfold tArgE at h
  simp only [bind, StateT.bind, Except.bind] at h
  cases hr : tArgRaw cx vm a st with
  | error _ => simp [hr] at h
  | ok r1 =>
    rcases r1 with ⟨⟨ea, ra⟩, st1⟩
    simp only [hr] at h
    obtain ⟨hle1, hcl1, hcore1⟩ := tArgRaw_spec hr
    obtain ⟨hle2, hcl2⟩ := coerceE_spec h
    exact ⟨hle1.trans hle2, fun hvm ht hdatas => hcl2 (hcore1 hvm) ht hdatas hcl1⟩

private def TLowerLe {α : Type} (m : TLowerM α) : Prop :=
  ∀ st a st', m st = .ok (a, st') → TStateLe st st'

private theorem TLowerLe.pure_le {α : Type} (a : α) : TLowerLe (pure a) := by
  intro st b st' h
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h; exact TStateLe.refl _

private theorem TLowerLe.bind_le {α β : Type} {m : TLowerM α} {f : α → TLowerM β}
    (hm : TLowerLe m) (hf : ∀ a, TLowerLe (f a)) : TLowerLe (m >>= f) := by
  intro st b st' h
  simp only [bind, StateT.bind, Except.bind] at h
  cases h1 : m st with
  | error _ => simp [h1] at h
  | ok r1 =>
    rcases r1 with ⟨a, st1⟩
    simp only [h1] at h
    exact (hm st a st1 h1).trans (hf a st1 b st' h)

private theorem TLowerLe.fresh_eq {m : TLowerM String}
    (heq : ∀ s, m s = .ok (localName s.nextLocal, { s with nextLocal := s.nextLocal + 1 })) :
    TLowerLe m := by
  intro st a st' h; rw [heq] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  exact ⟨Nat.le_succ _, Nat.le_refl _, rfl, DemandLe.refl _⟩

private theorem TLowerLe.mark_fn {fM : (Demand → Demand) → TLowerM Unit}
    (heq : ∀ u s, fM u s = .ok ((), { s with demand := u s.demand }))
    {u : Demand → Demand} (hu : ∀ d, DemandLe d (u d)) : TLowerLe (fM u) := by
  intro st a st' h; rw [heq] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, hu st.demand⟩

private theorem TLowerLe.lift_throw {α : Type} {fL : Except String α → TLowerM α}
    (heq : ∀ r s, fL r s = match r with | .ok a => .ok (a, s) | .error e => .error e)
    {msg : String} : TLowerLe (fL (throw msg)) := by
  intro st a st' h
  rw [heq] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

private theorem TLowerLe.tArgE_le (cx : TCx) (vm : TVarMap) (a : Arg) (r : Rep) :
    TLowerLe (tArgE cx vm a r) := fun _ _ _ h => (tArgE_spec h).1

private theorem TLowerLe.coerceE_le (cx : TCx) (r1 r2 : Rep) (e : Lower.Expr) :
    TLowerLe (coerceE cx r1 r2 e) := fun _ _ _ h => (coerceE_spec h).1

private theorem tPrimE_word_le (cx : TCx) (vm : TVarMap) (w : Src.Width) (wop : Src.WordOp)
    (as : List Arg) (target : Rep) : TLowerLe (tPrimE cx vm (.word w wop) as target) := by
  unfold tPrimE
  cases w with
  | w32 =>
    dsimp only
    cases wop <;> rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> try dsimp only
    all_goals
      repeat any_goals first
        | apply TLowerLe.tArgE_le
        | apply TLowerLe.coerceE_le
        | apply TLowerLe.pure_le
        | (apply TLowerLe.fresh_eq; intro _; rfl)
        | (apply TLowerLe.mark_fn <;> [ (intro _ _; rfl); (intro _; constructor <;> first | exact id | (intro _; rfl)) ])
        | (apply TLowerLe.lift_throw; intro _ _; rfl)
        | (refine TLowerLe.bind_le ?_ (fun _ => ?_))
        | (cases ‹Src.Width›; try dsimp only)
  | w64 =>
    dsimp only
    apply TLowerLe.bind_le
    · apply TLowerLe.mark_fn
      · intro _ _; rfl
      · intro _; constructor <;> first | exact id | (intro _; rfl)
    · intro _
      cases wop <;> rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> try dsimp only
      all_goals
        repeat any_goals first
          | apply TLowerLe.tArgE_le
          | apply TLowerLe.coerceE_le
          | apply TLowerLe.pure_le
          | (apply TLowerLe.fresh_eq; intro _; rfl)
          | (apply TLowerLe.mark_fn <;> [ (intro _ _; rfl); (intro _; constructor <;> first | exact id | (intro _; rfl)) ])
          | (apply TLowerLe.lift_throw; intro _ _; rfl)
          | (refine TLowerLe.bind_le ?_ (fun _ => ?_))
          | (cases ‹Src.Width›; try dsimp only)
      all_goals
        (cases b with
         | var _ | erased =>
           try dsimp only
           repeat any_goals first
             | apply TLowerLe.tArgE_le
             | apply TLowerLe.coerceE_le
             | apply TLowerLe.pure_le
             | (apply TLowerLe.mark_fn <;> [ (intro _ _; rfl); (intro _; constructor <;> first | exact id | (intro _; rfl)) ])
             | (refine TLowerLe.bind_le ?_ (fun _ => ?_))
         | lit l =>
           cases l with
           | str _ =>
             try dsimp only
             repeat any_goals first
               | apply TLowerLe.tArgE_le
               | apply TLowerLe.coerceE_le
               | apply TLowerLe.pure_le
               | (apply TLowerLe.mark_fn <;> [ (intro _ _; rfl); (intro _; constructor <;> first | exact id | (intro _; rfl)) ])
               | (refine TLowerLe.bind_le ?_ (fun _ => ?_))
           | nat n =>
             split
             · repeat any_goals first
                 | apply TLowerLe.tArgE_le
                 | apply TLowerLe.coerceE_le
                 | apply TLowerLe.pure_le
                 | (apply TLowerLe.fresh_eq; intro _; rfl)
                 | (refine TLowerLe.bind_le ?_ (fun _ => ?_))
             · repeat any_goals first
                 | apply TLowerLe.tArgE_le
                 | apply TLowerLe.coerceE_le
                 | apply TLowerLe.pure_le
                 | (apply TLowerLe.mark_fn <;> [ (intro _ _; rfl); (intro _; constructor <;> first | exact id | (intro _; rfl)) ])
                 | (refine TLowerLe.bind_le ?_ (fun _ => ?_)))
  | w8 =>
    dsimp only
    cases wop <;> rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> try dsimp only
    all_goals
      repeat any_goals first
        | apply TLowerLe.tArgE_le
        | apply TLowerLe.coerceE_le
        | apply TLowerLe.pure_le
        | (apply TLowerLe.mark_fn <;> [ (intro _ _; rfl); (intro _; constructor <;> first | exact id | (intro _; rfl)) ])
        | (apply TLowerLe.lift_throw; intro _ _; rfl)
        | (refine TLowerLe.bind_le ?_ (fun _ => ?_))
        | (cases ‹Src.Width›; try dsimp only)
  | w16 =>
    dsimp only
    cases wop <;> rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> try dsimp only
    all_goals
      repeat any_goals first
        | apply TLowerLe.tArgE_le
        | apply TLowerLe.coerceE_le
        | apply TLowerLe.pure_le
        | (apply TLowerLe.mark_fn <;> [ (intro _ _; rfl); (intro _; constructor <;> first | exact id | (intro _; rfl)) ])
        | (apply TLowerLe.lift_throw; intro _ _; rfl)
        | (refine TLowerLe.bind_le ?_ (fun _ => ?_))
        | (cases ‹Src.Width›; try dsimp only)

private theorem tMark_step_inv {fM : (Demand → Demand) → TLowerM Unit} {u : Demand → Demand}
    {α : Type} {f : Unit → TLowerM α} {st st' : TState} {a : α}
    (h : (fM u >>= f) st = .ok (a, st'))
    (heq : ∀ u s, fM u s = .ok ((), { s with demand := u s.demand }))
    (hu : ∀ d, DemandLe d (u d)) :
    ∃ s1, TStateLe st s1 ∧ s1 = { st with demand := u st.demand } ∧ f () s1 = .ok (a, st') := by
  simp only [bind, StateT.bind, Except.bind, heq] at h
  exact ⟨{ st with demand := u st.demand },
    ⟨Nat.le_refl _, Nat.le_refl _, rfl, hu st.demand⟩, rfl, h⟩

private theorem tFreshLocal_step_inv {m : TLowerM String}
    {α : Type} {f : String → TLowerM α} {st st' : TState} {a : α}
    (h : (m >>= f) st = .ok (a, st'))
    (heq : ∀ s, m s = .ok (localName s.nextLocal, { s with nextLocal := s.nextLocal + 1 })) :
    TStateLe st { st with nextLocal := st.nextLocal + 1 } ∧
    f (localName st.nextLocal) { st with nextLocal := st.nextLocal + 1 } = .ok (a, st') := by
  simp only [bind, StateT.bind, Except.bind, heq] at h
  exact ⟨⟨Nat.le_succ _, Nat.le_refl _, rfl, DemandLe.refl _⟩, h⟩

private theorem tLift_throw_elim {α : Type} {fL : Except String α → TLowerM α}
    {msg : String} {st st' : TState} {a : α}
    (h : fL (throw msg) st = .ok (a, st'))
    (heq : ∀ r s, fL r s = match r with | .ok a => .ok (a, s) | .error e => .error e) : False := by
  rw [heq] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

theorem tPrimE_spec {cx : TCx} {vm : TVarMap} {op : Prim} {as : List Arg} {target : Rep}
    {st st' : TState} {e : Lower.Expr}
    (h : tPrimE cx vm op as target st = .ok (e, st')) :
    TStateLe st st' ∧
    (op.isWord = false → (∀ p ∈ vm, isNatCoreRep p.2.2 = true) →
      isNatCoreRep target = true → datasNatCoreReps cx.P cx.cert cx.feat = true →
      isCleanNoU32 e = true) := by
  have hwrap : ∀ {fW : TCx → Lower.Expr → Rep → TLowerM Lower.Expr}
      {cx' : TCx} {ce : Lower.Expr} {tgt : Rep} {s0 s1 : TState} {res : Lower.Expr},
      fW cx' ce tgt s0 = .ok (res, s1) →
      ∀ {fL : {α : Type} → Except String α → TLowerM α}
        {fM : (Demand → Demand) → TLowerM Unit},
      (∀ cx' ce tgt, fW cx' ce tgt =
        match tgt with
        | .enum ind =>
          match cx'.boolEnum? with
          | some (bind, tt, ff) =>
            if bind == ind then
              pure (matchE ce [(.literal 0, .construct (enumName ind) (some []) ff []),
                               (.wildcard, .construct (enumName ind) (some []) tt [])])
            else fL (throw "wrapBool: enum mismatch")
          | none => fL (throw "wrapBool: Bool enum missing")
        | .obj => do
          fM fun d => { d with needObj := true }
          let some (tt, ff) := (Lower.Cx.mk cx'.P).boolNames
            | fL (throw "wrapBool: Bool pins missing")
          pure (matchE ce [(.literal 0, mk ff []), (.wildcard, mk tt [])])
        | _ => fL (throw s!"wrapBool: unexpected target rep {reprStr tgt}")) →
      (∀ {α : Type} (x : Except String α) s, fL x s = match x with | .ok a => .ok (a, s) | .error e => .error e) →
      (∀ u s, fM u s = .ok ((), { s with demand := u s.demand })) →
      TStateLe s0 s1 ∧ (isCleanNoU32 ce = true → isCleanNoU32 res = true) := by
    intro fW cx' ce tgt s0 s1 res hw fL fM hW hfL hfM
    rw [hW] at hw
    cases tgt with
    | «enum» ind =>
      cases hb : cx'.boolEnum? with
      | none => simp [hb, hfL, throw, throwThe, MonadExceptOf.throw] at hw
      | some b =>
        rcases b with ⟨bind, tt, ff⟩
        simp only [hb] at hw
        split at hw
        · simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          exact ⟨TStateLe.refl _, fun hce => by
            simp [matchE, isCleanNoU32, isCleanNoU32Arms, isSimplePat, isCleanNoU32List, hce]⟩
        · simp [hfL, throw, throwThe, MonadExceptOf.throw] at hw
    | obj =>
      simp only [bind, StateT.bind, Except.bind, hfM] at hw
      cases hb : (Lower.Cx.mk cx'.P).boolNames with
      | none => simp [hb, hfL, throw, throwThe, MonadExceptOf.throw] at hw
      | some tf =>
        rcases tf with ⟨tt, ff⟩
        simp only [hb, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        refine ⟨⟨Nat.le_refl _, Nat.le_refl _, rfl,
          by constructor <;> first | exact id | (intro _; rfl)⟩, fun hce => ?_⟩
        simp [matchE, mk, isCleanNoU32, isCleanNoU32Arms, isSimplePat, isCleanNoU32List, hce]
    | irr | nat _ | w8 | w16 | w32 | w64 | data _ =>
      simp [hfL, throw, throwThe, MonadExceptOf.throw] at hw
  cases op with
  | word w wop =>
    exact ⟨tPrimE_word_le cx vm w wop as target st e st' h, fun hnw => by simp [Lam.Prim.isWord] at hnw⟩
  | natPred =>
    unfold tPrimE at h
    rcases as with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> dsimp only at h
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · obtain ⟨⟨ea, ra⟩, st1, h1, h⟩ := tBind_step_inv h
      obtain ⟨xf, st2, h2, h⟩ := tBind_step_inv h
      obtain ⟨hle3, h⟩ := tFreshLocal_step_inv h (fun _ => rfl)
      obtain ⟨hle1, hcl1, hcore1⟩ := tArgRaw_spec h1
      obtain ⟨hle2, hcl2⟩ := coerceE_spec h2
      obtain ⟨hle4, hcl4⟩ := coerceE_spec h
      refine ⟨((hle1.trans hle2).trans hle3).trans hle4, fun _ hvm ht hdatas => ?_⟩
      have hxf := hcl2 (hcore1 hvm) rfl hdatas hcl1
      apply hcl4 rfl ht hdatas
      simp [letE, matchE, subE, vE, litE, isCleanNoU32, isCleanNoU32Arms, isSimplePat, hxf]
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
  | natAdd =>
    unfold tPrimE at h
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at h
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · obtain ⟨⟨ea, ra⟩, st1, h1, h⟩ := tBind_step_inv h
      obtain ⟨⟨eb, rb⟩, st2, h2, h⟩ := tBind_step_inv h
      obtain ⟨xa, st3, h3, h⟩ := tBind_step_inv h
      obtain ⟨xb, st4, h4, h⟩ := tBind_step_inv h
      obtain ⟨hle1, hcl1, hcore1⟩ := tArgRaw_spec h1
      obtain ⟨hle2, hcl2, hcore2⟩ := tArgRaw_spec h2
      obtain ⟨hle3, hcl3⟩ := coerceE_spec h3
      obtain ⟨hle4, hcl4⟩ := coerceE_spec h4
      by_cases hfast : (ra.isFieldNat && rb.isFieldNat && ra.fieldBound + rb.fieldBound ≤ natLimit) = true
      · simp only [hfast, ↓reduceIte] at h
        obtain ⟨hle5, hcl5⟩ := coerceE_spec h
        refine ⟨(((hle1.trans hle2).trans hle3).trans hle4).trans hle5, fun _ hvm ht hdatas => ?_⟩
        have hxa := hcl3 (hcore1 hvm) rfl hdatas hcl1
        have hxb := hcl4 (hcore2 hvm) rfl hdatas hcl2
        exact hcl5 rfl ht hdatas (by simp [addE, isCleanNoU32, hxa, hxb])
      · simp only [hfast, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨s5, hle5, _, h⟩ := tMark_step_inv h (fun _ _ => rfl)
          (fun _ => by constructor <;> first | exact id | (intro _; rfl))
        obtain ⟨hle6, h⟩ := tFreshLocal_step_inv h (fun _ => rfl)
        obtain ⟨hle7, hcl7⟩ := coerceE_spec h
        refine ⟨(((((hle1.trans hle2).trans hle3).trans hle4).trans hle5).trans hle6).trans hle7,
          fun _ hvm ht hdatas => ?_⟩
        have hxa := hcl3 (hcore1 hvm) rfl hdatas hcl1
        have hxb := hcl4 (hcore2 hvm) rfl hdatas hcl2
        apply hcl7 rfl ht hdatas
        simp [letE, seqE, addE, callE, vE, isCleanNoU32, isCleanNoU32List, isSimplePat,
          isPeepholeU32Name, hxa, hxb]
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
  | natSub =>
    unfold tPrimE at h
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at h
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · obtain ⟨⟨ea, ra⟩, st1, h1, h⟩ := tBind_step_inv h
      obtain ⟨xa, st2, h2, h⟩ := tBind_step_inv h
      obtain ⟨hle1, hcl1, hcore1⟩ := tArgRaw_spec h1
      obtain ⟨hle2, hcl2⟩ := coerceE_spec h2
      have hFallback : ∀ (fM : (Demand → Demand) → TLowerM Unit),
          (∀ u s, fM u s = .ok ((), { s with demand := u s.demand })) →
          (do let (eb, rb) ← tArgRaw cx vm b
              let xb ← coerceE cx rb (.nat natLimit) eb
              fM fun d => { d with needSubBorrow56 := true }
              coerceE cx (.nat ra.fieldBound) target (.project (callE "sub_borrow_56" [xa, xb]) 0)) st2 =
            .ok (e, st') →
          TStateLe st2 st' ∧
          ((∀ p ∈ vm, isNatCoreRep p.2.2 = true) → isNatCoreRep target = true →
            datasNatCoreReps cx.P cx.cert cx.feat = true → isCleanNoU32 xa = true →
            isCleanNoU32 e = true) := by
        intro fM hfM h0
        obtain ⟨⟨eb, rb⟩, st3, h3, h0⟩ := tBind_step_inv h0
        obtain ⟨xb, st4, h4, h0⟩ := tBind_step_inv h0
        obtain ⟨s5, hle5, _, h0⟩ := tMark_step_inv h0 hfM
          (fun _ => by constructor <;> first | exact id | (intro _; rfl))
        obtain ⟨hle3, hcl3, hcore3⟩ := tArgRaw_spec h3
        obtain ⟨hle4, hcl4⟩ := coerceE_spec h4
        obtain ⟨hle6, hcl6⟩ := coerceE_spec h0
        refine ⟨((hle3.trans hle4).trans hle5).trans hle6, fun hvm ht hdatas hxa => ?_⟩
        have hxb := hcl4 (hcore3 hvm) rfl hdatas hcl3
        apply hcl6 rfl ht hdatas
        simp [callE, isCleanNoU32, isCleanNoU32List, isPeepholeU32Name, hxa, hxb]
      cases b with
      | lit l =>
        cases l with
        | nat k =>
          cases k with
          | zero =>
            obtain ⟨hle3, hcl3⟩ := coerceE_spec h
            exact ⟨(hle1.trans hle2).trans hle3, fun _ hvm ht hdatas =>
              hcl3 rfl ht hdatas (hcl2 (hcore1 hvm) rfl hdatas hcl1)⟩
          | succ k' =>
            by_cases hk : k' + 1 ≤ 4
            · simp only [hk, ↓reduceIte] at h
              obtain ⟨hle3, h⟩ := tFreshLocal_step_inv h (fun _ => rfl)
              obtain ⟨hle4, hcl4⟩ := coerceE_spec h
              have hcs : ∀ (fC : Lower.Expr → Nat → Lower.Expr),
                  (∀ x n, fC x n = constSubMatchE x n) →
                  isCleanNoU32 (fC (vE (localName st2.nextLocal)) (k' + 1)) = true := by
                intro fC hfC; rw [hfC]; exact isCleanNoU32_constSubMatchE rfl _
              refine ⟨((hle1.trans hle2).trans hle3).trans hle4, fun _ hvm ht hdatas => ?_⟩
              have hxa := hcl2 (hcore1 hvm) rfl hdatas hcl1
              apply hcl4 rfl ht hdatas
              exact isCleanNoU32_letE hxa (hcs _ (fun _ _ => rfl))
            · simp only [hk, ↓reduceIte] at h
              obtain ⟨hle3, hcl3⟩ := hFallback _ (fun _ _ => rfl) h
              exact ⟨(hle1.trans hle2).trans hle3, fun _ hvm ht hdatas =>
                hcl3 hvm ht hdatas (hcl2 (hcore1 hvm) rfl hdatas hcl1)⟩
        | str s =>
          obtain ⟨hle3, hcl3⟩ := hFallback _ (fun _ _ => rfl) h
          exact ⟨(hle1.trans hle2).trans hle3, fun _ hvm ht hdatas =>
            hcl3 hvm ht hdatas (hcl2 (hcore1 hvm) rfl hdatas hcl1)⟩
      | var _ | erased =>
        obtain ⟨hle3, hcl3⟩ := hFallback _ (fun _ _ => rfl) h
        exact ⟨(hle1.trans hle2).trans hle3, fun _ hvm ht hdatas =>
          hcl3 hvm ht hdatas (hcl2 (hcore1 hvm) rfl hdatas hcl1)⟩
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
  | natMul =>
    unfold tPrimE at h
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at h
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · obtain ⟨⟨ea, ra⟩, st1, h1, h⟩ := tBind_step_inv h
      obtain ⟨⟨eb, rb⟩, st2, h2, h⟩ := tBind_step_inv h
      obtain ⟨xa, st3, h3, h⟩ := tBind_step_inv h
      obtain ⟨xb, st4, h4, h⟩ := tBind_step_inv h
      obtain ⟨hle1, hcl1, hcore1⟩ := tArgRaw_spec h1
      obtain ⟨hle2, hcl2, hcore2⟩ := tArgRaw_spec h2
      obtain ⟨hle3, hcl3⟩ := coerceE_spec h3
      obtain ⟨hle4, hcl4⟩ := coerceE_spec h4
      by_cases hfast : (ra.isFieldNat && rb.isFieldNat && ra.fieldBound * rb.fieldBound ≤ natLimit) = true
      · simp only [hfast, ↓reduceIte] at h
        obtain ⟨hle5, hcl5⟩ := coerceE_spec h
        refine ⟨(((hle1.trans hle2).trans hle3).trans hle4).trans hle5, fun _ hvm ht hdatas => ?_⟩
        have hxa := hcl3 (hcore1 hvm) rfl hdatas hcl1
        have hxb := hcl4 (hcore2 hvm) rfl hdatas hcl2
        exact hcl5 rfl ht hdatas (by simp [mulE, isCleanNoU32, hxa, hxb])
      · simp only [hfast, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨s5, hle5, _, h⟩ := tMark_step_inv h (fun _ _ => rfl)
          (fun _ => by constructor <;> first | exact id | (intro _; rfl))
        obtain ⟨hle6, hcl6⟩ := coerceE_spec h
        refine ⟨((((hle1.trans hle2).trans hle3).trans hle4).trans hle5).trans hle6,
          fun _ hvm ht hdatas => ?_⟩
        have hxa := hcl3 (hcore1 hvm) rfl hdatas hcl1
        have hxb := hcl4 (hcore2 hvm) rfl hdatas hcl2
        apply hcl6 rfl ht hdatas
        simp [callE, isCleanNoU32, isCleanNoU32List, isPeepholeU32Name, hxa, hxb]
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
  | natDiv =>
    unfold tPrimE at h
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at h
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · obtain ⟨xa, st1, h1, h⟩ := tBind_step_inv h
      obtain ⟨xb, st2, h2, h⟩ := tBind_step_inv h
      obtain ⟨s3, hle3, _, h⟩ := tMark_step_inv h (fun _ _ => rfl)
        (fun _ => by constructor <;> first | exact id | (intro _; rfl))
      obtain ⟨hle4, h⟩ := tFreshLocal_step_inv h (fun _ => rfl)
      obtain ⟨hle5, h⟩ := tFreshLocal_step_inv h (fun _ => rfl)
      obtain ⟨hle1, hcl1⟩ := tArgE_spec h1
      obtain ⟨hle2, hcl2⟩ := tArgE_spec h2
      obtain ⟨hle6, hcl6⟩ := coerceE_spec h
      refine ⟨((((hle1.trans hle2).trans hle3).trans hle4).trans hle5).trans hle6,
        fun _ hvm ht hdatas => ?_⟩
      have hxa := hcl1 hvm rfl hdatas
      have hxb := hcl2 hvm rfl hdatas
      apply hcl6 rfl ht hdatas
      simp [letE, matchE, callE, vE, litE, isCleanNoU32, isCleanNoU32List, isCleanNoU32Arms,
        isSimplePat, isPeepholeU32Name, hxa, hxb]
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
  | natMod =>
    unfold tPrimE at h
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at h
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · obtain ⟨xa, st1, h1, h⟩ := tBind_step_inv h
      obtain ⟨xb, st2, h2, h⟩ := tBind_step_inv h
      obtain ⟨s3, hle3, _, h⟩ := tMark_step_inv h (fun _ _ => rfl)
        (fun _ => by constructor <;> first | exact id | (intro _; rfl))
      obtain ⟨hle4, h⟩ := tFreshLocal_step_inv h (fun _ => rfl)
      obtain ⟨hle5, h⟩ := tFreshLocal_step_inv h (fun _ => rfl)
      obtain ⟨hle1, hcl1⟩ := tArgE_spec h1
      obtain ⟨hle2, hcl2⟩ := tArgE_spec h2
      obtain ⟨hle6, hcl6⟩ := coerceE_spec h
      refine ⟨((((hle1.trans hle2).trans hle3).trans hle4).trans hle5).trans hle6,
        fun _ hvm ht hdatas => ?_⟩
      have hxa := hcl1 hvm rfl hdatas
      have hxb := hcl2 hvm rfl hdatas
      apply hcl6 rfl ht hdatas
      simp [letE, matchE, callE, vE, isCleanNoU32, isCleanNoU32List, isCleanNoU32Arms,
        isSimplePat, isPeepholeU32Name, hxa, hxb]
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
  | natPow | natGcd | natShl | natShr =>
    unfold tPrimE at h
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at h
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · obtain ⟨xa, st1, h1, h⟩ := tBind_step_inv h
      obtain ⟨xb, st2, h2, h⟩ := tBind_step_inv h
      obtain ⟨s3, hle3, _, h⟩ := tMark_step_inv h (fun _ _ => rfl)
        (fun _ => by constructor <;> first | exact id | (intro _; rfl))
      obtain ⟨hle1, hcl1⟩ := tArgE_spec h1
      obtain ⟨hle2, hcl2⟩ := tArgE_spec h2
      obtain ⟨hle4, hcl4⟩ := coerceE_spec h
      refine ⟨((hle1.trans hle2).trans hle3).trans hle4, fun _ hvm ht hdatas => ?_⟩
      have hxa := hcl1 hvm rfl hdatas
      have hxb := hcl2 hvm rfl hdatas
      apply hcl4 rfl ht hdatas
      simp [callE, isCleanNoU32, isCleanNoU32List, isPeepholeU32Name, hxa, hxb]
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
  | natBeq =>
    unfold tPrimE at h
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at h
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · obtain ⟨xa, st1, h1, h⟩ := tBind_step_inv h
      obtain ⟨xb, st2, h2, h⟩ := tBind_step_inv h
      obtain ⟨hle1, hcl1⟩ := tArgE_spec h1
      obtain ⟨hle2, hcl2⟩ := tArgE_spec h2
      obtain ⟨hle3, hcl3⟩ := hwrap h (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      refine ⟨(hle1.trans hle2).trans hle3, fun _ hvm _ hdatas => ?_⟩
      have hxa := hcl1 hvm rfl hdatas
      have hxb := hcl2 hvm rfl hdatas
      apply hcl3
      simp [matchE, subE, litE, isCleanNoU32, isCleanNoU32Arms, isSimplePat, hxa, hxb]
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
  | natBle =>
    unfold tPrimE at h
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at h
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · obtain ⟨xa, st1, h1, h⟩ := tBind_step_inv h
      obtain ⟨xb, st2, h2, h⟩ := tBind_step_inv h
      obtain ⟨s3, hle3, _, h⟩ := tMark_step_inv h (fun _ _ => rfl)
        (fun _ => by constructor <;> first | exact id | (intro _; rfl))
      obtain ⟨hle1, hcl1⟩ := tArgE_spec h1
      obtain ⟨hle2, hcl2⟩ := tArgE_spec h2
      obtain ⟨hle4, hcl4⟩ := hwrap h (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      refine ⟨((hle1.trans hle2).trans hle3).trans hle4, fun _ hvm _ hdatas => ?_⟩
      have hxa := hcl1 hvm rfl hdatas
      have hxb := hcl2 hvm rfl hdatas
      apply hcl4
      simp [callE, isCleanNoU32, isCleanNoU32List, isPeepholeU32Name, hxa, hxb]
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
  | natBlt =>
    unfold tPrimE at h
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at h
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · obtain ⟨xa, st1, h1, h⟩ := tBind_step_inv h
      obtain ⟨xb, st2, h2, h⟩ := tBind_step_inv h
      obtain ⟨s3, hle3, _, h⟩ := tMark_step_inv h (fun _ _ => rfl)
        (fun _ => by constructor <;> first | exact id | (intro _; rfl))
      obtain ⟨hle1, hcl1⟩ := tArgE_spec h1
      obtain ⟨hle2, hcl2⟩ := tArgE_spec h2
      obtain ⟨hle4, hcl4⟩ := hwrap h (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      refine ⟨((hle1.trans hle2).trans hle3).trans hle4, fun _ hvm _ hdatas => ?_⟩
      have hxa := hcl1 hvm rfl hdatas
      have hxb := hcl2 hvm rfl hdatas
      apply hcl4
      simp [subE, callE, litE, isCleanNoU32, isCleanNoU32List, isPeepholeU32Name, hxa, hxb]
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
  | natLand | natLor | natXor =>
    unfold tPrimE at h
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at h
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    · obtain ⟨xa, st1, h1, h⟩ := tBind_step_inv h
      obtain ⟨xb, st2, h2, h⟩ := tBind_step_inv h
      obtain ⟨s3, hle3, _, h⟩ := tMark_step_inv h (fun _ _ => rfl)
        (fun _ => by constructor <;> first | exact id | (intro _; rfl))
      obtain ⟨hle1, hcl1⟩ := tArgE_spec h1
      obtain ⟨hle2, hcl2⟩ := tArgE_spec h2
      obtain ⟨hle4, hcl4⟩ := coerceE_spec h
      refine ⟨((hle1.trans hle2).trans hle3).trans hle4, fun _ hvm ht hdatas => ?_⟩
      have hxa := hcl1 hvm rfl hdatas
      have hxb := hcl2 hvm rfl hdatas
      apply hcl4 rfl ht hdatas
      simp [callE, wordE, isCleanNoU32, isCleanNoU32List, isPeepholeU32Name, hxa, hxb]
    · exact False.elim (tLift_throw_elim h (fun _ _ => rfl))

/-! ### `tTrapE`, `stepDownNat`, `tRhsE`, `tCaseE`, `tCodeE`, `tFunE`, `tEntryE` Specs -/

private theorem tTrapE_ok_inv
    {fTrap : TCx → Rep → String → TLowerM Lower.Expr}
    {cx : TCx} {r : Rep} {msg : String} {st st' : TState} {e : Lower.Expr}
    (h : fTrap cx r msg st = .ok (e, st'))
    {fDummy : Nat → TCx → Rep → TLowerM Lower.Expr}
    {fL : {α : Type} → Except String α → TLowerM α}
    {fM : (Demand → Demand) → TLowerM Unit}
    (hTrap : ∀ cx r msg, fTrap cx r msg =
      (fDummy (cx.cert.datas.length + 2) cx r >>= fun dv =>
        pure (seqE (.builtin (.assertEq (assertion msg)) [litE 0, litE 1]) dv)))
    (hDef : ∀ fuel cx r, fDummy fuel cx r =
      match r with
      | .irr => pure (.tuple [])
      | .nat _ | .w8 | .w16 => pure (litE 0)
      | .w32 => pure (callE "UInt32::from_field" [litE 0])
      | .w64 => do fM fun d => { d with needU64Bitwise := true }; pure (callE "UInt64::from_field" [litE 0])
      | .enum ind => do
        let some (k :: _) := cx.cert.enum? ind | fL (throw s!"dummy: empty enum {ind}")
        let some (idx, e) := cx.ctorEntry? k | fL (throw "dummy: missing enum ctor")
        pure (.construct (enumName ind) (some []) (ctorNameOf idx e.key) [])
      | .data d =>
        match fuel with
        | 0 => fL (throw s!"dummy: data {d} exceeded depth")
        | fuel' + 1 => do
          let some D := cx.cert.data? d | fL (throw s!"dummy: missing data {d}")
          let some (k, fl) := D.ctors.find? (fun (_, fl) => fl.all fun s => cx.rep s != .data d)
            | fL (throw s!"dummy: data {d} has no base constructor")
          let some (idx, e) := cx.ctorEntry? k | fL (throw "dummy: missing data ctor")
          let args ← fl.mapM fun s => do
            let fr := cx.rep s
            let dv ← fDummy fuel' cx fr
            pure (if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.store dv else dv)
          pure (.construct (dataName d) (some []) (ctorNameOf idx e.key) args)
      | .obj => do fM fun d => { d with needObj := true }; pure erasedE)
    (hfL : ∀ {α : Type} (x : Except String α) s, fL x s = match x with | .ok a => .ok (a, s) | .error e => .error e)
    (hfM : ∀ u s, fM u s = .ok ((), { s with demand := u s.demand })) :
    isTrapExpr e ∧ TStateLe st st' ∧
    (isNatCoreRep r = true → datasNatCoreReps cx.P cx.cert cx.feat = true →
      isCleanNoU32 e = true) := by
  have hDef' : ∀ fuel cx r, fDummy fuel cx r =
      match r with
      | .irr => pure (.tuple [])
      | .nat _ | .w8 | .w16 => pure (litE 0)
      | .w32 => pure (callE "UInt32::from_field" [litE 0])
      | .w64 => fun st => .ok (callE "UInt64::from_field" [litE 0],
          { st with demand := { st.demand with needU64Bitwise := true } })
      | .enum ind => fun st =>
        match cx.cert.enum? ind with
        | some (k :: _) =>
          match cx.ctorEntry? k with
          | some (idx, e) => .ok (.construct (enumName ind) (some []) (ctorNameOf idx e.key) [], st)
          | none => .error "dummy: missing enum ctor"
        | _ => .error s!"dummy: empty enum {ind}"
      | .data d =>
        match fuel with
        | 0 => fun _ => .error s!"dummy: data {d} exceeded depth"
        | fuel' + 1 => fun st =>
          match cx.cert.data? d with
          | none => .error s!"dummy: missing data {d}"
          | some D =>
            match D.ctors.find? (fun (_, fl) => fl.all fun s => cx.rep s != .data d) with
            | none => .error s!"dummy: data {d} has no base constructor"
            | some (k, fl) =>
              match cx.ctorEntry? k with
              | none => .error "dummy: missing data ctor"
              | some (idx, e) =>
                match (fl.mapM (m := TLowerM) fun s => do
                  let fr := cx.rep s
                  let dv ← fDummy fuel' cx fr
                  return if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .store dv else dv) st with
                | .error err => .error err
                | .ok (args, st') =>
                  .ok (.construct (dataName d) (some []) (ctorNameOf idx e.key) args, st')
      | .obj => fun st => .ok (erasedE, { st with demand := { st.demand with needObj := true } }) := by
    intro fuel cx' r'
    funext s
    rw [hDef]
    cases r' with
    | irr | nat _ | w8 | w16 | w32 => rfl
    | w64 => simp [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, hfM]
    | obj => simp [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, hfM]
    | «enum» ind =>
      cases he : cx'.cert.enum? ind with
      | none => simp [he, hfL, throw, throwThe, MonadExceptOf.throw]
      | some ks =>
        cases ks with
        | nil => simp [he, hfL, throw, throwThe, MonadExceptOf.throw]
        | cons k _ =>
          cases hc : cx'.ctorEntry? k with
          | none => simp [he, hc, hfL, throw, throwThe, MonadExceptOf.throw]
          | some _ => simp [he, hc, pure, StateT.pure, Except.pure]
    | data d =>
      cases fuel with
      | zero => simp [hfL, throw, throwThe, MonadExceptOf.throw]
      | succ fuel' =>
        cases hD : cx'.cert.data? d with
        | none => simp [hD, hfL, throw, throwThe, MonadExceptOf.throw]
        | some D =>
          cases hfind : D.ctors.find? (fun (_, fl) => fl.all fun s => cx'.rep s != .data d) with
          | none => simp [hD, hfind, hfL, throw, throwThe, MonadExceptOf.throw]
          | some kfl =>
            cases hc : cx'.ctorEntry? kfl.1 with
            | none => simp [hD, hfind, hc, hfL, throw, throwThe, MonadExceptOf.throw]
            | some _ =>
              simp only [hD, hfind, hc, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure]
              cases (List.mapM (m := TLowerM) _ kfl.2) s <;> rfl
  have hTrap' : ∀ cx r msg st, fTrap cx r msg st =
      match fDummy (cx.cert.datas.length + 2) cx r st with
      | .error err => .error err
      | .ok (dv, st') =>
        .ok (seqE (.builtin (.assertEq (assertion msg)) [litE 0, litE 1]) dv, st') := by
    intro cx' r' msg' s
    rw [hTrap]
    simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure]
    cases fDummy (cx'.cert.datas.length + 2) cx' r' s <;> rfl
  exact trapSpec_poly fTrap fDummy hTrap' (dummySpec_poly fDummy hDef') cx r msg st e st' h

private theorem stepDownNat_ok_inv
    {fS : TCx → OffMap → Var → String → Rep → Rep → TLowerM (Lower.Expr × Option (String × Nat))}
    {cx : TCx} {offs : OffMap} {x : Var} {nx : String} {rx target : Rep}
    {st st' : TState} {e : Lower.Expr} {off? : Option (String × Nat)}
    (h : fS cx offs x nx rx target st = .ok ((e, off?), st'))
    (heq : ∀ cx offs x nx rx target s, fS cx offs x nx rx target s =
      (match offs.lookup x with
       | some (baseNm, d) =>
         if d < 256 then do
           let e ← coerceE cx (.nat rx.fieldBound) target (subE (vE baseNm) (litE (d + 1)))
           let off? := match target with | .nat _ => some (baseNm, d + 1) | _ => none
           pure (e, off?)
         else do
           let e ← coerceE cx (.nat rx.fieldBound) target (subE (vE nx) (litE 1))
           let off? := match target with | .nat _ => some (nx, 1) | _ => none
           pure (e, off?)
       | none => do
         let e ← coerceE cx (.nat rx.fieldBound) target (subE (vE nx) (litE 1))
         let off? := match target with | .nat _ => some (nx, 1) | _ => none
         pure (e, off?)) s) :
    TStateLe st st' ∧
    (isNatCoreRep target = true → datasNatCoreReps cx.P cx.cert cx.feat = true →
      isCleanNoU32 e = true) ∧
    (∀ baseNm d, off? = some (baseNm, d) →
      baseNm = nx ∨ baseNm ∈ offs.map (fun p => p.2.1)) := by
  rw [heq] at h
  cases hl : offs.lookup x with
  | none =>
    simp only [hl] at h
    obtain ⟨e1, st1, h1, h2⟩ := tBind_step_inv h
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
    obtain ⟨hle, hcl⟩ := coerceE_spec h1
    refine ⟨hle, fun ht hdatas => hcl rfl ht hdatas (by simp [subE, vE, litE, isCleanNoU32]), ?_⟩
    intro baseNm d ho
    cases target <;> simp at ho
    exact Or.inl ho.1.symm
  | some bd =>
    rcases bd with ⟨base0, d0⟩
    simp only [hl] at h
    by_cases hlt : d0 < 256
    · simp only [hlt, ↓reduceIte] at h
      obtain ⟨e1, st1, h1, h2⟩ := tBind_step_inv h
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      obtain ⟨hle, hcl⟩ := coerceE_spec h1
      refine ⟨hle, fun ht hdatas => hcl rfl ht hdatas (by simp [subE, vE, litE, isCleanNoU32]), ?_⟩
      intro baseNm d ho
      cases target <;> simp at ho
      have hm := mem_of_lookup_eq_some hl
      exact Or.inr (List.mem_map.mpr ⟨(x, (base0, d0)), hm, ho.1⟩)
    · simp only [hlt, ↓reduceIte] at h
      obtain ⟨e1, st1, h1, h2⟩ := tBind_step_inv h
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      obtain ⟨hle, hcl⟩ := coerceE_spec h1
      refine ⟨hle, fun ht hdatas => hcl rfl ht hdatas (by simp [subE, vE, litE, isCleanNoU32]), ?_⟩
      intro baseNm d ho
      cases target <;> simp at ho
      exact Or.inl ho.1.symm

/-- Predicate asserting that every function in `cx.P` uses core representations for
its return value and parameters. -/
def FunCoreRepsOk (cx : TCx) : Prop :=
  ∀ f fd, cx.P.fun? f = some fd → f < cx.P.size →
    isNatCoreRep (cx.rep (cx.funShapes f).ret) = true ∧
    ∀ p ∈ fd.params.map Prod.fst, isNatCoreRep (cx.rep ((cx.funShapes f).var p)) = true

theorem funCoreRepsOk_of_natCoreProgram {P : Program} {cert : ShapeCert}
    {sched : CircuitSchedule} (h : natCoreProgram P cert = true) :
    FunCoreRepsOk { P, cert, feat := scanFeatures P, sched } := by
  intro f fd hfun hsz
  obtain ⟨_, _, _, hret, hparams, _⟩ := natCoreProgram_funInfo h hfun hsz
  exact ⟨hret, hparams⟩

theorem tRhsE_spec {cx : TCx} {vm : TVarMap} {nz : List Var} {offs : OffMap}
    {r : Rhs} {target : Rep} {st st' : TState} {e : Lower.Expr} {off? : Option (String × Nat)}
    (h : tRhsE cx vm nz offs r target st = .ok ((e, off?), st')) :
    TStateLe st st' ∧
    ((match r with | .prim op _ => !op.isWord | _ => true) = true →
     (∀ p ∈ vm, isNatCoreRep p.2.2 = true) →
     isNatCoreRep target = true →
     datasNatCoreReps cx.P cx.cert cx.feat = true →
     FunCoreRepsOk cx →
     isCleanNoU32 e = true) ∧
    (∀ baseNm d, off? = some (baseNm, d) →
      baseNm ∈ vm.map (fun p => p.2.1) ∨ baseNm ∈ offs.map (fun p => p.2.1)) := by
  cases r with
  | arg a =>
    unfold tRhsE at h
    obtain ⟨e1, st1, h1, h2⟩ := tBind_step_inv h
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
    obtain ⟨hle, hcl⟩ := tArgE_spec h1
    refine ⟨hle, fun _ hvm ht hdatas _ => hcl hvm ht hdatas, ?_⟩
    intro baseNm d ho
    cases a <;> cases target <;> simp at ho
    exact Or.inr (List.mem_map.mpr ⟨(_, (baseNm, d)), mem_of_lookup_eq_some ho, rfl⟩)
  | ctor c as =>
    unfold tRhsE at h
    cases hce : cx.ctorEntry? c.key with
    | none =>
      simp only [hce] at h
      exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    | some ie =>
      rcases ie with ⟨idx, entry⟩
      simp only [hce] at h
      by_cases har : (as.length == entry.arity && c.arity == entry.arity) = true
      · simp only [har, ↓reduceIte] at h
        cases target with
        | «enum» ind =>
          obtain ⟨e1, s1, h1, h2⟩ := tBind_step_inv h
          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1 h2
          obtain ⟨rfl, rfl⟩ := h1
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
          exact ⟨TStateLe.refl _, fun _ _ _ _ _ => rfl, fun _ _ ho => by cases ho⟩
        | data d =>
          cases hD : cx.cert.data? d with
          | none =>
            simp only [hD] at h
            obtain ⟨_, _, h1, _⟩ := tBind_step_inv h
            exact False.elim (tLift_throw_elim h1 (fun _ _ => rfl))
          | some D =>
            simp only [hD] at h
            cases hf : D.ctors.find? (·.1 == c.key) with
            | none =>
              simp only [hf] at h
              obtain ⟨_, _, h1, _⟩ := tBind_step_inv h
              exact False.elim (tLift_throw_elim h1 (fun _ _ => rfl))
            | some kfl =>
              rcases kfl with ⟨k', fl⟩
              simp only [hf] at h
              obtain ⟨fes, st1, hmap, h2⟩ := tBind_step_inv h
              obtain ⟨e1, st2, h2a, h2b⟩ := tBind_step_inv h2
              simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h2a h2b
              obtain ⟨rfl, rfl⟩ := h2a
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2b
              have hlist : ∀ (ls : List (Arg × Shape)) (s0 s1 : TState) (es : List Lower.Expr),
                  (∀ p ∈ ls, p.2 ∈ fl) →
                  (ls.mapM (m := TLowerM) fun (a, sh) => do
                    let fr := cx.rep sh
                    let ae ← tArgE cx vm a fr
                    pure (if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.store ae else ae)) s0 =
                    .ok (es, s1) →
                  TStateLe s0 s1 ∧
                  ((∀ p ∈ vm, isNatCoreRep p.2.2 = true) → datasNatCoreReps cx.P cx.cert cx.feat = true →
                    isCleanNoU32List es = true) := by
                intro ls
                induction ls with
                | nil =>
                  intro s0 s1 es _ h0
                  simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
                    Except.ok.injEq, Prod.mk.injEq] at h0
                  obtain ⟨rfl, rfl⟩ := h0; exact ⟨TStateLe.refl _, fun _ _ => rfl⟩
                | cons hd tl ih =>
                  intro s0 s1 es hsub h0
                  rw [List.mapM_cons] at h0
                  obtain ⟨e1, sa, h1, h0⟩ := tBind_step_inv h0
                  obtain ⟨es2, sb, h2, h0⟩ := tBind_step_inv h0
                  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
                  obtain ⟨rfl, rfl⟩ := h0
                  obtain ⟨ae, sa', hae, h1'⟩ := tBind_step_inv h1
                  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1'
                  obtain ⟨rfl, rfl⟩ := h1'
                  obtain ⟨hle1, hcl1⟩ := tArgE_spec hae
                  obtain ⟨hle2, hcl2⟩ := ih sa' sb es2 (fun p hp => hsub p (List.mem_cons_of_mem _ hp)) h2
                  refine ⟨hle1.trans hle2, fun hvm hdatas => ?_⟩
                  have hcore : isNatCoreRep (cx.rep hd.2) = true :=
                    datasNatCoreReps_field hdatas hD (List.mem_of_find?_eq_some hf) (hsub hd List.mem_cons_self)
                  have haec := hcl1 hvm hcore hdatas
                  have hcl1' : isCleanNoU32 (if dataFieldNeedsPtr cx.P cx.cert cx.feat d (cx.rep hd.2)
                      then Aiur.Generic.Expr.store ae else ae) = true := by
                    split <;> simpa [isCleanNoU32] using haec
                  simp [isCleanNoU32List, hcl1', hcl2 hvm hdatas]
              obtain ⟨hle, hcl⟩ := hlist (as.zip fl) st st1 fes (fun p hp => (List.of_mem_zip hp).2) hmap
              refine ⟨hle, fun _ hvm _ hdatas _ => by simpa [isCleanNoU32] using hcl hvm hdatas,
                fun _ _ ho => by cases ho⟩
        | irr | nat _ | w8 | w16 | w32 | w64 | obj =>
          obtain ⟨s1, hle1, _, hm⟩ := tMark_step_inv h (fun _ _ => rfl)
            (fun _ => by constructor <;> first | exact id | (intro _; rfl))
          obtain ⟨argEs, s2, hmap, hm⟩ := tBind_step_inv hm
          obtain ⟨e1, s3, h3, hm⟩ := tBind_step_inv hm
          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
          obtain ⟨hle3, hcl3⟩ := coerceE_spec h3
          have hlist : ∀ (ls : List Arg) (s0 s1' : TState) (es : List Lower.Expr),
              (ls.mapM (m := TLowerM) fun a => do pure (Aiur.Generic.Expr.store (← tArgE cx vm a .obj))) s0 =
                .ok (es, s1') →
              TStateLe s0 s1' ∧
              ((∀ p ∈ vm, isNatCoreRep p.2.2 = true) → datasNatCoreReps cx.P cx.cert cx.feat = true →
                isCleanNoU32List es = true) := by
            intro ls
            induction ls with
            | nil =>
              intro s0 s1' es h0
              simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
                Except.ok.injEq, Prod.mk.injEq] at h0
              obtain ⟨rfl, rfl⟩ := h0; exact ⟨TStateLe.refl _, fun _ _ => rfl⟩
            | cons a tl ih =>
              intro s0 s1' es h0
              rw [List.mapM_cons] at h0
              obtain ⟨e1, sa, h1, h0⟩ := tBind_step_inv h0
              obtain ⟨es2, sb, h2, h0⟩ := tBind_step_inv h0
              simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
              obtain ⟨rfl, rfl⟩ := h0
              obtain ⟨ae, sa', hae, h1'⟩ := tBind_step_inv h1
              simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1'
              obtain ⟨rfl, rfl⟩ := h1'
              obtain ⟨hleA, hclA⟩ := tArgE_spec hae
              obtain ⟨hleB, hclB⟩ := ih sa' sb es2 h2
              exact ⟨hleA.trans hleB, fun hvm hdatas => by
                simp [isCleanNoU32List, isCleanNoU32, hclA hvm rfl hdatas, hclB hvm hdatas]⟩
          obtain ⟨hle2, hcl2⟩ := hlist as s1 s2 argEs hmap
          refine ⟨(hle1.trans hle2).trans hle3, fun _ hvm ht hdatas _ => ?_,
            fun _ _ ho => by cases ho⟩
          exact hcl3 rfl ht hdatas (isCleanNoU32_mk (hcl2 hvm hdatas))
      · have harf : (as.length == entry.arity && c.arity == entry.arity) = false :=
          Bool.eq_false_iff.mpr har
        simp only [harf, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨_, _, h1, _⟩ := tBind_step_inv h
        exact False.elim (tLift_throw_elim h1 (fun _ _ => rfl))
  | proj x c i =>
    unfold tRhsE at h
    cases hlook : vm.lookup x with
    | none =>
      simp only [hlook] at h
      exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    | some nr =>
      rcases nr with ⟨nx, rx⟩
      simp only [hlook] at h
      have hnxMem : nx ∈ vm.map (fun p => p.2.1) :=
        List.mem_map.mpr ⟨(x, (nx, rx)), mem_of_lookup_eq_some hlook, rfl⟩
      cases rx with
      | nat b | w8 | w16 =>
        by_cases hns : (cx.P.known.natSucc == some c && i == 0) = true
        · simp only [hns, ↓reduceIte] at h
          by_cases hnz : nz.contains x = true
          · simp only [hnz, ↓reduceIte] at h
            obtain ⟨hle, hcl, hoff⟩ := stepDownNat_ok_inv h
              (fun _ _ _ _ _ _ _ => rfl)
            exact ⟨hle, fun _ _ ht hdatas _ => hcl ht hdatas, fun bm d ho =>
              (hoff bm d ho).imp (fun h => by rw [h]; exact hnxMem) id⟩
          · simp only [hnz, Bool.false_eq_true, ↓reduceIte] at h
            obtain ⟨tr, s1, h1, h⟩ := tBind_step_inv h
            obtain ⟨e2, s2, h2, h⟩ := tBind_step_inv h
            simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
            obtain ⟨_, hle1, hcl1⟩ := tTrapE_ok_inv h1 (fun _ _ _ => rfl)
              (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
              (fun _ _ => rfl) (fun _ _ => rfl)
            obtain ⟨hle2, hcl2⟩ := coerceE_spec h2
            refine ⟨hle1.trans hle2, fun _ _ ht hdatas _ => ?_, fun _ _ ho => by cases ho⟩
            have htr := hcl1 rfl hdatas
            apply hcl2 rfl ht hdatas
            simp [matchE, subE, vE, litE, isCleanNoU32, isCleanNoU32Arms, isSimplePat, htr]
        · simp only [hns, Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨tr, s1, h1, h⟩ := tBind_step_inv h
          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          obtain ⟨_, hle1, hcl1⟩ := tTrapE_ok_inv h1 (fun _ _ _ => rfl)
            (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
            (fun _ _ => rfl) (fun _ _ => rfl)
          exact ⟨hle1, fun _ _ ht hdatas _ => hcl1 ht hdatas, fun _ _ ho => by cases ho⟩
      | data d =>
        cases hD : cx.cert.data? d with
        | none =>
          simp only [hD] at h
          exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
        | some D =>
          simp only [hD] at h
          cases hf : D.ctors.find? (·.1 == c) with
          | none =>
            simp only [hf] at h
            obtain ⟨tr, s1, h1, h⟩ := tBind_step_inv h
            simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
            obtain ⟨_, hle1, hcl1⟩ := tTrapE_ok_inv h1 (fun _ _ _ => rfl)
              (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
              (fun _ _ => rfl) (fun _ _ => rfl)
            exact ⟨hle1, fun _ _ ht hdatas _ => hcl1 ht hdatas, fun _ _ ho => by cases ho⟩
          | some kfl =>
            rcases kfl with ⟨k', fl⟩
            simp only [hf] at h
            cases hce : cx.ctorEntry? c with
            | none =>
              simp only [hce] at h
              obtain ⟨tr, s1, h1, h⟩ := tBind_step_inv h
              simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
              obtain ⟨_, hle1, hcl1⟩ := tTrapE_ok_inv h1 (fun _ _ _ => rfl)
                (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
                (fun _ _ => rfl) (fun _ _ => rfl)
              exact ⟨hle1, fun _ _ ht hdatas _ => hcl1 ht hdatas, fun _ _ ho => by cases ho⟩
            | some ie =>
              rcases ie with ⟨idx, entry⟩
              simp only [hce] at h
              cases hsh : fl[i]? with
              | none =>
                simp only [hsh] at h
                obtain ⟨tr, s1, h1, h⟩ := tBind_step_inv h
                simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                obtain ⟨_, hle1, hcl1⟩ := tTrapE_ok_inv h1 (fun _ _ _ => rfl)
                  (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
                  (fun _ _ => rfl) (fun _ _ => rfl)
                exact ⟨hle1, fun _ _ ht hdatas _ => hcl1 ht hdatas, fun _ _ ho => by cases ho⟩
              | some sh =>
                simp only [hsh] at h
                obtain ⟨hle1, h⟩ := tFreshLocal_step_inv h (fun _ => rfl)
                obtain ⟨body, s2, h2, h⟩ := tBind_step_inv h
                simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                obtain ⟨hle2, hcl2⟩ := coerceE_spec h2
                refine ⟨hle1.trans hle2, fun _ _ ht hdatas _ => ?_, fun _ _ ho => by cases ho⟩
                have hcore : isNatCoreRep (cx.rep sh) = true :=
                  datasNatCoreReps_field hdatas hD (List.mem_of_find?_eq_some hf) (List.mem_of_getElem? hsh)
                have hbody0 : isCleanNoU32 (if dataFieldNeedsPtr cx.P cx.cert cx.feat d (cx.rep sh)
                    then Aiur.Generic.Expr.load (vE (localName st.nextLocal))
                    else vE (localName st.nextLocal)) = true := by
                  split <;> rfl
                have hbody := hcl2 hcore ht hdatas hbody0
                have hsp : ∀ (l : List Nat), isSimplePatList (l.map fun j =>
                    if j = i then .bind (localName st.nextLocal) else .wildcard) = true := by
                  intro l; induction l with
                  | nil => rfl
                  | cons hd tl ih =>
                    simp only [List.map_cons, isSimplePatList, ih, Bool.and_true]
                    split <;> rfl
                simp [matchE, vE, isCleanNoU32, isCleanNoU32Arms, isSimplePat, hsp, hbody]
      | obj =>
        obtain ⟨s1, hle1, _, h⟩ := tMark_step_inv h (fun _ _ => rfl)
          (fun _ => by constructor <;> first | exact id | (intro _; rfl))
        obtain ⟨e2, s2, h2, h⟩ := tBind_step_inv h
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        obtain ⟨hle2, hcl2⟩ := coerceE_spec h2
        exact ⟨hle1.trans hle2, fun _ _ ht hdatas _ =>
          hcl2 rfl ht hdatas (isCleanNoU32_projE ⟨cx.P⟩ nx c i), fun _ _ ho => by cases ho⟩
      | irr | w32 | w64 | «enum» _ =>
        obtain ⟨tr, s1, h1, h⟩ := tBind_step_inv h
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        obtain ⟨_, hle1, hcl1⟩ := tTrapE_ok_inv h1 (fun _ _ _ => rfl)
          (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
          (fun _ _ => rfl) (fun _ _ => rfl)
        exact ⟨hle1, fun _ _ ht hdatas _ => hcl1 ht hdatas, fun _ _ ho => by cases ho⟩
  | prim op as =>
    have hPrimFallback : ∀ (op' : Prim) (as' : List Arg),
        (tPrimE cx vm op' as' target >>= fun e1 => pure (e1, (none : Option (String × Nat)))) st =
          .ok ((e, off?), st') →
        TStateLe st st' ∧
        ((!op'.isWord) = true → (∀ p ∈ vm, isNatCoreRep p.2.2 = true) →
          isNatCoreRep target = true → datasNatCoreReps cx.P cx.cert cx.feat = true →
          FunCoreRepsOk cx → isCleanNoU32 e = true) ∧
        (∀ baseNm d, off? = some (baseNm, d) →
          baseNm ∈ vm.map (fun p => p.2.1) ∨ baseNm ∈ offs.map (fun p => p.2.1)) := by
      intro op' as' hp
      obtain ⟨e1, s1, h1, h2⟩ := tBind_step_inv hp
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      obtain ⟨hle, hcl⟩ := tPrimE_spec h1
      exact ⟨hle, fun hnw hvm ht hdatas _ => hcl (Bool.eq_false_iff.mpr (by simpa using hnw)) hvm ht hdatas,
        fun _ _ ho => by cases ho⟩
    unfold tRhsE at h
    cases op with
    | natPred =>
      cases as with
      | nil => exact hPrimFallback _ _ h
      | cons a rest =>
        cases a with
        | lit _ | erased => exact hPrimFallback _ _ h
        | var x =>
          cases rest with
          | cons _ _ => exact hPrimFallback _ _ h
          | nil =>
            cases target with
            | nat b =>
              by_cases hnz : nz.contains x = true
              · simp only [hnz, ↓reduceIte] at h
                cases hlook : vm.lookup x with
                | none => simp only [hlook] at h; exact hPrimFallback _ _ h
                | some nr =>
                  rcases nr with ⟨nx, rx⟩
                  simp only [hlook] at h
                  by_cases hfn : rx.isFieldNat = true
                  · simp only [hfn, ↓reduceIte] at h
                    have hnxMem : nx ∈ vm.map (fun p => p.2.1) :=
                      List.mem_map.mpr ⟨(x, (nx, rx)), mem_of_lookup_eq_some hlook, rfl⟩
                    obtain ⟨hle, hcl, hoff⟩ := stepDownNat_ok_inv h
                      (fun _ _ _ _ _ _ _ => rfl)
                    exact ⟨hle, fun _ _ ht hdatas _ => hcl ht hdatas,
                      fun bm d ho => (hoff bm d ho).imp (fun h => by rw [h]; exact hnxMem) id⟩
                  · simp only [hfn, Bool.false_eq_true, ↓reduceIte] at h
                    exact hPrimFallback _ _ h
              · simp only [hnz, Bool.false_eq_true, ↓reduceIte] at h
                exact hPrimFallback _ _ h
            | irr | w8 | w16 | w32 | w64 | «enum» _ | data _ | obj => exact hPrimFallback _ _ h
    | natSub =>
      cases target with
      | irr | w8 | w16 | w32 | w64 | «enum» _ | data _ | obj =>
        simp only [] at h; exact hPrimFallback _ _ h
      | nat b =>
        rcases as with _ | ⟨a, _ | ⟨b', _ | ⟨_, _⟩⟩⟩
        · simp only [] at h; exact hPrimFallback _ _ h
        · simp only [] at h; exact hPrimFallback _ _ h
        · cases a with
          | lit _ | erased => simp only [] at h; exact hPrimFallback _ _ h
          | var x =>
            cases b' with
            | var _ | erased => simp only [] at h; exact hPrimFallback _ _ h
            | lit l =>
              cases l with
              | str _ => simp only [] at h; exact hPrimFallback _ _ h
              | nat k =>
                cases k with
                | zero => simp only [] at h; exact hPrimFallback _ _ h
                | succ k' =>
                  cases k' with
                  | succ _ => simp only [] at h; exact hPrimFallback _ _ h
                  | zero =>
                    simp only [] at h
                    by_cases hnz : nz.contains x = true
                    · simp only [hnz, ↓reduceIte] at h
                      cases hlook : vm.lookup x with
                      | none => simp only [hlook] at h; exact hPrimFallback _ _ h
                      | some nr =>
                        rcases nr with ⟨nx, rx⟩
                        simp only [hlook] at h
                        by_cases hfn : rx.isFieldNat = true
                        · simp only [hfn, ↓reduceIte] at h
                          have hnxMem : nx ∈ vm.map (fun p => p.2.1) :=
                            List.mem_map.mpr ⟨(x, (nx, rx)), mem_of_lookup_eq_some hlook, rfl⟩
                          obtain ⟨hle, hcl, hoff⟩ := stepDownNat_ok_inv h
                            (fun _ _ _ _ _ _ _ => rfl)
                          exact ⟨hle, fun _ _ ht hdatas _ => hcl ht hdatas,
                            fun bm d ho => (hoff bm d ho).imp (fun h => by rw [h]; exact hnxMem) id⟩
                        · simp only [hfn, Bool.false_eq_true, ↓reduceIte] at h
                          exact hPrimFallback _ _ h
                    · simp only [hnz, Bool.false_eq_true, ↓reduceIte] at h
                      exact hPrimFallback _ _ h
        · simp only [] at h; exact hPrimFallback _ _ h
    | natAdd =>
      have hAddOff : ∀ (as' : List Arg) (x : Var) (k : Nat),
          (match offs.lookup x with
           | some (baseNm, d) =>
             if k ≤ d then
               if k == d then pure (vE baseNm, some (baseNm, 0))
               else pure (subE (vE baseNm) (litE (d - k)), some (baseNm, d - k))
             else do return (← tPrimE cx vm .natAdd as' target, none)
           | none => do return (← tPrimE cx vm .natAdd as' target, none)) st = .ok ((e, off?), st') →
          TStateLe st st' ∧
          ((!Prim.natAdd.isWord) = true → (∀ p ∈ vm, isNatCoreRep p.2.2 = true) →
            isNatCoreRep target = true → datasNatCoreReps cx.P cx.cert cx.feat = true →
            FunCoreRepsOk cx → isCleanNoU32 e = true) ∧
          (∀ baseNm d, off? = some (baseNm, d) →
            baseNm ∈ vm.map (fun p => p.2.1) ∨ baseNm ∈ offs.map (fun p => p.2.1)) := by
        intro as' x k ha
        cases hl : offs.lookup x with
        | none => simp only [hl] at ha; exact hPrimFallback _ _ ha
        | some bd =>
          rcases bd with ⟨base0, d0⟩
          simp only [hl] at ha
          by_cases hle : k ≤ d0
          · simp only [hle, ↓reduceIte] at ha
            have hm : base0 ∈ offs.map (fun p => p.2.1) :=
              List.mem_map.mpr ⟨(x, (base0, d0)), mem_of_lookup_eq_some hl, rfl⟩
            by_cases heq : (k == d0) = true
            · simp only [heq, ↓reduceIte, pure, StateT.pure, Except.pure,
                Except.ok.injEq, Prod.mk.injEq] at ha
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ha
              exact ⟨TStateLe.refl _, fun _ _ _ _ _ => rfl,
                fun bm _ ho => by cases ho; exact Or.inr hm⟩
            · simp only [heq, Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, Except.pure,
                Except.ok.injEq, Prod.mk.injEq] at ha
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ha
              exact ⟨TStateLe.refl _, fun _ _ _ _ _ => rfl,
                fun bm _ ho => by cases ho; exact Or.inr hm⟩
          · simp only [hle, ↓reduceIte] at ha; exact hPrimFallback _ _ ha
      cases target with
      | irr | w8 | w16 | w32 | w64 | «enum» _ | data _ | obj =>
        simp only [] at h; exact hPrimFallback _ _ h
      | nat _ =>
        rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
        · simp only [] at h; exact hPrimFallback _ _ h
        · simp only [] at h; exact hPrimFallback _ _ h
        · cases a with
          | var x =>
            cases b with
            | lit l =>
              cases l with
              | nat k => simp only [] at h; exact hAddOff _ x k h
              | str _ => simp only [] at h; exact hPrimFallback _ _ h
            | var _ | erased => simp only [] at h; exact hPrimFallback _ _ h
          | lit l =>
            cases l with
            | nat k =>
              cases b with
              | var x => simp only [] at h; exact hAddOff _ x k h
              | lit _ | erased => simp only [] at h; exact hPrimFallback _ _ h
            | str _ => simp only [] at h; exact hPrimFallback _ _ h
          | erased => simp only [] at h; exact hPrimFallback _ _ h
        · simp only [] at h; exact hPrimFallback _ _ h
    | natMul | natDiv | natMod | natPow | natGcd | natShl | natShr
    | natBeq | natBle | natBlt | natLand | natLor | natXor | word _ _ =>
      exact hPrimFallback _ _ h
  | call f as =>
    unfold tRhsE at h
    cases hfun : cx.P.fun? f with
    | none => simp only [hfun] at h; exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    | some fd =>
      simp only [hfun] at h
      by_cases hsz : f < cx.P.size
      · simp only [hsz, ↓reduceIte] at h
        by_cases har : (as.length == fd.params.length) = true
        · simp only [har, ↓reduceIte] at h
          obtain ⟨argEs, s1, hmap, h⟩ := tBind_step_inv h
          obtain ⟨e1, s2, h2, h⟩ := tBind_step_inv h
          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          obtain ⟨hle2, hcl2⟩ := coerceE_spec h2
          have hlist : ∀ (ls : List (Arg × Rep)) (s0 s1' : TState) (es : List Lower.Expr),
              (ls.mapM (m := TLowerM) fun x => tArgE cx vm x.1 x.2) s0 = .ok (es, s1') →
              TStateLe s0 s1' ∧
              ((∀ p ∈ vm, isNatCoreRep p.2.2 = true) →
               (∀ q ∈ ls, isNatCoreRep q.2 = true) →
               datasNatCoreReps cx.P cx.cert cx.feat = true →
               isCleanNoU32List es = true) := by
            intro ls
            induction ls with
            | nil =>
              intro s0 s1' es h0
              simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
                Except.ok.injEq, Prod.mk.injEq] at h0
              obtain ⟨rfl, rfl⟩ := h0; exact ⟨TStateLe.refl _, fun _ _ _ => rfl⟩
            | cons hd tl ih =>
              intro s0 s1' es h0
              rw [List.mapM_cons] at h0
              obtain ⟨e1', sa, h1, h0⟩ := tBind_step_inv h0
              obtain ⟨es2, sb, h2', h0⟩ := tBind_step_inv h0
              simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
              obtain ⟨rfl, rfl⟩ := h0
              obtain ⟨hleA, hclA⟩ := tArgE_spec h1
              obtain ⟨hleB, hclB⟩ := ih sa sb es2 h2'
              exact ⟨hleA.trans hleB, fun hvm hls hdatas => by
                simp [isCleanNoU32List, hclA hvm (hls hd List.mem_cons_self) hdatas,
                  hclB hvm (fun q hq => hls q (List.mem_cons_of_mem _ hq)) hdatas]⟩
          obtain ⟨hle1, hcl1⟩ := hlist _ st s1 argEs hmap
          refine ⟨hle1.trans hle2, fun _ hvm ht hdatas hfc => ?_, fun _ _ ho => by cases ho⟩
          obtain ⟨hretCore, hparamCore⟩ := hfc f fd hfun hsz
          have hargsClean : isCleanNoU32List argEs = true := by
            apply hcl1 hvm _ hdatas
            intro q hq
            have hq2 := (List.of_mem_zip hq).2
            obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hq2
            rw [← hpeq]; exact hparamCore p hp
          exact hcl2 hretCore ht hdatas (isCleanNoU32_callE (isPeepholeU32Name_funName f) hargsClean)
        · have harf : (as.length == fd.params.length) = false := Bool.eq_false_iff.mpr har
          simp only [harf, Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨_, _, h1, _⟩ := tBind_step_inv h
          exact False.elim (tLift_throw_elim h1 (fun _ _ => rfl))
      · simp only [hsz, ↓reduceIte] at h
        obtain ⟨_, _, h1, _⟩ := tBind_step_inv h
        exact False.elim (tLift_throw_elim h1 (fun _ _ => rfl))

private theorem filterMapM_pure_stateT {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (st : TState),
      (xs.filterMapM (m := TLowerM) fun a => pure (f a)) st = .ok (xs.filterMap f, st) := by
  intro xs
  have hloop : ∀ (l : List α) (bacc : List β) (st : TState),
      (List.filterMapM.loop (m := TLowerM) (fun a => pure (f a)) l bacc) st =
        .ok (bacc.reverse ++ l.filterMap f, st) := by
    intro l
    induction l with
    | nil =>
      intro bacc st
      simp [List.filterMapM.loop, pure, StateT.pure, Except.pure]
    | cons a tl ih =>
      intro bacc st
      rw [List.filterMapM.loop]
      simp only [bind, StateT.bind, Except.bind, List.filterMap_cons]
      have hp : (pure (f a) : TLowerM (Option β)) st = .ok (f a, st) := rfl
      rw [hp]
      cases hfa : f a with
      | none => exact ih bacc st
      | some b =>
        dsimp only
        rw [ih (b :: bacc) st]
        simp [List.reverse_cons, List.append_assoc]
  intro st
  simpa [List.filterMapM] using hloop xs [] st

private theorem firstPerKey_mem : ∀ (acc alts : List (CtorKey × Lower.Expr)) (p : CtorKey × Lower.Expr),
    p ∈ Lower.firstPerKey acc alts → p ∈ acc ∨ p ∈ alts
  | acc, [], p, hm => by
    simp only [Lower.firstPerKey, List.mem_reverse] at hm
    exact Or.inl hm
  | acc, (k, e) :: rest, p, hm => by
    unfold Lower.firstPerKey at hm
    split at hm
    · exact (firstPerKey_mem acc rest p hm).imp id (List.mem_cons_of_mem _)
    · rcases firstPerKey_mem ((k, e) :: acc) rest p hm with h1 | h2
      · rcases List.mem_cons.mp h1 with rfl | hacc
        · exact Or.inr List.mem_cons_self
        · exact Or.inl hacc
      · exact Or.inr (List.mem_cons_of_mem _ h2)

theorem tCaseE_spec {cx : TCx} {nx : String} {rx retR : Rep}
    {alts : List (CtorKey × Lower.Expr)} {d : Option Lower.Expr}
    {st st' : TState} {e : Lower.Expr}
    (h : tCaseE cx nx rx retR alts d st = .ok (e, st')) :
    TStateLe st st' ∧
    (isNatCoreRep retR = true → datasNatCoreReps cx.P cx.cert cx.feat = true →
     (∀ p ∈ alts, isCleanNoU32 p.2 = true) →
     (∀ de, d = some de → isCleanNoU32 de = true) →
     isCleanNoU32 e = true) := by
  unfold tCaseE at h
  have hcont : ∀ {fTrap : TCx → Rep → String → TLowerM Lower.Expr}
      {fL : {α : Type} → Except String α → TLowerM α}
      {fM : (Demand → Demand) → TLowerM Unit}
      {fF : TLowerM String}
      (fb : Lower.Expr) (s1 : TState),
      (let firsts : List (CtorKey × Lower.Expr) := Lower.firstPerKey [] alts
       let pick (ok : Option CtorKey) : TLowerM Lower.Expr :=
         match ok with
         | some k => pure (((firsts.find? (fun (p : CtorKey × Lower.Expr) => p.1 == k)).map (fun (p : CtorKey × Lower.Expr) => p.2)).getD fb)
         | none => fTrap cx retR "unpinned Nat literal under case"
       match rx with
       | .nat _ | .w8 | .w16 => do
         let zBody ← pick cx.P.known.natZero
         let sBody ← pick cx.P.known.natSucc
         return matchE (vE nx) [(.literal 0, zBody), (.wildcard, sBody)]
       | .enum ind => do
         let some ks := cx.cert.enum? ind | fL (throw s!"case: unknown enum {ind}")
         let arms ← firsts.filterMapM (m := TLowerM) fun ((k, body) : CtorKey × Lower.Expr) =>
           if ks.contains k then
             match cx.ctorEntry? k with
             | some (idx, entry) =>
               pure (some (Aiur.Generic.Pattern.construct (.named (enumName ind) []) (ctorNameOf idx entry.key) [], body))
             | none => pure none
           else pure none
         let dfltArm : List (Lower.Pat × Lower.Expr) := Option.rec [] (fun de => [(Aiur.Generic.Pattern.wildcard, de)]) d
         return matchE (vE nx) (arms ++ dfltArm)
       | .data did => do
         let some D := cx.cert.data? did | fL (throw s!"case: unknown data {did}")
         let arms ← firsts.filterMapM (m := TLowerM) fun ((k, body) : CtorKey × Lower.Expr) =>
           if D.ctors.any (·.1 == k) then
             match cx.ctorEntry? k with
             | some (idx, entry) =>
               pure (some (Aiur.Generic.Pattern.construct (.named (dataName did) []) (ctorNameOf idx entry.key)
                 (List.replicate entry.arity Aiur.Generic.Pattern.wildcard), body))
             | none => pure none
           else pure none
         let dfltArm : List (Lower.Pat × Lower.Expr) := Option.rec [] (fun de => [(Aiur.Generic.Pattern.wildcard, de)]) d
         return matchE (vE nx) (arms ++ dfltArm)
       | .obj => do
         fM fun dm => { dm with needObj := true }
         let arms := Lower.ctorArms ⟨cx.P⟩ firsts
         let q ← fF
         let zBody ← pick cx.P.known.natZero
         let sBody ← pick cx.P.known.natSucc
         let natArm : Lower.Pat × Lower.Expr :=
           (pN (.bind q), matchE (vE q) [(.literal 0, zBody), (.wildcard, sBody)])
         let erasedArm : Lower.Pat × Lower.Expr := (pC "E" [], ← fTrap cx retR "case on an erased value")
         let strArm : Lower.Pat × Lower.Expr := (pC "S" [.wildcard], ← fTrap cx retR "case on a string literal")
         let dfltArm : List (Lower.Pat × Lower.Expr) := Option.rec [] (fun de => [(Aiur.Generic.Pattern.wildcard, de)]) d
         return matchE (vE nx) (arms ++ [natArm, erasedArm, strArm] ++ dfltArm)
       | .irr => fTrap cx retR "case on erased value"
       | _ => fL (throw s!"case on unsupported rep {reprStr rx}")) s1 = .ok (e, st') →
      (∀ cx r msg st e st', fTrap cx r msg st = .ok (e, st') →
        TStateLe st st' ∧ (isNatCoreRep r = true → datasNatCoreReps cx.P cx.cert cx.feat = true → isCleanNoU32 e = true)) →
      (∀ {α : Type} (x : Except String α) s, fL x s = match x with | .ok a => .ok (a, s) | .error e => .error e) →
      (∀ u s, fM u s = .ok ((), { s with demand := u s.demand })) →
      (∀ s, fF s = .ok (localName s.nextLocal, { s with nextLocal := s.nextLocal + 1 })) →
      TStateLe st s1 →
      (isNatCoreRep retR = true → datasNatCoreReps cx.P cx.cert cx.feat = true →
       (∀ de, d = some de → isCleanNoU32 de = true) → isCleanNoU32 fb = true) →
      TStateLe st st' ∧
      (isNatCoreRep retR = true → datasNatCoreReps cx.P cx.cert cx.feat = true →
       (∀ p ∈ alts, isCleanNoU32 p.2 = true) →
       (∀ de, d = some de → isCleanNoU32 de = true) →
       isCleanNoU32 e = true) := by
    intro fTrap fL fM fF fb s1 hc hTrap hfL hfM hfF hleFb hclFb
    have hpick : ∀ (ok : Option CtorKey) (sa sb : TState) (pe : Lower.Expr),
        (match ok with
         | some k => pure ((((Lower.firstPerKey [] alts).find? (fun (p : CtorKey × Lower.Expr) => p.1 == k)).map (fun (p : CtorKey × Lower.Expr) => p.2)).getD fb)
         | none => fTrap cx retR "unpinned Nat literal under case") sa = .ok (pe, sb) →
        TStateLe sa sb ∧
        (isNatCoreRep retR = true → datasNatCoreReps cx.P cx.cert cx.feat = true →
         (∀ p ∈ alts, isCleanNoU32 p.2 = true) → isCleanNoU32 fb = true → isCleanNoU32 pe = true) := by
      intro ok sa sb pe hp
      cases ok with
      | none =>
        obtain ⟨hle, hcl⟩ := hTrap cx retR "unpinned Nat literal under case" sa pe sb hp
        exact ⟨hle, fun hr hdatas _ _ => hcl hr hdatas⟩
      | some k =>
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        refine ⟨TStateLe.refl _, fun _ _ halts hfbClean => ?_⟩
        cases hf : (Lower.firstPerKey [] alts).find? (·.1 == k) with
        | none => simpa [hf] using hfbClean
        | some p =>
          simp only [Option.map_some, Option.getD_some]
          rcases firstPerKey_mem [] alts p (List.mem_of_find?_eq_some hf) with hnil | hm'
          · cases hnil
          · exact halts p hm'
    have hdfltClean : ∀ (hd : ∀ de, d = some de → isCleanNoU32 de = true),
        isCleanNoU32Arms (Option.rec [] (fun de => [(.wildcard, de)]) d) = true := by
      intro hd; cases d with
      | none => rfl
      | some de => simp [isCleanNoU32Arms, isSimplePat, hd de rfl]
    cases rx with
    | nat b | w8 | w16 =>
      obtain ⟨zBody, s2, hz, hc⟩ := tBind_step_inv hc
      obtain ⟨sBody, s3, hs, hc⟩ := tBind_step_inv hc
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨hle2, hcl2⟩ := hpick cx.P.known.natZero s1 s2 zBody hz
      obtain ⟨hle3, hcl3⟩ := hpick cx.P.known.natSucc s2 s3 sBody hs
      refine ⟨(hleFb.trans hle2).trans hle3, fun hr hdatas halts hd => ?_⟩
      have hfbc := hclFb hr hdatas hd
      simp [matchE, vE, isCleanNoU32, isCleanNoU32Arms, isSimplePat,
        hcl2 hr hdatas halts hfbc, hcl3 hr hdatas halts hfbc]
    | «enum» ind =>
      cases he : cx.cert.enum? ind with
      | none => simp [he, hfL, throw, throwThe, MonadExceptOf.throw] at hc
      | some ks =>
        simp only [he] at hc
        let armFn : CtorKey × Lower.Expr → Option (Lower.Pat × Lower.Expr) := fun (k, body) =>
          if ks.contains k then
            match cx.ctorEntry? k with
            | some (idx, entry) =>
              some (.construct (.named (enumName ind) []) (ctorNameOf idx entry.key) [], body)
            | none => none
          else none
        have hfm : (List.filterMapM (m := TLowerM) (fun x =>
            if ks.contains x.1 then
              match cx.ctorEntry? x.1 with
              | some (idx, entry) =>
                pure (some (Aiur.Generic.Pattern.construct (.named (enumName ind) []) (ctorNameOf idx entry.key) [], x.2))
              | none => pure none
            else pure none) (Lower.firstPerKey [] alts)) s1 =
            .ok ((Lower.firstPerKey [] alts).filterMap armFn, s1) := by
          have heqFn : (fun x : CtorKey × Lower.Expr =>
              if ks.contains x.1 then
                match cx.ctorEntry? x.1 with
                | some (idx, entry) =>
                  pure (f := TLowerM) (some (Aiur.Generic.Pattern.construct (.named (enumName ind) []) (ctorNameOf idx entry.key) [], x.2))
                | none => pure none
              else pure none) = (fun x => pure (armFn x)) := by
            funext ⟨k, body⟩; dsimp only [armFn]
            split
            · cases cx.ctorEntry? k <;> rfl
            · rfl
          rw [heqFn]
          exact filterMapM_pure_stateT armFn _ s1
        obtain ⟨arms, s2, hmap, hc⟩ := tBind_step_inv hc
        rw [hfm, Except.ok.injEq, Prod.mk.injEq] at hmap
        obtain ⟨rfl, rfl⟩ := hmap
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        refine ⟨hleFb, fun _ _ halts hd => ?_⟩
        have harms : isCleanNoU32Arms ((Lower.firstPerKey [] alts).filterMap armFn) = true := by
          rw [isCleanNoU32Arms_iff]
          intro a ha
          obtain ⟨⟨k, body⟩, hmem, hfa⟩ := List.mem_filterMap.mp ha
          have hbClean : isCleanNoU32 body = true := by
            rcases firstPerKey_mem [] alts (k, body) hmem with hnil | hm'
            · cases hnil
            · exact halts (k, body) hm'
          dsimp only [armFn] at hfa
          split at hfa
          · cases hce : cx.ctorEntry? k with
            | none => simp [hce] at hfa
            | some ie =>
              simp only [hce, Option.some.injEq] at hfa
              subst hfa
              exact ⟨rfl, hbClean⟩
          · cases hfa
        simp [matchE, vE, isCleanNoU32, isCleanNoU32Arms_append harms (hdfltClean hd)]
    | data did =>
      cases hD : cx.cert.data? did with
      | none => simp [hD, hfL, throw, throwThe, MonadExceptOf.throw] at hc
      | some D =>
        simp only [hD] at hc
        let armFn : CtorKey × Lower.Expr → Option (Lower.Pat × Lower.Expr) := fun (k, body) =>
          if D.ctors.any (·.1 == k) then
            match cx.ctorEntry? k with
            | some (idx, entry) =>
              some (.construct (.named (dataName did) []) (ctorNameOf idx entry.key)
                (List.replicate entry.arity .wildcard), body)
            | none => none
          else none
        have hfm : (List.filterMapM (m := TLowerM) (fun x =>
            if D.ctors.any (·.1 == x.1) then
              match cx.ctorEntry? x.1 with
              | some (idx, entry) =>
                pure (some (Aiur.Generic.Pattern.construct (.named (dataName did) []) (ctorNameOf idx entry.key)
                  (List.replicate entry.arity .wildcard), x.2))
              | none => pure none
            else pure none) (Lower.firstPerKey [] alts)) s1 =
            .ok ((Lower.firstPerKey [] alts).filterMap armFn, s1) := by
          have heqFn : (fun x : CtorKey × Lower.Expr =>
              if D.ctors.any (·.1 == x.1) then
                match cx.ctorEntry? x.1 with
                | some (idx, entry) =>
                  pure (f := TLowerM) (some (Aiur.Generic.Pattern.construct (.named (dataName did) []) (ctorNameOf idx entry.key)
                    (List.replicate entry.arity .wildcard), x.2))
                | none => pure none
              else pure none) = (fun x => pure (armFn x)) := by
            funext ⟨k, body⟩; dsimp only [armFn]
            split
            · cases cx.ctorEntry? k <;> rfl
            · rfl
          rw [heqFn]
          exact filterMapM_pure_stateT armFn _ s1
        obtain ⟨arms, s2, hmap, hc⟩ := tBind_step_inv hc
        rw [hfm, Except.ok.injEq, Prod.mk.injEq] at hmap
        obtain ⟨rfl, rfl⟩ := hmap
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        refine ⟨hleFb, fun _ _ halts hd => ?_⟩
        have hrep : ∀ n, isSimplePatList (List.replicate n (.wildcard : Lower.Pat)) = true := by
          intro n; induction n with
          | zero => rfl
          | succ n ih => simp [List.replicate_succ, isSimplePatList, isSimplePat, ih]
        have harms : isCleanNoU32Arms ((Lower.firstPerKey [] alts).filterMap armFn) = true := by
          rw [isCleanNoU32Arms_iff]
          intro a ha
          obtain ⟨⟨k, body⟩, hmem, hfa⟩ := List.mem_filterMap.mp ha
          have hbClean : isCleanNoU32 body = true := by
            rcases firstPerKey_mem [] alts (k, body) hmem with hnil | hm'
            · cases hnil
            · exact halts (k, body) hm'
          dsimp only [armFn] at hfa
          split at hfa
          · cases hce : cx.ctorEntry? k with
            | none => simp [hce] at hfa
            | some ie =>
              simp only [hce, Option.some.injEq] at hfa
              subst hfa
              exact ⟨by simp [isSimplePat, hrep], hbClean⟩
          · cases hfa
        simp [matchE, vE, isCleanNoU32, isCleanNoU32Arms_append harms (hdfltClean hd)]
    | obj =>
      obtain ⟨s2, hle2, _, hc⟩ := tMark_step_inv hc hfM
        (fun _ => by constructor <;> first | exact id | (intro _; rfl))
      obtain ⟨hle3, hc⟩ := tFreshLocal_step_inv hc hfF
      obtain ⟨zBody, s4, hz, hc⟩ := tBind_step_inv hc
      obtain ⟨sBody, s5, hs, hc⟩ := tBind_step_inv hc
      obtain ⟨eTr, s6, heTr, hc⟩ := tBind_step_inv hc
      obtain ⟨sTr, s7, hsTr, hc⟩ := tBind_step_inv hc
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨hle4, hcl4⟩ := hpick cx.P.known.natZero _ s4 zBody hz
      obtain ⟨hle5, hcl5⟩ := hpick cx.P.known.natSucc s4 s5 sBody hs
      obtain ⟨hle6, hcl6⟩ := hTrap cx retR "case on an erased value" s5 eTr s6 heTr
      obtain ⟨hle7, hcl7⟩ := hTrap cx retR "case on a string literal" s6 sTr s7 hsTr
      refine ⟨(((((hleFb.trans hle2).trans hle3).trans hle4).trans hle5).trans hle6).trans hle7,
        fun hr hdatas halts hd => ?_⟩
      have hfbc := hclFb hr hdatas hd
      have hca : isCleanNoU32Arms (Lower.ctorArms ⟨cx.P⟩ (Lower.firstPerKey [] alts)) = true := by
        apply isCleanNoU32Arms_ctorArms
        intro p hp
        rcases firstPerKey_mem [] alts p hp with hnil | hm'
        · cases hnil
        · exact halts p hm'
      have hmid : isCleanNoU32Arms
          [(pN (.bind (localName s2.nextLocal)),
              matchE (vE (localName s2.nextLocal)) [(.literal 0, zBody), (.wildcard, sBody)]),
           (pC "E" [], eTr),
           (pC "S" [.wildcard], sTr)] = true := by
        simp [isCleanNoU32Arms, pN, pC, matchE, vE, isSimplePat, isSimplePatList, isCleanNoU32,
          hcl4 hr hdatas halts hfbc, hcl5 hr hdatas halts hfbc,
          hcl6 hr hdatas, hcl7 hr hdatas]
      simp only [matchE, vE, isCleanNoU32, Bool.true_and]
      exact isCleanNoU32Arms_append (isCleanNoU32Arms_append hca hmid) (hdfltClean hd)
    | irr =>
      obtain ⟨hle, hcl⟩ := hTrap cx retR "case on erased value" s1 e st' hc
      exact ⟨hleFb.trans hle, fun hr hdatas _ _ => hcl hr hdatas⟩
    | w32 | w64 =>
      simp [hfL, throw, throwThe, MonadExceptOf.throw] at hc
  cases d with
  | some de =>
    obtain ⟨fb, s1, hfb, hc⟩ := tBind_step_inv h
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfb
    obtain ⟨rfl, rfl⟩ := hfb
    refine hcont de st hc ?_ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
      (TStateLe.refl _) (fun _ _ hd => hd de rfl)
    intro _ _ _ _ _ _ ht
    obtain ⟨_, hle, hcl⟩ := tTrapE_ok_inv ht (fun _ _ _ => rfl)
      (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
      (fun _ _ => rfl) (fun _ _ => rfl)
    exact ⟨hle, hcl⟩
  | none =>
    obtain ⟨fb, s1, hfb, hc⟩ := tBind_step_inv h
    obtain ⟨_, hle1, hcl1⟩ := tTrapE_ok_inv hfb (fun _ _ _ => rfl)
      (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
      (fun _ _ => rfl) (fun _ _ => rfl)
    refine hcont fb s1 hc ?_ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
      hle1 (fun hr hdatas _ => hcl1 hr hdatas)
    intro _ _ _ _ _ _ ht
    obtain ⟨_, hle, hcl⟩ := tTrapE_ok_inv ht (fun _ _ _ => rfl)
      (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
      (fun _ _ => rfl) (fun _ _ => rfl)
    exact ⟨hle, hcl⟩

private theorem bindTVm_mem : ∀ {vm : TVarMap} {ps : List Var} {nrs : List (String × Rep)}
    {p : Var × String × Rep}, p ∈ bindTVm vm ps nrs →
    p ∈ vm ∨ ∃ x ∈ ps, ∃ nr ∈ nrs, p = (x, nr)
  | _, [], _, _, hm => Or.inl hm
  | _, _ :: _, [], _, hm => Or.inl hm
  | vm, x :: xs, nr :: nrs, p, hm => by
    rcases bindTVm_mem (vm := (x, nr) :: vm) hm with h1 | ⟨y, hy, q, hq, rfl⟩
    · rcases List.mem_cons.mp h1 with rfl | hvm
      · exact Or.inr ⟨x, List.mem_cons_self, nr, List.mem_cons_self, rfl⟩
      · exact Or.inl hvm
    · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, q, List.mem_cons_of_mem _ hq, rfl⟩

/-- Every join-point entry in `jenv` has a non-U32 function name and core parameter reps. -/
def JEnvCoreOk (jenv : List TJEntry) : Prop :=
  ∀ ji ∈ jenv, isPeepholeU32Name ji.fnName = false ∧ ∀ pr ∈ ji.paramReps, isNatCoreRep pr = true

private theorem markRep_step_inv {fMR : Rep → TLowerM Unit} {r : Rep}
    {α : Type} {f : Unit → TLowerM α} {st st' : TState} {a : α}
    (h : (fMR r >>= f) st = .ok (a, st'))
    (hObj : ∀ st, fMR .obj st = .ok ((), { st with demand := { st.demand with needObj := true } }))
    (hW64 : ∀ st, fMR .w64 st = .ok ((), { st with demand := { st.demand with needU64Bitwise := true } }))
    (hOther : ∀ r st, r ≠ .obj → r ≠ .w64 → fMR r st = .ok ((), st)) :
    ∃ s1, TStateLe st s1 ∧ s1.nextLocal = st.nextLocal ∧ s1.nextJp = st.nextJp ∧
      f () s1 = .ok (a, st') := by
  obtain ⟨s1, hm, hnl, hnj, hlf, hd⟩ := markRep_poly fMR hObj hW64 hOther r st
  simp only [bind, StateT.bind, Except.bind, hm] at h
  exact ⟨s1, ⟨hnl ▸ Nat.le_refl _, hnj ▸ Nat.le_refl _, hlf, hd⟩, hnl, hnj, h⟩

private theorem forIn_markRep_step_inv {β α : Type} {g : β → Rep} {xs : List β}
    {fMR : Rep → TLowerM Unit} {f : PUnit → TLowerM α} {st st' : TState} {a : α}
    (h : ((forIn xs PUnit.unit (fun x _ => StateT.bind (fMR (g x)) fun _ =>
        StateT.pure (ForInStep.yield PUnit.unit)) : TLowerM PUnit) >>= f) st = .ok (a, st'))
    (hObj : ∀ st, fMR .obj st = .ok ((), { st with demand := { st.demand with needObj := true } }))
    (hW64 : ∀ st, fMR .w64 st = .ok ((), { st with demand := { st.demand with needU64Bitwise := true } }))
    (hOther : ∀ r st, r ≠ .obj → r ≠ .w64 → fMR r st = .ok ((), st)) :
    ∃ s1, TStateLe st s1 ∧ s1.nextLocal = st.nextLocal ∧ s1.nextJp = st.nextJp ∧
      f PUnit.unit s1 = .ok (a, st') := by
  obtain ⟨s1, hm, hnl, hnj, hlf, hd⟩ :=
    forIn_markRep_poly g fMR (markRep_poly fMR hObj hW64 hOther) xs st
  simp only [bind, StateT.bind, Except.bind, hm] at h
  exact ⟨s1, ⟨hnl ▸ Nat.le_refl _, hnj ▸ Nat.le_refl _, hlf, hd⟩, hnl, hnj, h⟩

private theorem tFreshJp_step_inv {m : TLowerM Nat}
    {α : Type} {f : Nat → TLowerM α} {st st' : TState} {a : α}
    (h : (m >>= f) st = .ok (a, st'))
    (heq : ∀ s, m s = .ok (s.nextJp, { s with nextJp := s.nextJp + 1 })) :
    TStateLe st { st with nextJp := st.nextJp + 1 } ∧
    f st.nextJp { st with nextJp := st.nextJp + 1 } = .ok (a, st') := by
  simp only [bind, StateT.bind, Except.bind, heq] at h
  exact ⟨⟨Nat.le_refl _, Nat.le_succ _, rfl, DemandLe.refl _⟩, h⟩

private theorem tFreshLocals_step_inv {fFL : Nat → TLowerM (List String)} {n : Nat}
    {α : Type} {f : List String → TLowerM α} {st st' : TState} {a : α}
    (h : (fFL n >>= f) st = .ok (a, st'))
    (h0 : ∀ st, fFL 0 st = .ok ([], st))
    (hS : ∀ k st, fFL (k + 1) st =
      (fFL k { st with nextLocal := st.nextLocal + 1 }).bind fun (t, s') =>
        .ok (localName st.nextLocal :: t, s')) :
    TStateLe st { st with nextLocal := st.nextLocal + n } ∧
    f ((List.range n).map (fun i => localName (st.nextLocal + i)))
      { st with nextLocal := st.nextLocal + n } = .ok (a, st') := by
  have hfl := freshLocals_poly fFL h0 hS n st
  simp only [bind, StateT.bind, Except.bind, hfl] at h
  exact ⟨⟨Nat.le_add_right _ _, Nat.le_refl _, rfl, DemandLe.refl _⟩, h⟩

private theorem tEmitLifted_step_inv {fE : Lower.Fn → TLowerM Unit} {g : Lower.Fn}
    {α : Type} {f : Unit → TLowerM α} {st st' : TState} {a : α}
    (h : (fE g >>= f) st = .ok (a, st'))
    (heq : ∀ g s, fE g s = .ok ((), { s with lifted := s.lifted ++ [g] })) :
    TCodeStateLe st { st with lifted := st.lifted ++ [g] } ∧
    f () { st with lifted := st.lifted ++ [g] } = .ok (a, st') := by
  simp only [bind, StateT.bind, Except.bind, heq] at h
  exact ⟨⟨Nat.le_refl _, Nat.le_refl _, fun _ hm => List.mem_append_left _ hm, DemandLe.refl _⟩, h⟩

private theorem mapM_tArgE_spec {cx : TCx} {vm : TVarMap} :
    ∀ {ls : List (Arg × Rep)} {s0 s1 : TState} {es : List Lower.Expr},
      (ls.mapM (m := TLowerM) fun x => tArgE cx vm x.1 x.2) s0 = .ok (es, s1) →
      TStateLe s0 s1 ∧
      ((∀ p ∈ vm, isNatCoreRep p.2.2 = true) →
       (∀ q ∈ ls, isNatCoreRep q.2 = true) →
       datasNatCoreReps cx.P cx.cert cx.feat = true →
       isCleanNoU32List es = true)
  | [], s0, s1, es, h => by
    simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨TStateLe.refl _, fun _ _ _ => rfl⟩
  | hd :: tl, s0, s1, es, h => by
    rw [List.mapM_cons] at h
    obtain ⟨e1, sa, h1, h⟩ := tBind_step_inv h
    obtain ⟨es2, sb, h2, h⟩ := tBind_step_inv h
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hle1, hcl1⟩ := tArgE_spec h1
    obtain ⟨hle2, hcl2⟩ := mapM_tArgE_spec h2
    exact ⟨hle1.trans hle2, fun hvm hls hdatas => by
      simp [isCleanNoU32List, hcl1 hvm (hls hd List.mem_cons_self) hdatas,
        hcl2 hvm (fun q hq => hls q (List.mem_cons_of_mem _ hq)) hdatas]⟩

private theorem isCleanNoU32List_append {a b : List Lower.Expr}
    (ha : isCleanNoU32List a = true) (hb : isCleanNoU32List b = true) :
    isCleanNoU32List (a ++ b) = true := by
  rw [isCleanNoU32List_iff] at ha hb ⊢
  intro x hx
  rcases List.mem_append.mp hx with h1 | h2
  · exact ha x h1
  · exact hb x h2

mutual

theorem tCodeE_spec {cx : TCx} {fid : FunId} {fsh : FunShapes} {retR : Rep} :
    ∀ {vm : TVarMap} {jenv : List TJEntry} {nz : List Var} {offs : OffMap}
      {c : Code} {st st' : TState} {e : Lower.Expr},
      tCodeE cx fid fsh retR vm jenv nz offs c st = .ok (e, st') →
      TCodeStateLe st st' ∧
      (codeNoWordPrims c = true →
       codeNatCoreReps cx.P cx.cert cx.feat fsh c = true →
       (∀ p ∈ vm, isNatCoreRep p.2.2 = true) →
       JEnvCoreOk jenv →
       isNatCoreRep retR = true →
       datasNatCoreReps cx.P cx.cert cx.feat = true →
       FunCoreRepsOk cx →
       (∀ g ∈ st.lifted, isCleanNoU32 g.body = true) →
       isCleanNoU32 e = true ∧ ∀ g ∈ st'.lifted, isCleanNoU32 g.body = true)
  | vm, jenv, nz, offs, .bind x r k, st, st', e, h => by
    unfold tCodeE at h
    obtain ⟨s1, hle1, _, _, h⟩ := markRep_step_inv h
      (fun _ => rfl) (fun _ => rfl)
      (fun r _ h1 h2 => by cases r <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2)
    obtain ⟨⟨re, xOff?⟩, s2, hr, h⟩ := tBind_step_inv h
    obtain ⟨hle3, h⟩ := tFreshLocal_step_inv h (fun _ => rfl)
    obtain ⟨ke, s4, hk, h⟩ := tBind_step_inv h
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hle2, hcl2, _⟩ := tRhsE_spec hr
    obtain ⟨hle4, hcl4⟩ := tCodeE_spec hk
    refine ⟨((hle1.trans hle2).trans hle3).toCodeLe.trans hle4,
      fun hnw hcore hvm hj hret hdatas hfc hlift => ?_⟩
    simp only [codeNoWordPrims, codeNatCoreReps, Bool.and_eq_true] at hnw hcore
    have hre := hcl2 (by cases r <;> exact hnw.1) hvm hcore.1 hdatas hfc
    have hvm' : ∀ p ∈ ((x, localName s2.nextLocal, cx.rep (fsh.var x)) :: vm), isNatCoreRep p.2.2 = true := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | htl
      · exact hcore.1
      · exact hvm p htl
    have hlift3 : ∀ g ∈ ({ s2 with nextLocal := s2.nextLocal + 1 }).lifted, isCleanNoU32 g.body = true := by
      intro g hg
      have hg' : g ∈ st.lifted := by simpa [hle2.lifted, hle1.lifted] using hg
      exact hlift g hg'
    obtain ⟨hke, hlift'⟩ := hcl4 hnw.2 hcore.2 hvm' hj hret hdatas hfc hlift3
    exact ⟨isCleanNoU32_letE hre hke, hlift'⟩
  | vm, jenv, nz, offs, .jp j ps isRec body k, st, st', e, h => by
    unfold tCodeE at h
    obtain ⟨hle1, h⟩ := tFreshJp_step_inv h (fun _ => rfl)
    obtain ⟨s2, hle2, _, _, h⟩ := forIn_markRep_step_inv (g := Prod.snd) h
      (fun _ => rfl) (fun _ => rfl)
      (fun r _ h1 h2 => by cases r <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2)
    obtain ⟨s3, hle3, _, _, h⟩ := forIn_markRep_step_inv (g := id) h
      (fun _ => rfl) (fun _ => rfl)
      (fun r _ h1 h2 => by cases r <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2)
    obtain ⟨s4, hle4, _, _, h⟩ := markRep_step_inv h
      (fun _ => rfl) (fun _ => rfl)
      (fun r _ h1 h2 => by cases r <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2)
    obtain ⟨hle5, h⟩ := tFreshLocals_step_inv h (fun _ => rfl) (fun _ _ => rfl)
    obtain ⟨bodyExpr, s6, hbody, h⟩ := tBind_step_inv h
    obtain ⟨hle7, h⟩ := tEmitLifted_step_inv h (fun _ _ => rfl)
    obtain ⟨hle6, hcl6⟩ := tCodeE_spec hbody
    obtain ⟨hle8, hcl8⟩ := tCodeE_spec h
    have hlePre : TStateLe st { s4 with nextLocal := s4.nextLocal + ps.length } :=
      (((hle1.trans hle2).trans hle3).trans hle4).trans hle5
    refine ⟨(hlePre.toCodeLe.trans hle6).trans (hle7.trans hle8),
      fun hnw hcore hvm hj hret hdatas hfc hlift => ?_⟩
    simp only [codeNoWordPrims, codeNatCoreReps, Bool.and_eq_true] at hnw hcore
    have hpsCore : ∀ p ∈ ps, isNatCoreRep (cx.rep (fsh.var p)) = true :=
      List.all_eq_true.mp hcore.1.1
    have hparamRepsCore : ∀ pr ∈ ps.map (fun p => cx.rep (fsh.var p)), isNatCoreRep pr = true := by
      intro pr hpr
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hpr
      exact hpsCore p hp
    have hBindEq : ∀ (fBV : TVarMap → List Var → List (String × Rep) → TVarMap),
        (∀ vm x xs nr nrs, fBV vm (x :: xs) (nr :: nrs) = fBV ((x, nr) :: vm) xs nrs) →
        (∀ vm nrs, fBV vm [] nrs = vm) →
        (∀ vm x xs, fBV vm (x :: xs) [] = vm) →
        ∀ p ∈ fBV vm ps (((List.range ps.length).map fun i => localName (s4.nextLocal + i)).zip
            (ps.map fun p => cx.rep (fsh.var p))),
          isNatCoreRep p.2.2 = true := by
      intro fBV hC hN1 hN2 p hp
      rw [bindTVm_poly fBV hC hN1 hN2] at hp
      rcases bindTVm_mem hp with h1 | ⟨_, _, nr, hnr, rfl⟩
      · exact hvm p h1
      · exact hparamRepsCore nr.2 (List.of_mem_zip hnr).2
    have hjiOk : isPeepholeU32Name (jpFunName fid st.nextJp) = false ∧
        ∀ pr ∈ ps.map (fun p => cx.rep (fsh.var p)), isNatCoreRep pr = true :=
      ⟨isPeepholeU32Name_jpFunName fid st.nextJp, hparamRepsCore⟩
    have hjCons : ∀ capVars, JEnvCoreOk (⟨j, jpFunName fid st.nextJp, capVars,
        ps.map (fun p => cx.rep (fsh.var p)), retR⟩ :: jenv) := by
      intro capVars ji hji
      rcases List.mem_cons.mp hji with rfl | htl
      · exact hjiOk
      · exact hj ji htl
    have hjBody : ∀ capVars, JEnvCoreOk (if isRec then
        ⟨j, jpFunName fid st.nextJp, capVars, ps.map (fun p => cx.rep (fsh.var p)), retR⟩ :: jenv
        else jenv) := by
      intro capVars; split
      · exact hjCons capVars
      · exact hj
    have hliftPre : ∀ g ∈ ({ s4 with nextLocal := s4.nextLocal + ps.length }).lifted,
        isCleanNoU32 g.body = true := by
      intro g hg
      have hg' : g ∈ st.lifted := by rw [← hlePre.lifted]; exact hg
      exact hlift g hg'
    obtain ⟨hbodyClean, hlift6⟩ := hcl6 hnw.1 hcore.1.2
      (hBindEq _ (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl))
      (hjBody _) hret hdatas hfc hliftPre
    apply hcl8 hnw.2 hcore.2 hvm (hjCons _) hret hdatas hfc
    intro g hg
    rcases List.mem_append.mp hg with h1 | h2
    · exact hlift6 g h1
    · simp only [List.mem_singleton] at h2; subst h2; exact hbodyClean
  | vm, jenv, nz, offs, .jmp j as, st, st', e, h => by
    unfold tCodeE at h
    cases hf : jenv.find? (·.id == j) with
    | none => simp only [hf] at h; exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    | some ji =>
      simp only [hf] at h
      by_cases har : (as.length == ji.paramReps.length) = true
      · simp only [har, ↓reduceIte] at h
        obtain ⟨argExprs, s1, hmap, h⟩ := tBind_step_inv h
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hle1, hcl1⟩ := mapM_tArgE_spec hmap
        refine ⟨hle1.toCodeLe, fun _ _ hvm hj _ hdatas _ hlift => ?_⟩
        obtain ⟨hnm, hprs⟩ := hj ji (List.mem_of_find?_eq_some hf)
        have hcapsClean : isCleanNoU32List (ji.capVars.map fun x => vE x.1) = true := by
          rw [isCleanNoU32List_iff]
          intro x hx
          obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
          rfl
        have hargsClean : isCleanNoU32List argExprs = true :=
          hcl1 hvm (fun q hq => hprs q.2 (List.of_mem_zip hq).2) hdatas
        exact ⟨isCleanNoU32_callE hnm (isCleanNoU32List_append hcapsClean hargsClean),
          fun g hg => hlift g (hle1.lifted ▸ hg)⟩
      · have harf : (as.length == ji.paramReps.length) = false := Bool.eq_false_iff.mpr har
        simp only [harf, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨_, _, h1, _⟩ := tBind_step_inv h
        exact False.elim (tLift_throw_elim h1 (fun _ _ => rfl))
  | vm, jenv, nz, offs, .case x alts d, st, st', e, h => by
    unfold tCodeE at h
    cases hlook : vm.lookup x with
    | none => simp only [hlook] at h; exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    | some nr =>
      rcases nr with ⟨nx, rx⟩
      simp only [hlook] at h
      obtain ⟨altExprs, s1, halts, h⟩ := tBind_step_inv h
      obtain ⟨dExpr, s2, hd, h⟩ := tBind_step_inv h
      obtain ⟨hle1, hcl1⟩ := tAltsE_spec halts
      obtain ⟨hle2, hcl2⟩ := tOptE_spec hd
      obtain ⟨hle3, hcl3⟩ := tCaseE_spec h
      refine ⟨(hle1.trans hle2).trans hle3.toCodeLe,
        fun hnw hcore hvm hj hret hdatas hfc hlift => ?_⟩
      simp only [codeNoWordPrims, codeNatCoreReps, Bool.and_eq_true] at hnw hcore
      obtain ⟨haltsClean, hlift1⟩ := hcl1 hnw.1 hcore.1 hvm hj hret hdatas hfc hlift
      obtain ⟨hdClean, hlift2⟩ := hcl2 hnw.2 hcore.2 hvm hj hret hdatas hfc hlift1
      exact ⟨hcl3 hret hdatas haltsClean hdClean, fun g hg => hlift2 g (hle3.lifted ▸ hg)⟩
  | vm, jenv, nz, offs, .ret a, st, st', e, h => by
    unfold tCodeE at h
    obtain ⟨hle, hcl⟩ := tArgE_spec h
    exact ⟨hle.toCodeLe, fun _ _ hvm _ hret hdatas _ hlift =>
      ⟨hcl hvm hret hdatas, fun g hg => hlift g (hle.lifted ▸ hg)⟩⟩
  | vm, jenv, nz, offs, .tcall f as, st, st', e, h => by
    unfold tCodeE at h
    cases hfun : cx.P.fun? f with
    | none => simp only [hfun] at h; exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
    | some fd =>
      simp only [hfun] at h
      by_cases hsz : f < cx.P.size
      · simp only [hsz, ↓reduceIte] at h
        by_cases har : (as.length == fd.params.length) = true
        · simp only [har, ↓reduceIte] at h
          obtain ⟨argEs, s1, hmap, h⟩ := tBind_step_inv h
          obtain ⟨hle1, hcl1⟩ := mapM_tArgE_spec hmap
          obtain ⟨hle2, hcl2⟩ := coerceE_spec h
          refine ⟨(hle1.trans hle2).toCodeLe, fun _ _ hvm _ hret hdatas hfc hlift => ?_⟩
          obtain ⟨hretCore, hparamCore⟩ := hfc f fd hfun hsz
          have hargsClean : isCleanNoU32List argEs = true := by
            apply hcl1 hvm _ hdatas
            intro q hq
            obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp (List.of_mem_zip hq).2
            rw [← hpeq]; exact hparamCore p hp
          exact ⟨hcl2 hretCore hret hdatas (isCleanNoU32_callE (isPeepholeU32Name_funName f) hargsClean),
            fun g hg => hlift g (hle1.lifted ▸ hle2.lifted ▸ hg)⟩
        · have harf : (as.length == fd.params.length) = false := Bool.eq_false_iff.mpr har
          simp only [harf, Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨_, _, h1, _⟩ := tBind_step_inv h
          exact False.elim (tLift_throw_elim h1 (fun _ _ => rfl))
      · simp only [hsz, ↓reduceIte] at h
        obtain ⟨_, _, h1, _⟩ := tBind_step_inv h
        exact False.elim (tLift_throw_elim h1 (fun _ _ => rfl))
  | vm, jenv, nz, offs, .trap, st, st', e, h => by
    unfold tCodeE at h
    obtain ⟨_, hle, hcl⟩ := tTrapE_ok_inv h (fun _ _ _ => rfl)
      (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
      (fun _ _ => rfl) (fun _ _ => rfl)
    exact ⟨hle.toCodeLe, fun _ _ _ _ hret hdatas _ hlift =>
      ⟨hcl hret hdatas, fun g hg => hlift g (hle.lifted ▸ hg)⟩⟩

theorem tAltsE_spec {cx : TCx} {fid : FunId} {fsh : FunShapes} {retR : Rep} :
    ∀ {vm : TVarMap} {jenv : List TJEntry} {nz : List Var} {offs : OffMap}
      {scrut : Var} {scrutR : Rep} {alts : List Alt} {st st' : TState}
      {res : List (CtorKey × Lower.Expr)},
      tAltsE cx fid fsh retR vm jenv nz offs scrut scrutR alts st = .ok (res, st') →
      TCodeStateLe st st' ∧
      (altsNoWordPrims alts = true →
       altsNatCoreReps cx.P cx.cert cx.feat fsh alts = true →
       (∀ p ∈ vm, isNatCoreRep p.2.2 = true) →
       JEnvCoreOk jenv →
       isNatCoreRep retR = true →
       datasNatCoreReps cx.P cx.cert cx.feat = true →
       FunCoreRepsOk cx →
       (∀ g ∈ st.lifted, isCleanNoU32 g.body = true) →
       (∀ p ∈ res, isCleanNoU32 p.2 = true) ∧ ∀ g ∈ st'.lifted, isCleanNoU32 g.body = true)
  | _, _, _, _, _, _, [], st, st', res, h => by
    simp only [tAltsE, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨TCodeStateLe.refl _, fun _ _ _ _ _ _ _ hlift => ⟨(fun _ hm => by cases hm), hlift⟩⟩
  | vm, jenv, nz, offs, scrut, scrutR, .mk k b :: rest, st, st', res, h => by
    unfold tAltsE at h
    obtain ⟨be, s1, hb, h⟩ := tBind_step_inv h
    obtain ⟨re, s2, hr, h⟩ := tBind_step_inv h
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hle1, hcl1⟩ := tCodeE_spec hb
    obtain ⟨hle2, hcl2⟩ := tAltsE_spec hr
    refine ⟨hle1.trans hle2, fun hnw hcore hvm hj hret hdatas hfc hlift => ?_⟩
    simp only [altsNoWordPrims, altsNatCoreReps, Bool.and_eq_true] at hnw hcore
    obtain ⟨hbe, hlift1⟩ := hcl1 hnw.1 hcore.1 hvm hj hret hdatas hfc hlift
    obtain ⟨hre, hlift2⟩ := hcl2 hnw.2 hcore.2 hvm hj hret hdatas hfc hlift1
    refine ⟨fun p hp => ?_, hlift2⟩
    rcases List.mem_cons.mp hp with rfl | htl
    · exact hbe
    · exact hre p htl

theorem tOptE_spec {cx : TCx} {fid : FunId} {fsh : FunShapes} {retR : Rep} :
    ∀ {vm : TVarMap} {jenv : List TJEntry} {nz : List Var} {offs : OffMap}
      {d : Option Code} {st st' : TState} {res : Option Lower.Expr},
      tOptE cx fid fsh retR vm jenv nz offs d st = .ok (res, st') →
      TCodeStateLe st st' ∧
      (optNoWordPrims d = true →
       optNatCoreReps cx.P cx.cert cx.feat fsh d = true →
       (∀ p ∈ vm, isNatCoreRep p.2.2 = true) →
       JEnvCoreOk jenv →
       isNatCoreRep retR = true →
       datasNatCoreReps cx.P cx.cert cx.feat = true →
       FunCoreRepsOk cx →
       (∀ g ∈ st.lifted, isCleanNoU32 g.body = true) →
       (∀ de, res = some de → isCleanNoU32 de = true) ∧ ∀ g ∈ st'.lifted, isCleanNoU32 g.body = true)
  | _, _, _, _, none, st, st', res, h => by
    simp only [tOptE, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨TCodeStateLe.refl _, fun _ _ _ _ _ _ _ hlift => ⟨(fun _ hm => by cases hm), hlift⟩⟩
  | vm, jenv, nz, offs, some c, st, st', res, h => by
    unfold tOptE at h
    obtain ⟨ce, s1, hc, h⟩ := tBind_step_inv h
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hle, hcl⟩ := tCodeE_spec hc
    refine ⟨hle, fun hnw hcore hvm hj hret hdatas hfc hlift => ?_⟩
    obtain ⟨hce, hlift1⟩ := hcl hnw hcore hvm hj hret hdatas hfc hlift
    exact ⟨fun de hde => by cases hde; exact hce, hlift1⟩

end

/-! ### `tFunE_spec`, `tEntryE_spec`, and `TypedLoweredWorld.hasFun` / `hasEntry` -/

theorem tFunE_spec {cx : TCx} {fid : FunId} {fd : Fun} {st st' : TState} {fns : List Lower.Fn}
    (h : tFunE cx fid fd st = .ok (fns, st')) :
    TStateLe st st' ∧
    let fsh := cx.funShapes fid
    let paramReps := (fd.params.map Prod.fst).map fun p => cx.rep (fsh.var p)
    let retR := cx.rep fsh.ret
    let pns := (List.range fd.params.length).map (fun k => localName (st.nextLocal + k))
    let initOffs : OffMap :=
      ((fd.params.map Prod.fst).zip (pns.zip paramReps)).filterMap fun (p, nm, r) =>
        match r with | .nat _ => some (p, (nm, 0)) | _ => none
    ∃ stBodyIn stBodyOut body,
      stBodyIn.nextLocal = st.nextLocal + fd.params.length ∧
      stBodyIn.lifted = [] ∧
      DemandLe st.demand stBodyIn.demand ∧
      tCodeE cx fid fsh retR (bindTVm [] (fd.params.map Prod.fst) (pns.zip paramReps))
        [] [] initOffs fd.body stBodyIn = .ok (body, stBodyOut) ∧
      DemandLe stBodyOut.demand st'.demand ∧
      fns = { name := funName fid
              params := (pns.zip paramReps).map fun (nm, r) => (nm, r.aiurTy)
              result := retR.aiurTy
              body := body
              isInline := shouldInlineFun cx.P cx.sched fid fd } :: stBodyOut.lifted ∧
      (natCoreProgram cx.P cx.cert = true → cx.feat = scanFeatures cx.P →
        cx.P.fun? fid = some fd → fid < cx.P.size →
        isCleanNoU32 body = true ∧ ∀ g ∈ stBodyOut.lifted, isCleanNoU32 g.body = true) := by
  unfold tFunE at h
  obtain ⟨s1, hle1, hnl1, _, h⟩ := forIn_markRep_step_inv (g := id) h
    (fun _ => rfl) (fun _ => rfl)
    (fun r _ h1 h2 => by cases r <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2)
  obtain ⟨s2, hle2, hnl2, _, h⟩ := markRep_step_inv h
    (fun _ => rfl) (fun _ => rfl)
    (fun r _ h1 h2 => by cases r <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2)
  obtain ⟨hle3, h⟩ := tFreshLocals_step_inv h (fun _ => rfl) (fun _ _ => rfl)
  obtain ⟨prevSt, s3, hget, h⟩ := tBind_step_inv h
  simp only [get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at hget
  obtain ⟨rfl, rfl⟩ := hget
  obtain ⟨_, s4, hmod, h⟩ := tBind_step_inv h
  simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at hmod
  obtain ⟨_, rfl⟩ := hmod
  have hnlEq : s2.nextLocal = st.nextLocal := hnl2.trans hnl1
  have hlifEq : s2.lifted = st.lifted := hle2.lifted.trans hle1.lifted
  rw [hnlEq, hlifEq] at h
  set pns := (List.range fd.params.length).map fun i => localName (st.nextLocal + i)
  set preps := (fd.params.map Prod.fst).map fun p => cx.rep ((cx.funShapes fid).var p)
  set initOffs : OffMap :=
    ((fd.params.map Prod.fst).zip (pns.zip preps)).filterMap
      fun (p, nm, r) => match r with | .nat _ => some (p, (nm, 0)) | _ => none
  have hCodeStep :
      ∀ {fBV : TVarMap → List Var → List (String × Rep) → TVarMap}
        {β : Type} {f : Lower.Expr → TLowerM β} {b : β} {sA sB : TState},
        (tCodeE cx fid (cx.funShapes fid) (cx.rep (cx.funShapes fid).ret)
          (fBV [] (fd.params.map Prod.fst) (pns.zip preps)) [] [] initOffs fd.body >>= f) sA = .ok (b, sB) →
        (∀ vm x xs nr nrs, fBV vm (x :: xs) (nr :: nrs) = fBV ((x, nr) :: vm) xs nrs) →
        (∀ vm nrs, fBV vm [] nrs = vm) →
        (∀ vm x xs, fBV vm (x :: xs) [] = vm) →
        ∃ body stOut,
          tCodeE cx fid (cx.funShapes fid) (cx.rep (cx.funShapes fid).ret)
            (bindTVm [] (fd.params.map Prod.fst) (pns.zip preps)) [] [] initOffs fd.body sA = .ok (body, stOut) ∧
          f body stOut = .ok (b, sB) := by
    intro fBV β f b sA sB hstep h1 h2 h3
    rw [bindTVm_poly fBV h1 h2 h3] at hstep
    exact tBind_step_inv hstep
  obtain ⟨body, stOut, hcode, h⟩ := hCodeStep h
    (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    pure, StateT.pure, Except.bind, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hleCode, hclCode⟩ := tCodeE_spec hcode
  have hlePre : TStateLe st { s2 with nextLocal := st.nextLocal + fd.params.length } := by
    have h3' : TStateLe s2 { s2 with nextLocal := st.nextLocal + fd.params.length } := by
      simpa [hnlEq] using hle3
    exact (hle1.trans hle2).trans h3'
  refine ⟨⟨Nat.le_trans hlePre.nextLocal hleCode.nextLocal,
           Nat.le_trans hlePre.nextJp hleCode.nextJp,
           rfl,
           hlePre.demand.trans hleCode.demand⟩,
          { s2 with nextLocal := st.nextLocal + fd.params.length, lifted := [] },
          stOut, body, rfl, rfl, hlePre.demand, hcode, DemandLe.refl _, rfl, ?_⟩
  intro hnc hfeat hfun hsz
  obtain ⟨_, _, hnw, hretCore, hparamCore, hcodeCore⟩ := natCoreProgram_funInfo hnc hfun hsz
  have hdatas := natCoreProgram_datasNatCoreReps hnc
  have hfc : FunCoreRepsOk cx := by
    intro f' fd' hfun' hsz'
    obtain ⟨_, _, _, hr, hp, _⟩ := natCoreProgram_funInfo hnc hfun' hsz'
    simp only [TCx.rep, TCx.funShapes, hfeat]; exact ⟨hr, hp⟩
  have hvmCore : ∀ p ∈ bindTVm [] (fd.params.map Prod.fst)
      (((List.range fd.params.length).map fun i => localName (st.nextLocal + i)).zip
        ((fd.params.map Prod.fst).map fun p => cx.rep ((cx.funShapes fid).var p))),
      isNatCoreRep p.2.2 = true := by
    intro p hp
    rcases bindTVm_mem hp with hnil | ⟨_, _, nr, hnr, rfl⟩
    · cases hnil
    · obtain ⟨q, hq, hqr⟩ := List.mem_map.mp (List.of_mem_zip hnr).2
      rw [← hqr]; simp only [TCx.rep, TCx.funShapes, hfeat]; exact hparamCore q hq
  exact hclCode hnw (by simp only [TCx.funShapes, hfeat]; exact hcodeCore) hvmCore (fun _ hm => by cases hm)
    (by simp only [TCx.rep, TCx.funShapes, hfeat]; exact hretCore)
    (by rw [hfeat]; exact hdatas) hfc (fun _ hm => by cases hm)

theorem tEntryE_spec {cx : TCx} {i : Nat} {f : FunId} {st st' : TState}
    {ef : Lower.Fn} {retR : Rep}
    (h : tEntryE cx i f st = .ok ((ef, retR), st')) :
    TStateLe st st' ∧
    ∃ fd st1 argEs,
      cx.P.fun? f = some fd ∧
      f < cx.P.size ∧
      retR = cx.rep (cx.funShapes f).ret ∧
      TStateLe st st1 ∧
      (fd.params.length > 0 → st1.demand.needCheckU56 = true) ∧
      ((List.range fd.params.length).zip
        ((fd.params.map Prod.fst).map fun p => cx.rep ((cx.funShapes f).var p))).mapM (m := TLowerM)
          (fun (j, pr) =>
            let pName := entryParamName j
            coerceE cx (.nat natLimit) pr (seqE (callE "check_u56" [vE pName]) (vE pName))) st1 =
        .ok (argEs, st') ∧
      ef = { name := entryName i
             params := (List.range fd.params.length).map fun j => (entryParamName j, (.field : Lower.Ty))
             result := retR.aiurTy
             body := callE (funName f) argEs
             isInline := false } := by
  unfold tEntryE at h
  cases hfun : cx.P.fun? f with
  | none => simp only [hfun] at h; exact False.elim (tLift_throw_elim h (fun _ _ => rfl))
  | some fd =>
    simp only [hfun] at h
    by_cases hsz : f < cx.P.size
    · simp only [hsz, ↓reduceIte] at h
      have hlistLe : ∀ (ls : List (Nat × Rep)) (s0 s1 : TState) (es : List Lower.Expr),
          (ls.mapM (m := TLowerM) fun (j, pr) =>
            coerceE cx (.nat natLimit) pr (seqE (callE "check_u56" [vE (entryParamName j)]) (vE (entryParamName j)))) s0 =
            .ok (es, s1) →
          TStateLe s0 s1 := by
        intro ls; induction ls with
        | nil =>
          intro s0 s1 es hm
          simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at hm
          obtain ⟨_, rfl⟩ := hm; exact TStateLe.refl _
        | cons hd tl ih =>
          intro s0 s1 es hm
          rw [List.mapM_cons] at hm
          obtain ⟨_, sa, h1, hm⟩ := tBind_step_inv hm
          obtain ⟨_, sb, h2, hm⟩ := tBind_step_inv hm
          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm
          obtain ⟨_, rfl⟩ := hm
          exact (coerceE_spec h1).1.trans (ih sa sb _ h2)
      by_cases hpos : fd.params.length > 0
      · simp only [hpos, ↓reduceIte] at h
        obtain ⟨s1, hle1, hs1Eq, h⟩ := tMark_step_inv h (fun _ _ => rfl)
          (fun _ => by constructor <;> first | exact id | (intro _; rfl))
        obtain ⟨argEs, s2, hmap, h⟩ := tBind_step_inv h
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        have hle2 := hlistLe _ s1 s2 argEs hmap
        exact ⟨hle1.trans hle2, fd, s1, argEs, rfl, hsz, rfl, hle1,
          fun _ => by rw [hs1Eq], hmap, rfl⟩
      · simp only [hpos, ↓reduceIte] at h
        obtain ⟨argEs, s2, hmap, h⟩ := tBind_step_inv h
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        have hle2 := hlistLe _ st s2 argEs hmap
        exact ⟨hle2, fd, st, argEs, rfl, hsz, rfl, TStateLe.refl _,
          fun hp => absurd hp hpos, hmap, rfl⟩
    · simp only [hsz, ↓reduceIte] at h
      obtain ⟨_, _, h1, _⟩ := tBind_step_inv h
      exact False.elim (tLift_throw_elim h1 (fun _ _ => rfl))

theorem TypedLoweredWorld.ctors_keys_nodup {F : Type} [Field F] [DecidableEq F]
    {P : Program} {cert : ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    {world : World F} (lw : TypedLoweredWorld P cert sched lp world) :
    (P.ctors.map (·.key)).Nodup :=
  (typedLowerProgram_inv lw.lowered).1

theorem TypedLoweredWorld.ctors_names_nodup {F : Type} [Field F] [DecidableEq F]
    {P : Program} {cert : ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    {world : World F} (lw : TypedLoweredWorld P cert sched lp world) :
    (objCtorNames P).Nodup :=
  (typedLowerProgram_inv lw.lowered).2.1

/-- Extract lowered function body, lifted join points, cleanliness, and `WorldHasFn`
from `TypedLoweredWorld` for any function `f` in `P`. -/
theorem TypedLoweredWorld.hasFun {F : Type} [Field F] [DecidableEq F]
    {P : Program} {cert : ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    {world : World F} (lw : TypedLoweredWorld P cert sched lp world)
    (hnc : natCoreProgram P cert = true)
    {f : FunId} {fd : Fun} (hfun : P.fun? f = some fd) (hsz : f < P.size) :
    let feat := scanFeatures P
    let cx : TCx := { P, cert, feat, sched }
    let fsh := cx.funShapes f
    let paramReps := (fd.params.map Prod.fst).map fun p => cx.rep (fsh.var p)
    let retR := cx.rep fsh.ret
    ∃ baseIdx stIn stOut body,
      let pns := (List.range fd.params.length).map (fun k => localName (baseIdx + k))
      let initOffs : OffMap :=
        ((fd.params.map Prod.fst).zip (pns.zip paramReps)).filterMap fun (p, nm, r) =>
          match r with | .nat _ => some (p, (nm, 0)) | _ => none
      stIn.nextLocal = baseIdx + fd.params.length ∧
      stIn.lifted = [] ∧
      tCodeE cx f fsh retR (bindTVm [] (fd.params.map Prod.fst) (pns.zip paramReps))
        [] [] initOffs fd.body stIn = .ok (body, stOut) ∧
      DemandLe stOut.demand lp.demand ∧
      isCleanNoU32 body = true ∧
      WorldHasFn world (qualified (funName f)) pns
        (qualifyExprF F (Peephole.rewriteExpr body)) ∧
      (∀ g ∈ stOut.lifted,
        isCleanNoU32 g.body = true ∧
        WorldHasFn world (qualified g.name) (g.params.map Prod.fst)
          (qualifyExprF F (Peephole.rewriteExpr g.body))) := by
  obtain ⟨_, _, stDatas, stFuns, stFinal, fnGroups, entries, _, hfg, hen, hdem, _, _, _, hfuncs⟩ :=
    typedLowerProgram_inv lw.lowered
  have hmemFL := funList_mem_of_fun? hfun hsz
  obtain ⟨hleFuns, _, hallFuns⟩ := mem_mapM_stateT
    (fun (p : FunId × Fun) _ _ _ _ hf => (tFunE_spec hf).1) hfg
  obtain ⟨hleEnt, _, _⟩ := mem_mapM_stateT
    (fun (p : Nat × FunId) _ _ _ _ he => (tEntryE_spec he).1) hen
  obtain ⟨fns, st1, st2, hfnsMem, hfunE, _, hle2Funs⟩ := hallFuns (f, fd) hmemFL
  obtain ⟨_, stIn, stOut, body, hnl, hlf, _, hcode, hdOut2, hfnsEq, hclean⟩ := tFunE_spec hfunE
  obtain ⟨hbodyClean, hliftClean⟩ := hclean hnc rfl hfun hsz
  have hdemLp : DemandLe stOut.demand lp.demand := by
    rw [hdem]
    exact (hdOut2.trans hle2Funs.demand).trans hleEnt.demand
  set feat := scanFeatures P
  set cx : TCx := { P, cert, feat, sched }
  set fsh := cx.funShapes f
  set paramReps := (fd.params.map Prod.fst).map fun p => cx.rep (fsh.var p)
  set retR := cx.rep fsh.ret
  set pns := (List.range fd.params.length).map (fun k => localName (st1.nextLocal + k))
  have hlenPns : pns.length = paramReps.length := by simp [pns, paramReps]
  have hparamsFst : ((pns.zip paramReps).map fun (nm, r) => (nm, r.aiurTy)).map Prod.fst = pns := by
    rw [List.map_map]
    change (pns.zip paramReps).map Prod.fst = pns
    exact List.map_fst_zip (Nat.le_of_eq hlenPns)
  refine ⟨st1.nextLocal, stIn, stOut, body, hnl, hlf, hcode, hdemLp, hbodyClean, ?_, ?_⟩
  · let mainFn : Lower.Fn := {
      name := funName f
      params := (pns.zip paramReps).map fun (nm, r) => (nm, r.aiurTy)
      result := retR.aiurTy
      body := body
      isInline := shouldInlineFun P sched f fd
    }
    have hmemMain : Peephole.rewriteFn mainFn ∈ lp.program.functions := by
      rw [hfuncs]
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_map_of_mem
      rw [List.mem_flatten]
      exact ⟨fns, hfnsMem, by rw [hfnsEq]; exact List.mem_cons_self⟩
    have hwf := lw.hasFn (Peephole.rewriteFn mainFn) hmemMain
    simpa [Peephole.rewriteFn, mainFn, hparamsFst] using hwf
  · intro g hg
    have hmemG : Peephole.rewriteFn g ∈ lp.program.functions := by
      rw [hfuncs]
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_map_of_mem
      rw [List.mem_flatten]
      exact ⟨fns, hfnsMem, by rw [hfnsEq]; exact List.mem_cons_of_mem _ hg⟩
    exact ⟨hliftClean g hg, lw.hasFn (Peephole.rewriteFn g) hmemG⟩

/-- Extract lowered entry wrapper `Prog::main<i>`, its `exportReps[i]?`, `needCheckU56` demand,
and `WorldHasFn` from `TypedLoweredWorld` for export `i`. -/
theorem TypedLoweredWorld.hasEntry {F : Type} [Field F] [DecidableEq F]
    {P : Program} {cert : ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    {world : World F} (lw : TypedLoweredWorld P cert sched lp world)
    {i : Nat} {f : FunId} (hexp : P.exports[i]? = some f) :
    let feat := scanFeatures P
    let cx : TCx := { P, cert, feat, sched }
    ∃ fd st1 st2 argEs,
      P.fun? f = some fd ∧
      f < P.size ∧
      lp.exportReps[i]? = some (cx.rep (cx.funShapes f).ret) ∧
      (fd.params.length > 0 → lp.demand.needCheckU56 = true) ∧
      ((List.range fd.params.length).zip
        ((fd.params.map Prod.fst).map fun p => cx.rep ((cx.funShapes f).var p))).mapM (m := TLowerM)
          (fun (j, pr) =>
            let pName := entryParamName j
            coerceE cx (.nat natLimit) pr (seqE (callE "check_u56" [vE pName]) (vE pName))) st1 =
        .ok (argEs, st2) ∧
      DemandLe st2.demand lp.demand ∧
      WorldHasFn world (qualified (entryName i))
        ((List.range fd.params.length).map entryParamName)
        (qualifyExprF F (callE (funName f) argEs)) := by
  obtain ⟨_, _, _, stFuns, stFinal, _, entries, _, _, hen, hdem, _, hexpReps, _, hfuncs⟩ :=
    typedLowerProgram_inv lw.lowered
  have hiLt : i < P.exports.length := (List.getElem?_eq_some_iff.mp hexp).1
  have hget : P.exports[i] = f := (List.getElem?_eq_some_iff.mp hexp).2
  have hzipGet : ((List.range P.exports.length).zip P.exports)[i]? = some (i, f) :=
    List.getElem?_eq_some_iff.mpr ⟨by simp [hiLt], by simp [hget]⟩
  obtain ⟨⟨ef, retR⟩, s0, s2, hentGet, hentE, _, hle2Final⟩ :=
    getElem?_mapM_stateT (fun (p : Nat × FunId) _ _ _ _ he => (tEntryE_spec he).1) hen i (i, f) hzipGet
  obtain ⟨hleEntry, fd, st1, argEs, hfun, hsz, rfl, hle01, hchk56, hmap, hefEq⟩ := tEntryE_spec hentE
  have hrepGet : lp.exportReps[i]? = some ((({ P, cert, feat := scanFeatures P, sched } : TCx).rep
      (({ P, cert, feat := scanFeatures P, sched } : TCx).funShapes f).ret)) := by
    rw [hexpReps, List.getElem?_map, hentGet]; rfl
  have hdem2 : DemandLe s2.demand lp.demand := by rw [hdem]; exact hle2Final.demand
  have hchk56Lp : fd.params.length > 0 → lp.demand.needCheckU56 = true := by
    intro hpos
    have h1 := hchk56 hpos
    have hmapLe : TStateLe st1 s2 := by
      have aux : ∀ (ls : List (Nat × Rep)) (sa sb : TState) (es : List Lower.Expr),
          (ls.mapM (m := TLowerM) fun (j, pr) =>
            coerceE { P, cert, feat := scanFeatures P, sched } (.nat natLimit) pr
              (seqE (callE "check_u56" [vE (entryParamName j)]) (vE (entryParamName j)))) sa =
            .ok (es, sb) →
          TStateLe sa sb := by
        intro ls; induction ls with
        | nil =>
          intro sa sb es hm
          simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at hm
          obtain ⟨_, rfl⟩ := hm; exact TStateLe.refl _
        | cons hd tl ih =>
          intro sa sb es hm
          rw [List.mapM_cons] at hm
          obtain ⟨_, s', h1', hm⟩ := tBind_step_inv hm
          obtain ⟨_, s'', h2', hm⟩ := tBind_step_inv hm
          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm
          obtain ⟨_, rfl⟩ := hm
          exact (coerceE_spec h1').1.trans (ih s' s'' _ h2')
      exact aux _ st1 s2 argEs hmap
    exact hdem2.needCheckU56 (hmapLe.demand.needCheckU56 h1)
  have hmemEf : ef ∈ lp.program.functions := by
    rw [hfuncs]
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨(ef, _), List.mem_of_getElem? hentGet, rfl⟩
  have hwf := lw.hasFn ef hmemEf
  rw [hefEq] at hwf
  refine ⟨fd, st1, s2, argEs, hfun, hsz, hrepGet, hchk56Lp, hmap, hdem2, ?_⟩
  simpa [List.map_map, Function.comp_def] using hwf

end NatCoreAndInversions

/-! ## Section 6: Typed Environments & Expression Backward Simulation -/

section TypedEnvsAndExprSim

variable {F : Type} [Field F] [DecidableEq F]

/-! ### `EvalExprN` Inversion & Pattern-Matching Helpers -/

theorem evalExprN_tuple0_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals (.tuple []) h r h') :
    r = .tuple [] ∧ h' = h := by
  cases ev with
  | tuple hargs =>
    cases hargs
    exact ⟨rfl, rfl⟩

theorem evalExprN_project_inv {world : World F} {d : Nat} {types : Types}
    {locals : Environment F Nat} {e : Aiur.Generic.Expr F} {i : Nat}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d types locals (.project e i) h r h') :
    ∃ vs, EvalExprN world d types locals e h (.tuple vs) h' ∧ vs[i]? = some r := by
  cases ev with
  | project he hget =>
    rename_i v
    cases v with
    | tuple vs =>
      simp only [projectValue] at hget
      cases hg : vs[i]? with
      | none => simp [hg] at hget
      | some x =>
        rw [hg] at hget
        simp only [pure, Except.pure, Except.ok.injEq] at hget
        subst hget
        exact ⟨vs, he, hg⟩
    | field _ | construct _ _ _ | ptr _ _ => simp [projectValue] at hget

theorem evalExprN_call1_inv {world : World F} {d : Nat} {locals : Environment F Nat}
    {name : String} {e1 : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d [] locals (.call name (some []) [e1]) h r h') :
    ∃ d' v1 hm, d' < d ∧
      EvalExprN world d [] locals e1 h v1 hm ∧
      EvalFnN world d' name [v1] hm r h' := by
  obtain ⟨d', vs, hm, hd', hargs, hcal⟩ := evalExprN_call_inv ev
  cases hargs with
  | cons ev1 htl =>
    cases htl
    exact ⟨d', _, hm, hd', ev1, hcal⟩

theorem evalExprN_call2_inv {world : World F} {d : Nat} {locals : Environment F Nat}
    {name : String} {e1 e2 : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d [] locals (.call name (some []) [e1, e2]) h r h') :
    ∃ d' v1 v2 h1 h2, d' < d ∧
      EvalExprN world d [] locals e1 h v1 h1 ∧
      EvalExprN world d [] locals e2 h1 v2 h2 ∧
      EvalFnN world d' name [v1, v2] h2 r h' := by
  obtain ⟨d', vs, hm, hd', hargs, hcal⟩ := evalExprN_call_inv ev
  cases hargs with
  | cons ev1 htl1 =>
    cases htl1 with
    | cons ev2 htl2 =>
      cases htl2
      exact ⟨d', _, _, _, _, hd', ev1, ev2, hcal⟩

theorem evalExprN_match_inv {world : World F} {d : Nat} {locals : Environment F Nat}
    {scrut : Aiur.Generic.Expr F}
    {arms : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d [] locals (.matchValue scrut arms) h r h') :
    ∃ v hm bs body,
      EvalExprN world d [] locals scrut h v hm ∧
      SourceSemantics.selectArm world [] hm v arms = .ok (some (bs, body)) ∧
      EvalExprN world d [] (bs ++ locals) body hm r h' := by
  cases ev with
  | matchValue evS hsel evB => exact ⟨_, _, _, _, evS, hsel, evB⟩

theorem evalExprN_match_lit_wild_inv {world : World F} {d : Nat} {locals : Environment F Nat}
    {scrut e1 e2 : Lower.Expr} {k : Nat} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExprN world d [] locals
      (qualifyExprF F (matchE scrut [(.literal k, e1), (.wildcard, e2)])) h r h') :
    ∃ v hm,
      EvalExprN world d [] locals (qualifyExprF F scrut) h v hm ∧
      ((v = .field (k : F) ∧ EvalExprN world d [] locals (qualifyExprF F e1) hm r h') ∨
       (v ≠ .field (k : F) ∧ EvalExprN world d [] locals (qualifyExprF F e2) hm r h')) := by
  simp only [matchE, qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
    Aiur.Generic.Pattern.map, List.map] at ev
  obtain ⟨v, hm, bs, body, evS, hsel, evB⟩ := evalExprN_match_inv ev
  cases v with
  | field x =>
    by_cases hx : x = (k : F)
    · subst hx
      simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, Aiur.Pattern.bindings] at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      exact ⟨.field (k : F), hm, evS, Or.inl ⟨rfl, evB⟩⟩
    · have hkx : (k : F) ≠ x := Ne.symm hx
      simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, Aiur.Pattern.bindings, hkx] at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      exact ⟨.field x, hm, evS, Or.inr ⟨fun h => hx (Value.field.inj h), evB⟩⟩
  | tuple _ | construct _ _ _ | ptr _ _ =>
    simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, Aiur.Pattern.bindings] at hsel
    obtain ⟨rfl, rfl⟩ := hsel
    exact ⟨_, hm, evS, Or.inr ⟨(fun h => by cases h), evB⟩⟩

omit [Field F] in
private theorem selectArm_append_inv_t {world : World F} {h : Heap F} {v : SourceValue F}
    {l1 l2 : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)}
    {b : Environment F Nat} {body : Aiur.Generic.Expr F}
    (hsel : SourceSemantics.selectArm world [] h v (l1 ++ l2) = .ok (some (b, body))) :
    SourceSemantics.selectArm world [] h v l1 = .ok (some (b, body)) ∨
    (SourceSemantics.selectArm world [] h v l1 = .ok none ∧
     SourceSemantics.selectArm world [] h v l2 = .ok (some (b, body))) := by
  induction l1 with
  | nil => exact Or.inr ⟨rfl, hsel⟩
  | cons arm rest ih =>
    rcases arm with ⟨pat, armBody⟩
    simp only [List.cons_append, SourceSemantics.selectArm, bind, Except.bind] at hsel ⊢
    cases hm : world.matchPattern [] h pat v with
    | error e => simp [hm] at hsel
    | ok res =>
      cases res with
      | some bs =>
        simp only [hm, pure, Except.pure] at hsel ⊢
        exact Or.inl hsel
      | none =>
        simp only [hm] at hsel ⊢
        exact ih hsel

omit [Field F] in
private theorem matchListWith_attach_eq_t {world : World F} {h : Heap F} :
    ∀ (ps : List (Aiur.Generic.Pattern F)) (vs : List (SourceValue F)),
      matchListWith (fun p => matchPatternWith world.constant world.constDepth [] h p.1) ps.attach vs =
      matchListWith (World.matchPattern world [] h) ps vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, v :: vs => by
    simp only [List.attach_cons, matchListWith]
    cases hm : matchPatternWith world.constant world.constDepth [] h p v with
    | error _ => simp [World.matchPattern, hm, bind, Except.bind]
    | ok r =>
      cases r with
      | none => simp [World.matchPattern, hm, bind, Except.bind]
      | some b =>
        simp only [World.matchPattern, hm, bind, Except.bind]
        have hmap : ∀ {α β : Type} (f : α → β) (l : List α)
            (g : β → SourceValue F → Except EvalError (Option (Environment F Nat)))
            (ws : List (SourceValue F)),
            matchListWith g (l.map f) ws = matchListWith (fun a => g (f a)) l ws := by
          intro α β f l g
          induction l with
          | nil => intro ws; cases ws <;> rfl
          | cons a tl ih =>
            intro ws; cases ws with
            | nil => rfl
            | cons w wt =>
              simp only [List.map_cons, matchListWith]
              cases g (f a) w with
              | error _ => rfl
              | ok r' => cases r' with
                | none => rfl
                | some _ => simp only [bind, Except.bind, ih]
        rw [hmap]
        have ih := matchListWith_attach_eq_t (world := world) (h := h) ps vs
        simp only [World.matchPattern, ih]

omit [Field F] in
private theorem matchListWith_replicate_wildcard_t {world : World F} {h : Heap F} :
    ∀ (n : Nat) (ps : List (SourceValue F)),
      ps.length = n →
      matchListWith (World.matchPattern world [] h) (List.replicate n .wildcard) ps = .ok (some [])
  | 0, [], _ => rfl
  | 0, _ :: _, hlen => by simp at hlen
  | _ + 1, [], hlen => by simp at hlen
  | n + 1, _ :: ps, hlen => by
    have hlen' : ps.length = n := by simpa using hlen
    simp only [List.replicate_succ, matchListWith, bind, Except.bind, pure, Except.pure]
    have hw : world.matchPattern [] h .wildcard ‹_› = .ok (some []) := by
      simp [World.matchPattern, matchPatternWith, pure, Except.pure]
    rw [hw, matchListWith_replicate_wildcard_t n ps hlen']
    rfl

omit [Field F] in
private theorem matchListWith_binds {world : World F} {h : Heap F} :
    ∀ (fvars : List String) (ws : List (SourceValue F)),
      ws.length = fvars.length →
      matchListWith (World.matchPattern world [] h)
        (fvars.map (Aiur.Generic.Pattern.bind : String → Aiur.Generic.Pattern F)) ws =
      .ok (some (fvars.zip ws))
  | [], [], _ => rfl
  | [], _ :: _, hlen => by simp at hlen
  | _ :: _, [], hlen => by simp at hlen
  | fv :: fvt, w :: wt, hlen => by
    have hlen' : wt.length = fvt.length := by simpa using hlen
    simp only [List.map_cons, List.zip_cons_cons, matchListWith, bind, Except.bind,
      pure, Except.pure]
    have hb : world.matchPattern [] h (.bind fv) w = .ok (some [(fv, w)]) := by
      simp [World.matchPattern, matchPatternWith, pure, Except.pure]
    rw [hb, matchListWith_binds fvt wt hlen']
    rfl

omit [Field F] in
private theorem matchListWith_projPats_gen {world : World F} {h : Heap F} (q : String) :
    ∀ (len start i : Nat) (ps : List (SourceValue F)),
      ps.length = len →
      matchListWith (World.matchPattern world [] h)
        ((List.range len).map fun j =>
          if start + j = i then (Aiur.Generic.Pattern.bind q : Aiur.Generic.Pattern F)
          else .wildcard) ps =
      .ok (some (if start ≤ i ∧ i < start + len then
        match ps[i - start]? with
        | some p => [(q, p)]
        | none => []
      else []))
  | 0, start, i, [], _ => by simp [matchListWith, pure, Except.pure]
  | 0, _, _, _ :: _, hlen => by simp at hlen
  | _ + 1, _, _, [], hlen => by simp at hlen
  | len + 1, start, i, p :: pt, hlen => by
    have hlen' : pt.length = len := by simpa using hlen
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have htailEq :
        (List.range len).map ((fun j => if start + j = i then
          (Aiur.Generic.Pattern.bind q : Aiur.Generic.Pattern F) else .wildcard) ∘ (· + 1)) =
        (List.range len).map (fun j => if (start + 1) + j = i then
          (Aiur.Generic.Pattern.bind q : Aiur.Generic.Pattern F) else .wildcard) := by
      apply List.map_congr_left
      intro j _
      have hadd : start + (j + 1) = (start + 1) + j := by omega
      simp [Function.comp, hadd]
    rw [htailEq]
    have ih := matchListWith_projPats_gen (world := world) (h := h) q len (start + 1) i pt hlen'
    by_cases hsi : start = i
    · subst hsi
      have hnot : ¬ (start + 1 ≤ start ∧ start < start + 1 + len) := by omega
      have hcond : start ≤ start ∧ start < start + (len + 1) := by omega
      have hbind : world.matchPattern [] h (.bind q) p = .ok (some [(q, p)]) := by
        simp [World.matchPattern, matchPatternWith, pure, Except.pure]
      simp only [Nat.add_zero, ↓reduceIte, matchListWith, hbind, ih, hnot, hcond, Nat.sub_self,
        List.getElem?_cons_zero, List.append_nil, bind, Except.bind, pure, Except.pure, and_self]
    · have hne0 : start + 0 ≠ i := by omega
      have hiff : (start ≤ i ∧ i < start + (len + 1)) ↔ (start + 1 ≤ i ∧ i < start + 1 + len) := by
        omega
      have hwild : world.matchPattern [] h .wildcard p = .ok (some []) := by
        simp [World.matchPattern, matchPatternWith, pure, Except.pure]
      simp only [hne0, ↓reduceIte, matchListWith, hwild, ih, List.nil_append,
        bind, Except.bind, pure, Except.pure]
      by_cases hc : start + 1 ≤ i ∧ i < start + 1 + len
      · have hc' : start ≤ i ∧ i < start + (len + 1) := hiff.mpr hc
        have hsub : i - start = (i - (start + 1)) + 1 := by omega
        simp [hc, hc', hsub]
      · have hc' : ¬ (start ≤ i ∧ i < start + (len + 1)) := fun h => hc (hiff.mp h)
        simp only [hc, hc', ↓reduceIte]

/-- Backward soundness of `TypedLower.constSubMatch`: matching `tmp` (holding `n < natLimit`)
against `0 => 0, ..., (k-1) => 0, _ => tmp - k` yields `n - k` for any `k < natLimit`. -/
theorem evalExprN_constSubMatch (fc : FieldCompatible64 F) {world : World F} {d : Nat}
    {locals : Environment F Nat} {tmp : String} {n k : Nat}
    {h h' : Heap F} {r : SourceValue F}
    (hn : n < natLimit) (hk : k < natLimit)
    (hloc : locals.find? (·.1 == tmp) = some (tmp, .field (n : F)))
    (ev : EvalExprN world d [] locals
      (qualifyExprF F
        (matchE (vE tmp)
          (((List.range k).map fun i => (Aiur.Generic.Pattern.literal i, litE 0)) ++
           [(.wildcard, subE (vE tmp) (litE k))]))) h r h') :
    r = .field ((n - k : Nat) : F) ∧ h' = h := by
  simp only [matchE, vE, subE, litE, qualifyExprF, qualifyExpr, qualifyPat,
    Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map_append, List.map_map,
    List.map_cons, List.map_nil] at ev
  obtain ⟨v, hm, bs, body, evS, hsel, evB⟩ := evalExprN_match_inv ev
  obtain ⟨hl, hmEq⟩ := evalExprN_var_inv evS
  cases hmEq
  rw [hloc, Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨_, hvEq⟩ := hl
  cases hvEq
  have hzeroArms : ∀ (ls : List Nat) (bs : Environment F Nat) (body : Aiur.Generic.Expr F),
      (∀ i ∈ ls, i < k) →
      (SourceSemantics.selectArm world [] h (.field (n : F))
        (ls.map fun (i : Nat) => (Aiur.Generic.Pattern.literal (i : F), Aiur.Generic.Expr.literal (0 : F))) =
          .ok (some (bs, body)) →
        bs = [] ∧ body = .literal (0 : F) ∧ ∃ i ∈ ls, (n : F) = (i : F)) ∧
      (SourceSemantics.selectArm world [] h (.field (n : F))
        (ls.map fun (i : Nat) => (Aiur.Generic.Pattern.literal (i : F), Aiur.Generic.Expr.literal (0 : F))) =
          .ok none →
        ∀ i ∈ ls, (n : F) ≠ (i : F)) := by
    intro ls
    induction ls with
    | nil =>
      intro bs body _
      exact ⟨(fun h0 => by cases h0), (fun _ _ hm => by cases hm)⟩
    | cons a tl ih =>
      intro bs body hlt
      constructor
      · intro h0
        by_cases heq : (n : F) = (a : F)
        · simp [List.map_cons, SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
            Aiur.Pattern.bindings, heq] at h0
          obtain ⟨rfl, rfl⟩ := h0
          exact ⟨rfl, rfl, a, List.mem_cons_self, heq⟩
        · have hne' : (a : F) ≠ (n : F) := Ne.symm heq
          simp [List.map_cons, SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
            Aiur.Pattern.bindings, hne'] at h0
          obtain ⟨hbs, hbd, i, hi, hieq⟩ :=
            (ih bs body (fun j hj => hlt j (List.mem_cons_of_mem _ hj))).1 h0
          exact ⟨hbs, hbd, i, List.mem_cons_of_mem _ hi, hieq⟩
      · intro h0 i hi
        by_cases heq : (n : F) = (a : F)
        · simp [List.map_cons, SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
            Aiur.Pattern.bindings, heq] at h0
        · have hne' : (a : F) ≠ (n : F) := Ne.symm heq
          simp [List.map_cons, SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
            Aiur.Pattern.bindings, hne'] at h0
          rcases List.mem_cons.mp hi with rfl | htl
          · exact heq
          · exact (ih [] (.literal 0) (fun j hj => hlt j (List.mem_cons_of_mem _ hj))).2 h0 i htl
  have hmapEq :
      List.map
        ((fun a => (Aiur.Generic.Pattern.map Nat.cast a.1, Aiur.Generic.Expr.map Nat.cast a.2)) ∘
          (fun a => (qualifyPat a.1, qualifyExpr a.2)) ∘
          fun i => (Aiur.Generic.Pattern.literal i, Aiur.Generic.Expr.literal (0 : Nat)))
        (List.range k) =
      (List.range k).map fun (i : Nat) => (Aiur.Generic.Pattern.literal (i : F), Aiur.Generic.Expr.literal (0 : F)) := by
    apply List.map_congr_left
    intro i _; simp [qualifyPat, qualifyExpr, Aiur.Generic.Pattern.map, Aiur.Generic.Expr.map]
  rw [hmapEq] at hsel
  rcases selectArm_append_inv_t hsel with hhit | ⟨hmiss, hwild⟩
  · obtain ⟨rfl, rfl, i, hiMem, hiEq⟩ :=
      (hzeroArms (List.range k) _ _ (fun j hj => List.mem_range.mp hj)).1 hhit
    have hiLt : i < k := List.mem_range.mp hiMem
    have hni : n = i := fc.natCast_inj56 hn (lt_trans hiLt hk) hiEq
    subst hni
    obtain ⟨rfl, hh'⟩ := evalExprN_literal_inv evB
    have hsub0 : n - k = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hiLt)
    exact ⟨by simp [hsub0], hh'⟩
  · have hneAll := (hzeroArms (List.range k) [] (.literal 0) (fun j hj => List.mem_range.mp hj)).2 hmiss
    have hkn : k ≤ n := by
      by_contra hlt
      have hnLt : n < k := Nat.lt_of_not_le hlt
      exact hneAll n (List.mem_range.mpr hnLt) rfl
    simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith] at hwild
    obtain ⟨rfl, rfl⟩ := hwild
    obtain ⟨vl, vr, hm1, evl, evr, hsub⟩ := evalExprN_binary_inv evB
    obtain ⟨hll, hm1Eq⟩ := evalExprN_var_inv evl
    cases hm1Eq
    simp only [List.nil_append, hloc, Option.some.injEq, Prod.mk.injEq] at hll
    obtain ⟨_, hvlEq⟩ := hll
    cases hvlEq
    obtain ⟨hvrEq, hh'Eq⟩ := evalExprN_literal_inv evr
    cases hvrEq; cases hh'Eq
    simp only [evalBinOp, Except.ok.injEq] at hsub
    rw [← hsub, Nat.cast_sub hkn]
    exact ⟨rfl, rfl⟩

private theorem selectArm_ctorArms_miss_t {P : Program} {world : World F} {h : Heap F}
    {cname : String} {ps : List (SourceValue F)}
    (hmiss : ∀ idx k, ctorNameOf idx k ≠ cname) :
    ∀ (xs : List (CtorKey × Lower.Expr)),
      SourceSemantics.selectArm world [] h (.construct objQName cname ps)
        ((Lower.ctorArms ⟨P⟩ xs).map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) = .ok none
  | [] => rfl
  | (k, body) :: rest => by
    unfold Lower.ctorArms
    cases hc : (Lower.Cx.mk P).ctorEntry? k with
    | none => exact selectArm_ctorArms_miss_t hmiss rest
    | some p =>
      rcases p with ⟨idx, entry⟩
      have hne : cname ≠ ctorNameOf idx entry.key := Ne.symm (hmiss idx entry.key)
      have hbne : (cname != ctorNameOf idx entry.key) = true := bne_iff_ne.mpr hne
      simp only [List.map_cons, pC, SourceSemantics.selectArm, qualifyPatF, qualifyPat,
        qualifyTy, objTy, qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol, hbne,
        Bool.or_true, Bool.true_or, ↓reduceIte, bind, Except.bind, pure, Except.pure]
      exact selectArm_ctorArms_miss_t hmiss rest

private theorem selectArm_ctorArms_ctor_t {P : Program} {world : World F} {h : Heap F}
    (hnd : (objCtorNames P).Nodup) (hkeys : (P.ctors.map (·.key)).Nodup)
    {idx : Nat} {entry : Lam.CtorInfo} {ps : List (SourceValue F)}
    (atIdx : P.ctors[idx]? = some entry) (hlen : ps.length = entry.arity) :
    ∀ (xs : List (CtorKey × Lower.Expr)),
      SourceSemantics.selectArm world [] h (.construct objQName (ctorNameOf idx entry.key) ps)
        ((Lower.ctorArms ⟨P⟩ xs).map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) =
      .ok ((xs.find? (·.1 == entry.key)).map fun p => ([], qualifyExprF F p.2))
  | [] => rfl
  | (k, body) :: rest => by
    unfold Lower.ctorArms
    by_cases hk : k = entry.key
    · subst hk
      have hc : (Lower.Cx.mk P).ctorEntry? entry.key = some (idx, entry) :=
        ctorEntry?_complete hkeys atIdx
      simp only [hc, List.map_cons, List.find?_cons, beq_self_eq_true, Option.map_some]
      have hrepMap :
          List.map (Aiur.Generic.Pattern.map Nat.cast)
            (List.map qualifyPat (List.replicate entry.arity (Aiur.Generic.Pattern.wildcard : Lower.Pat))) =
          List.replicate entry.arity (Aiur.Generic.Pattern.wildcard : Aiur.Generic.Pattern F) := by
        simp [List.map_replicate, qualifyPat, Aiur.Generic.Pattern.map]
      simp only [pC, SourceSemantics.selectArm, qualifyPatF, qualifyPat, qualifyTy, objTy,
        qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith,
        constructorName, Ty.subst, Ty.toCore, Instance.symbol, List.map_nil, List.isEmpty_nil,
        ↓reduceIte, hrepMap, List.length_replicate, hlen, bne_self_eq_false, Bool.or_self,
        Bool.false_eq_true, bind, Except.bind, pure, Except.pure]
      rw [matchListWith_attach_eq_t, matchListWith_replicate_wildcard_t entry.arity ps hlen]
    · have hbeq : (k == entry.key) = false := beq_false_of_ne hk
      simp only [List.find?_cons, hbeq]
      cases hc : (Lower.Cx.mk P).ctorEntry? k with
      | none => exact selectArm_ctorArms_ctor_t hnd hkeys atIdx hlen rest
      | some p =>
        rcases p with ⟨idx', entry'⟩
        obtain ⟨hget', hkey'⟩ := ctorEntry?_sound hc
        have hneName : ctorNameOf idx entry.key ≠ ctorNameOf idx' entry'.key := by
          intro heq
          obtain ⟨_, hentryEq⟩ := ctorNameOf_inj_of_nodup hnd atIdx hget' heq
          exact hk (hkey'.symm.trans (congrArg Lam.CtorInfo.key hentryEq.symm))
        have hbne : (ctorNameOf idx entry.key != ctorNameOf idx' entry'.key) = true :=
          bne_iff_ne.mpr hneName
        simp only [List.map_cons, pC, SourceSemantics.selectArm, qualifyPatF, qualifyPat,
          qualifyTy, objTy, qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol, hbne,
          Bool.or_true, Bool.true_or, ↓reduceIte, bind, Except.bind, pure, Except.pure]
        exact selectArm_ctorArms_ctor_t hnd hkeys atIdx hlen rest

/-! ### `Shape` / `RhsOk` / `boolEnum?` / `ctorInfo?` Helpers -/

private theorem shape_le_data_inv {σ : Shape} {d : Nat} (hle : σ.le (.data d) = true) :
    σ = .data d := by
  cases σ <;> simp [Shape.le] at hle
  subst hle; rfl

private theorem shape_le_enum_inv {σ : Shape} {ind : Src.CId} (hle : σ.le (.enum ind) = true) :
    σ = .enum ind := by
  cases σ <;> simp [Shape.le] at hle
  subst hle; rfl

private theorem repOf_eq_data_inv {P : Program} {cert : ShapeCert} {feat : Features}
    {σ : Shape} {d : Nat} (h : repOf P cert feat σ = .data d) :
    σ = .data d ∧ validData P cert d = true := by
  cases σ with
  | data d' =>
    simp only [repOf] at h
    split at h
    · cases h; exact ⟨rfl, ‹_›⟩
    · cases h
  | natLt _ =>
    simp only [repOf] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h <;> cases h
  | «enum» _ => simp only [repOf] at h; split at h <;> cases h
  | word w => cases w <;> cases h
  | any | irr | nat | «fn» _ _ | inter _ _ | arr _ _ => cases h

private theorem repOf_eq_enum_inv {P : Program} {cert : ShapeCert} {feat : Features}
    {σ : Shape} {ind : Src.CId} (h : repOf P cert feat σ = .enum ind) :
    σ = .enum ind ∧ validEnum P cert ind = true := by
  cases σ with
  | «enum» ind' =>
    simp only [repOf] at h
    split at h
    · cases h; exact ⟨rfl, ‹_›⟩
    · cases h
  | natLt _ =>
    simp only [repOf] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h <;> cases h
  | data _ => simp only [repOf] at h; split at h <;> cases h
  | word w => cases w <;> cases h
  | any | irr | nat | «fn» _ _ | inter _ _ | arr _ _ => cases h

private theorem rhsOk_ctor_data_inv {P : Program} {cert : ShapeCert} {fsh : FunShapes}
    {c : CtorInfo} {as : List Arg} {d : Nat}
    (h : Fir.Shape.RhsOk P cert fsh (.ctor c as) (.data d)) :
    ∃ D fl, cert.data? d = some D ∧ (c.key, fl) ∈ D.ctors ∧ Fir.Shape.ArgsOk fsh as fl := by
  generalize hr : Rhs.ctor c as = r at h
  generalize hτ : Shape.data d = τ at h
  induction h with
  | ctorData hD hmem hargs =>
    cases hr; cases hτ; exact ⟨_, _, hD, hmem, hargs⟩
  | weaken _ hle ih =>
    subst hτ
    have hσ := shape_le_data_inv hle
    exact ih hr hσ.symm
  | _ => cases hr <;> cases hτ

private theorem rhsOk_ctor_enum_inv {P : Program} {cert : ShapeCert} {fsh : FunShapes}
    {c : CtorInfo} {as : List Arg} {ind : Src.CId}
    (h : Fir.Shape.RhsOk P cert fsh (.ctor c as) (.enum ind)) :
    ∃ ks, as = [] ∧ cert.enum? ind = some ks ∧ c.key ∈ ks := by
  generalize hr : Rhs.ctor c as = r at h
  generalize hτ : Shape.enum ind = τ at h
  induction h with
  | ctorEnum hE hmem =>
    cases hr; cases hτ; exact ⟨_, rfl, hE, hmem⟩
  | weaken _ hle ih =>
    subst hτ
    have hσ := shape_le_enum_inv hle
    exact ih hr hσ.symm
  | _ => cases hr <;> cases hτ

private theorem paramsOk_eq_map {fsh : FunShapes} :
    ∀ {ps : List Var} {σs : List Shape},
      Fir.Shape.ParamsOk fsh ps σs → σs = ps.map fsh.var
  | _, _, .nil => rfl
  | _, _, .cons tl => congrArg (List.cons _) (paramsOk_eq_map tl)

private theorem ctorInfo?_of_ctorEntry? {P : Program}
    (hkeys : (P.ctors.map (·.key)).Nodup) {k : CtorKey} {idx : Nat} {entry : Lam.CtorInfo}
    (hc : Lower.ctorEntry? P k = some (idx, entry)) :
    ∃ c, P.ctorInfo? k = some c ∧ c.key = k ∧ c.nobj = entry.arity := by
  obtain ⟨hget, hkey⟩ := ctorEntry?_sound hc
  unfold Program.ctorInfo? Fir.CtorInfo.ofKey
  cases hf : P.ctors.find? (·.key == k) with
  | none =>
    have hmem := List.mem_of_getElem? hget
    have := List.find?_eq_none.mp hf entry hmem
    simp [hkey] at this
  | some e' =>
    have hmem' := List.mem_of_find?_eq_some hf
    have hk' : e'.key = k := beq_iff_eq.mp (by simpa using List.find?_some hf)
    obtain ⟨j, hjLt, hjEq⟩ := List.mem_iff_getElem.mp hmem'
    have hget' : P.ctors[j]? = some e' := List.getElem?_eq_some_iff.mpr ⟨hjLt, hjEq⟩
    have hiLt : idx < P.ctors.length := (List.getElem?_eq_some_iff.mp hget).1
    have hEqIdx : idx = j := by
      have h1 : (P.ctors.map (·.key))[idx]'(by simp [hiLt]) = k := by
        simp [(List.getElem?_eq_some_iff.mp hget).2, hkey]
      have h2 : (P.ctors.map (·.key))[j]'(by simp [hjLt]) = k := by
        simp [hjEq, hk']
      have hfin : (⟨idx, by simp [hiLt]⟩ : Fin (P.ctors.map (·.key)).length) = ⟨j, by simp [hjLt]⟩ :=
        (List.nodup_iff_injective_getElem.mp hkeys) (h1.trans h2.symm)
      exact congrArg Fin.val hfin
    subst hEqIdx
    rw [hget] at hget'; cases hget'
    exact ⟨_, rfl, rfl, rfl⟩

private theorem boolEnum?_sound {cx : TCx} {ind : Src.CId} {ttNm ffNm : String}
    (h : cx.boolEnum? = some (ind, ttNm, ffNm)) :
    ∃ tt ff it et if_ ef,
      cx.P.known.boolTrue = some tt ∧ cx.P.known.boolFalse = some ff ∧
      cx.ctorEntry? tt = some (it, et) ∧ cx.ctorEntry? ff = some (if_, ef) ∧
      et.arity = 0 ∧ ef.arity = 0 ∧
      ttNm = ctorNameOf it et.key ∧ ffNm = ctorNameOf if_ ef.key := by
  unfold TCx.boolEnum? at h
  cases htt : cx.P.known.boolTrue with
  | none => simp [htt] at h
  | some tt =>
    cases hff : cx.P.known.boolFalse with
    | none => simp [htt, hff] at h
    | some ff =>
      cases hct : cx.ctorEntry? tt with
      | none => simp [htt, hff, hct] at h
      | some pit =>
        rcases pit with ⟨it, et⟩
        cases hcf : cx.ctorEntry? ff with
        | none => simp [htt, hff, hcf] at h
        | some pif =>
          rcases pif with ⟨if_, ef⟩
          simp only [htt, hff, hct, hcf, bind, Option.bind] at h
          by_cases har : (et.arity == 0 && ef.arity == 0) = true
          · simp only [har, ↓reduceIte] at h
            cases hfind : cx.cert.enums.find? (fun e => validEnum cx.P cx.cert e.1 && e.2.contains tt && e.2.contains ff) with
            | none => rw [hfind] at h; cases h
            | some pk =>
              rw [hfind] at h
              simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              simp only [Bool.and_eq_true, beq_iff_eq] at har
              exact ⟨tt, ff, it, et, if_, ef, rfl, rfl, hct, hcf, har.1, har.2, rfl, rfl⟩
          · simp [har] at h

private theorem boolNames_sound {P : Program} {ttNm ffNm : String}
    (h : (Lower.Cx.mk P).boolNames = some (ttNm, ffNm)) :
    ∃ tt ff it et if_ ef,
      P.known.boolTrue = some tt ∧ P.known.boolFalse = some ff ∧
      Lower.ctorEntry? P tt = some (it, et) ∧ Lower.ctorEntry? P ff = some (if_, ef) ∧
      et.arity = 0 ∧ ef.arity = 0 ∧
      ttNm = ctorNameOf it et.key ∧ ffNm = ctorNameOf if_ ef.key := by
  unfold Lower.Cx.boolNames at h
  cases htt : P.known.boolTrue with
  | none => simp [htt] at h
  | some tt =>
    cases hff : P.known.boolFalse with
    | none => simp [htt, hff] at h
    | some ff =>
      cases hct : (Lower.Cx.mk P).ctorEntry? tt with
      | none => simp [htt, hff, hct] at h
      | some pit =>
        rcases pit with ⟨it, et⟩
        cases hcf : (Lower.Cx.mk P).ctorEntry? ff with
        | none => simp [htt, hff, hcf] at h
        | some pif =>
          rcases pif with ⟨if_, ef⟩
          simp only [htt, hff, hct, hcf, bind, Option.bind] at h
          by_cases har : (et.arity == 0 && ef.arity == 0) = true
          · simp only [har, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [Bool.and_eq_true, beq_iff_eq] at har
            exact ⟨tt, ff, it, et, if_, ef, rfl, rfl, hct, hcf, har.1, har.2, rfl, rfl⟩
          · simp [har] at h

end TypedEnvsAndExprSim

section TypedEnvsOnly

variable {F : Type} [Field F]

/-! ### Typed Environment, Offset, Non-Zero, and Join-Point Stack Invariants -/

/-- Parallel list of `TVR` judgments for parameter / argument lists. -/
inductive TVRs (P : Program) (cert : ShapeCert) (feat : Features) (h : Heap F) :
    List Rep → List Fir.Val → List (SourceValue F) → Prop where
  | nil : TVRs P cert feat h [] [] []
  | cons {r : Rep} {rs : List Rep} {v : Fir.Val} {vs : List Fir.Val}
      {w : SourceValue F} {ws : List (SourceValue F)} :
      TVR P cert feat h r v w → TVRs P cert feat h rs vs ws →
      TVRs P cert feat h (r :: rs) (v :: vs) (w :: ws)

theorem TVRs.extend {P : Program} {cert : ShapeCert} {feat : Features} {h h' : Heap F}
    (ext : Heap.Extends h h') :
    ∀ {rs : List Rep} {vs : List Fir.Val} {ws : List (SourceValue F)},
      TVRs P cert feat h rs vs ws → TVRs P cert feat h' rs vs ws
  | _, _, _, .nil => .nil
  | _, _, _, .cons hd tl => .cons (hd.extend ext) (tl.extend ext)

theorem TVRs.length_eq {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F} :
    ∀ {rs : List Rep} {vs : List Fir.Val} {ws : List (SourceValue F)},
      TVRs P cert feat h rs vs ws → rs.length = vs.length ∧ vs.length = ws.length
  | _, _, _, .nil => ⟨rfl, rfl⟩
  | _, _, _, .cons _ tl =>
    let ⟨h1, h2⟩ := tl.length_eq
    ⟨congrArg Nat.succ h1, congrArg Nat.succ h2⟩

/-- Typed lexical environment relation: every variable in `vm` carries its exact
`repOf (fsh.var x)`, and whenever its Aiur local name is bound in `locals` (including
after capture filtering), `ρ` maps `x` to a `TVR`-related `Fir.Val`. -/
structure TEnvRel (P : Program) (cert : ShapeCert) (feat : Features) (h : Heap F)
    (fsh : FunShapes) (vm : TVarMap) (ρ : Env) (locals : Environment F Nat) : Prop where
  rep_eq : ∀ x nx r, vm.lookup x = some (nx, r) → r = repOf P cert feat (fsh.var x)
  rel : ∀ x nx r w, vm.lookup x = some (nx, r) →
    locals.find? (·.1 == nx) = some (nx, w) →
    ∃ v, ρ.get? x = some v ∧ TVR P cert feat h r v w

theorem TEnvRel.extend {P : Program} {cert : ShapeCert} {feat : Features} {h h' : Heap F}
    (ext : Heap.Extends h h') {fsh : FunShapes} {vm : TVarMap} {ρ : Env}
    {locals : Environment F Nat} (hr : TEnvRel P cert feat h fsh vm ρ locals) :
    TEnvRel P cert feat h' fsh vm ρ locals where
  rep_eq := hr.rep_eq
  rel x nx r w hlook hloc := by
    obtain ⟨v, hρ, htvr⟩ := hr.rel x nx r w hlook hloc
    exact ⟨v, hρ, htvr.extend ext⟩

private theorem tlookup_mem_names {vm : TVarMap} {x : Var} {nx : String} {r : Rep}
    (h : vm.lookup x = some (nx, r)) : nx ∈ vm.map (fun p => p.2.1) :=
  List.mem_map.mpr ⟨(x, (nx, r)), mem_of_lookup_eq_some h, rfl⟩

theorem TEnvRel.cons_fresh {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F}
    {fsh : FunShapes} {vm : TVarMap} {ρ : Env} {locals : Environment F Nat}
    {x : Var} {nx : String} {rx : Rep} {v : Fir.Val} {w : SourceValue F}
    (hr : TEnvRel P cert feat h fsh vm ρ locals)
    (hfresh : nx ∉ vm.map (fun p => p.2.1))
    (hrep : rx = repOf P cert feat (fsh.var x))
    (htvr : TVR P cert feat h rx v w) :
    TEnvRel P cert feat h fsh ((x, nx, rx) :: vm) (ρ.insert x v) ((nx, w) :: locals) where
  rep_eq y ny r hlook := by
    by_cases hyx : y = x
    · subst hyx
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hlook
      obtain ⟨_, rfl⟩ := hlook
      exact hrep
    · have hb : (y == x) = false := beq_false_of_ne hyx
      simp only [List.lookup, hb] at hlook
      exact hr.rep_eq y ny r hlook
  rel y ny r wy hlook hloc := by
    by_cases hyx : y = x
    · subst hyx
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hlook
      obtain ⟨rfl, rfl⟩ := hlook
      simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hloc
      obtain ⟨_, rfl⟩ := hloc
      exact ⟨v, Src.NatMap.get?_insert_self ρ y v, htvr⟩
    · have hb : (y == x) = false := beq_false_of_ne hyx
      simp only [List.lookup, hb] at hlook
      have hne : nx ≠ ny := fun heq => hfresh (heq ▸ tlookup_mem_names hlook)
      have hneB : (nx == ny) = false := beq_false_of_ne hne
      simp only [List.find?_cons, hneB] at hloc
      obtain ⟨vy, hρ, htvry⟩ := hr.rel y ny r wy hlook hloc
      exact ⟨vy, by rw [FirFacts.get?_insert_ne ρ v (Ne.symm hyx)]; exact hρ, htvry⟩

theorem TEnvRel.cons_unused {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F}
    {fsh : FunShapes} {vm : TVarMap} {ρ : Env} {locals : Environment F Nat}
    {nm : String} {w : SourceValue F}
    (hr : TEnvRel P cert feat h fsh vm ρ locals)
    (hfresh : nm ∉ vm.map (fun p => p.2.1)) :
    TEnvRel P cert feat h fsh vm ρ ((nm, w) :: locals) where
  rep_eq := hr.rep_eq
  rel y ny r wy hlook hloc := by
    have hne : nm ≠ ny := fun heq => hfresh (heq ▸ tlookup_mem_names hlook)
    have hneB : (nm == ny) = false := beq_false_of_ne hne
    simp only [List.find?_cons, hneB] at hloc
    exact hr.rel y ny r wy hlook hloc

theorem TEnvRel.of_capZip {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F}
    {fsh : FunShapes} {vm : TVarMap} {ρ : Env} {localsDef : Environment F Nat}
    {capNames : List String} {capVals : List (SourceValue F)}
    (hr : TEnvRel P cert feat h fsh vm ρ localsDef)
    (hnd : capNames.Nodup) (hcap : EvalCapArgs localsDef capNames capVals) :
    TEnvRel P cert feat h fsh vm ρ (capNames.zip capVals) where
  rep_eq := hr.rep_eq
  rel y ny r wy hlook hloc := by
    have hmem : (ny, wy) ∈ capNames.zip capVals := List.mem_of_find?_eq_some hloc
    have hnyMem : ny ∈ capNames := (List.of_mem_zip hmem).1
    have heq := find?_eq_of_evalCapArgs hnd hcap hnyMem
    rw [heq] at hloc
    exact hr.rel y ny r wy hlook hloc

theorem TEnvRel.bindTVm_append {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F}
    {fsh : FunShapes} :
    ∀ {ps : List Var} {pns : List String} {vs : List Fir.Val} {ws : List (SourceValue F)}
      {vm : TVarMap} {ρ : Env} {base : Environment F Nat},
      ps.length = pns.length →
      pns.Nodup →
      (∀ p ∈ pns, p ∉ base.map Prod.fst) →
      (∀ p ∈ pns, p ∉ vm.map (fun q => q.2.1)) →
      TEnvRel P cert feat h fsh vm ρ base →
      TVRs P cert feat h (ps.map fun p => repOf P cert feat (fsh.var p)) vs ws →
      TEnvRel P cert feat h fsh
        (bindTVm vm ps (pns.zip (ps.map fun p => repOf P cert feat (fsh.var p))))
        (Fir.bindAll ρ ps vs) (base ++ pns.zip ws) := by
  intro ps
  induction ps with
  | nil =>
    intro pns vs ws vm ρ base hlen _ _ _ henv htvrs
    cases pns <;> cases htvrs <;> simp_all [bindTVm, Fir.bindAll]
  | cons x xs ih =>
    intro pns vs ws vm ρ base hlen hnd hdisjB hdisjV henv htvrs
    cases pns with
    | nil => simp at hlen
    | cons pn pnt =>
      cases htvrs with
      | @cons _ _ v vs' w ws' hvr htl =>
        rw [List.nodup_cons] at hnd
        simp only [List.map_cons, List.zip_cons_cons, bindTVm, Fir.bindAll]
        have hlen' : xs.length = pnt.length := by simpa using hlen
        have hpnDisjB : pn ∉ base.map Prod.fst := hdisjB pn List.mem_cons_self
        have hpnDisjV : pn ∉ vm.map (fun q => q.2.1) := hdisjV pn List.mem_cons_self
        have hnoneBase : base.find? (·.1 == pn) = none := by
          rw [List.find?_eq_none]
          intro p hp; simp only [beq_iff_eq]; intro heq
          exact hpnDisjB (List.mem_map.mpr ⟨p, hp, heq⟩)
        have henv1 : TEnvRel P cert feat h fsh
            ((x, pn, repOf P cert feat (fsh.var x)) :: vm) (ρ.insert x v) (base ++ [(pn, w)]) :=
          { rep_eq := fun y ny r hlook => by
              by_cases hyx : y = x
              · subst hyx
                simp only [List.lookup, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hlook
                obtain ⟨_, rfl⟩ := hlook; rfl
              · have hb : (y == x) = false := beq_false_of_ne hyx
                simp only [List.lookup, hb] at hlook
                exact henv.rep_eq y ny r hlook
            rel := fun y ny r wy hlook hloc => by
              by_cases hyx : y = x
              · subst hyx
                simp only [List.lookup, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hlook
                obtain ⟨rfl, rfl⟩ := hlook
                rw [List.find?_append, hnoneBase] at hloc
                simp only [Option.none_or, List.find?_cons, beq_self_eq_true, Option.some.injEq,
                  Prod.mk.injEq] at hloc
                obtain ⟨_, rfl⟩ := hloc
                exact ⟨v, Src.NatMap.get?_insert_self ρ y v, hvr⟩
              · have hb : (y == x) = false := beq_false_of_ne hyx
                simp only [List.lookup, hb] at hlook
                have hne : pn ≠ ny := fun heq => hpnDisjV (heq ▸ tlookup_mem_names hlook)
                have hneB : (pn == ny) = false := beq_false_of_ne hne
                rw [List.find?_append] at hloc
                cases hfb : base.find? (·.1 == ny) with
                | none =>
                  rw [hfb] at hloc
                  simp [hneB] at hloc
                | some p =>
                  rw [hfb] at hloc
                  simp only [Option.some_or, Option.some.injEq] at hloc
                  subst hloc
                  obtain ⟨vy, hρ, htvry⟩ := henv.rel y ny r wy hlook hfb
                  exact ⟨vy, by rw [FirFacts.get?_insert_ne ρ v (Ne.symm hyx)]; exact hρ, htvry⟩ }
        have hdisjB' : ∀ p ∈ pnt, p ∉ (base ++ [(pn, w)]).map Prod.fst := by
          intro p hp hmem
          simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
            List.mem_singleton] at hmem
          rcases hmem with hb | rfl
          · exact hdisjB p (List.mem_cons_of_mem _ hp) hb
          · exact hnd.1 hp
        have hdisjV' : ∀ p ∈ pnt, p ∉ (((x, pn, repOf P cert feat (fsh.var x)) :: vm).map (fun q => q.2.1)) := by
          intro p hp hmem
          simp only [List.map_cons, List.mem_cons] at hmem
          rcases hmem with rfl | hv
          · exact hnd.1 hp
          · exact hdisjV p (List.mem_cons_of_mem _ hp) hv
        have hres := ih (base := base ++ [(pn, w)]) hlen' hnd.2 hdisjB' hdisjV' henv1 htl
        simpa [List.append_assoc] using hres

/-- Non-zero invariant for `nz : List Var`: every variable in `nz` holds a positive `Nat` literal. -/
def NzRel (ρ : Env) (nz : List Var) : Prop :=
  ∀ x ∈ nz, ∃ n, ρ.get? x = some (.lit (.nat n)) ∧ 0 < n

theorem NzRel.filter_ne {ρ : Env} {nz : List Var} (h : NzRel ρ nz) (x : Var) (v : Fir.Val) :
    NzRel (ρ.insert x v) (nz.filter (· != x)) := by
  intro y hy
  simp only [List.mem_filter, bne_iff_ne, ne_eq] at hy
  obtain ⟨n, hget, hpos⟩ := h y hy.1
  exact ⟨n, by rw [FirFacts.get?_insert_ne ρ v (Ne.symm hy.2)]; exact hget, hpos⟩

theorem NzRel.cons {ρ : Env} {nz : List Var} {x : Var} {n : Nat}
    (hget : ρ.get? x = some (.lit (.nat n))) (hpos : 0 < n) (h : NzRel ρ nz) :
    NzRel ρ (x :: nz) := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | htl
  · exact ⟨n, hget, hpos⟩
  · exact h y htl

private theorem get?_bindAll_not_mem {ρ : Env} {y : Var} :
    ∀ {ps : List Var} {vs : List Fir.Val},
      y ∉ ps → (Fir.bindAll ρ ps vs).get? y = ρ.get? y
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | p :: pt, v :: vt, hni => by
    simp only [List.mem_cons, not_or] at hni
    simp only [Fir.bindAll]
    rw [get?_bindAll_not_mem hni.2, FirFacts.get?_insert_ne ρ v (Ne.symm hni.1)]

theorem NzRel.filter_bindAll {ρ : Env} {nz : List Var} (h : NzRel ρ nz)
    (ps : List Var) (vs : List Fir.Val) :
    NzRel (Fir.bindAll ρ ps vs) (nz.filter fun v => !ps.contains v) := by
  intro y hy
  simp only [List.mem_filter, Bool.not_eq_true', Bool.eq_false_iff] at hy
  have hni : y ∉ ps := fun hm => hy.2 (List.contains_iff_mem.mpr hm)
  obtain ⟨n, hget, hpos⟩ := h y hy.1
  exact ⟨n, by rw [get?_bindAll_not_mem hni]; exact hget, hpos⟩

/-- Countdown offset invariant for `offs : OffMap`: if `offs.lookup x = some (baseNm, d)`, then
`x` holds `n < natLimit` in `ρ` and whenever `baseNm` is bound in `locals`, it holds
`.field ((n + d : Nat) : F)` with `n + d < natLimit`. -/
def OffsRel (ρ : Env) (locals : Environment F Nat) (offs : OffMap) : Prop :=
  ∀ x baseNm d, offs.lookup x = some (baseNm, d) →
    ∃ n, ρ.get? x = some (.lit (.nat n)) ∧ n < natLimit ∧
      ∀ w, locals.find? (·.1 == baseNm) = some (baseNm, w) →
        n + d < natLimit ∧ w = .field ((n + d : Nat) : F)

theorem OffsRel.cons_unused {ρ : Env} {locals : Environment F Nat} {offs : OffMap}
    {nm : String} {w0 : SourceValue F}
    (h : OffsRel ρ locals offs) (hfresh : nm ∉ offs.map (fun p => p.2.1)) :
    OffsRel ρ ((nm, w0) :: locals) offs := by
  intro x baseNm d hl
  obtain ⟨n, hρ, hn, hbase⟩ := h x baseNm d hl
  have hmem : baseNm ∈ offs.map (fun p => p.2.1) :=
    List.mem_map.mpr ⟨(x, (baseNm, d)), mem_of_lookup_eq_some hl, rfl⟩
  have hne : nm ≠ baseNm := fun heq => hfresh (heq ▸ hmem)
  have hneB : (nm == baseNm) = false := beq_false_of_ne hne
  refine ⟨n, hρ, hn, fun w hloc => ?_⟩
  simp only [List.find?_cons, hneB] at hloc
  exact hbase w hloc

private theorem lookup_filter_ne_inv {α : Type} {offs : List (Var × α)} {x y : Var} {v : α}
    (h : (offs.filter (·.1 != x)).lookup y = some v) :
    y ≠ x ∧ offs.lookup y = some v := by
  induction offs with
  | nil => simp at h
  | cons hd tl ih =>
    rcases hd with ⟨k, a⟩
    simp only [List.filter_cons] at h
    by_cases hkx : (k != x) = true
    · simp only [hkx, ↓reduceIte, List.lookup] at h ⊢
      by_cases hyk : (y == k) = true
      · simp only [hyk, Option.some.injEq] at h ⊢
        subst h
        have hyk' : y = k := beq_iff_eq.mp hyk
        have hkx' : k ≠ x := bne_iff_ne.mp hkx
        exact ⟨hyk' ▸ hkx', rfl⟩
      · have hykf : (y == k) = false := Bool.eq_false_iff.mpr hyk
        simp only [hykf] at h ⊢
        exact ih h
    · have hkxf : (k != x) = false := Bool.eq_false_iff.mpr hkx
      simp only [hkxf, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hne, hl⟩ := ih h
      have hkx' : k = x := by simpa using hkxf
      have hykf : (y == k) = false := beq_false_of_ne (hkx' ▸ hne)
      exact ⟨hne, by simp [List.lookup, hykf, hl]⟩

theorem OffsRel.update {ρ : Env} {locals : Environment F Nat} {offs : OffMap}
    {x : Var} {nx : String} {v : Fir.Val} {w1 : SourceValue F} {xOff? : Option (String × Nat)}
    (h : OffsRel ρ locals offs)
    (hfreshOld : nx ∉ offs.map (fun p => p.2.1))
    (hnew : ∀ baseNm d, xOff? = some (baseNm, d) →
      nx ≠ baseNm ∧
      ∃ n, v = .lit (.nat n) ∧ n < natLimit ∧
        ∀ w, locals.find? (·.1 == baseNm) = some (baseNm, w) →
          n + d < natLimit ∧ w = .field ((n + d : Nat) : F)) :
    OffsRel (ρ.insert x v) ((nx, w1) :: locals)
      (match xOff? with
       | some off => (x, off) :: offs.filter (·.1 != x)
       | none => offs.filter (·.1 != x)) := by
  have hfilt : ∀ y baseNm d, (offs.filter (·.1 != x)).lookup y = some (baseNm, d) →
      ∃ n, (ρ.insert x v).get? y = some (.lit (.nat n)) ∧ n < natLimit ∧
        ∀ w, ((nx, w1) :: locals).find? (·.1 == baseNm) = some (baseNm, w) →
          n + d < natLimit ∧ w = .field ((n + d : Nat) : F) := by
    intro y baseNm d hl
    obtain ⟨hne, hlOld⟩ := lookup_filter_ne_inv hl
    obtain ⟨n, hρ, hn, hbase⟩ := h y baseNm d hlOld
    have hmem : baseNm ∈ offs.map (fun p => p.2.1) :=
      List.mem_map.mpr ⟨(y, (baseNm, d)), mem_of_lookup_eq_some hlOld, rfl⟩
    have hneNx : nx ≠ baseNm := fun heq => hfreshOld (heq ▸ hmem)
    have hneB : (nx == baseNm) = false := beq_false_of_ne hneNx
    refine ⟨n, by rw [FirFacts.get?_insert_ne ρ v (Ne.symm hne)]; exact hρ, hn, fun w hloc => ?_⟩
    simp only [List.find?_cons, hneB] at hloc
    exact hbase w hloc
  cases xOff? with
  | none => exact hfilt
  | some off =>
    rcases off with ⟨b0, d0⟩
    intro y baseNm d hl
    by_cases hyx : y = x
    · subst hyx
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      obtain ⟨hneNx, n, rfl, hn, hbase⟩ := hnew b0 d0 rfl
      have hneB : (nx == b0) = false := beq_false_of_ne hneNx
      refine ⟨n, Src.NatMap.get?_insert_self ρ y _, hn, fun w hloc => ?_⟩
      simp only [List.find?_cons, hneB] at hloc
      exact hbase w hloc
    · have hb : (y == x) = false := beq_false_of_ne hyx
      simp only [List.lookup, hb] at hl
      exact hfilt y baseNm d hl

theorem OffsRel.of_initOffs {P : Program} {cert : ShapeCert} {feat : Features} {h : Heap F}
    {fsh : FunShapes} :
    ∀ {ps : List Var} {pns : List String} {vs : List Fir.Val} {ws : List (SourceValue F)}
      {ρ : Env} {base : Environment F Nat},
      ps.Nodup →
      ps.length = pns.length →
      pns.Nodup →
      (∀ p ∈ pns, p ∉ base.map Prod.fst) →
      TVRs P cert feat h (ps.map fun p => repOf P cert feat (fsh.var p)) vs ws →
      OffsRel (Fir.bindAll ρ ps vs) (base ++ pns.zip ws)
        ((ps.zip (pns.zip (ps.map fun p => repOf P cert feat (fsh.var p)))).filterMap
          fun (p, nm, r) => match r with | .nat _ => some (p, (nm, 0)) | _ => none) := by
  intro ps
  induction ps with
  | nil =>
    intro pns vs ws ρ base _ _ _ _ _ x baseNm d hl
    cases hl
  | cons x xs ih =>
    intro pns vs ws ρ base hpsNd hlen hpnsNd hdisjB htvrs
    cases pns with
    | nil => simp at hlen
    | cons pn pnt =>
      cases htvrs with
      | @cons _ _ v vs' w ws' hvr htl =>
        rw [List.nodup_cons] at hpsNd hpnsNd
        have hlen' : xs.length = pnt.length := by simpa using hlen
        have hpnDisjB : pn ∉ base.map Prod.fst := hdisjB pn List.mem_cons_self
        have hnoneBase : base.find? (·.1 == pn) = none := by
          rw [List.find?_eq_none]
          intro p hp; simp only [beq_iff_eq]; intro heq
          exact hpnDisjB (List.mem_map.mpr ⟨p, hp, heq⟩)
        have hdisjB' : ∀ p ∈ pnt, p ∉ (base ++ [(pn, w)]).map Prod.fst := by
          intro p hp hmem
          simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
            List.mem_singleton] at hmem
          rcases hmem with hb | rfl
          · exact hdisjB p (List.mem_cons_of_mem _ hp) hb
          · exact hpnsNd.1 hp
        have htail := ih (ρ := ρ.insert x v) (base := base ++ [(pn, w)])
          hpsNd.2 hlen' hpnsNd.2 hdisjB' htl
        have htail' : OffsRel (Fir.bindAll (ρ.insert x v) xs vs') (base ++ (pn, w) :: pnt.zip ws')
            ((xs.zip (pnt.zip (xs.map fun p => repOf P cert feat (fsh.var p)))).filterMap
              fun (p, nm, r) => match r with | .nat _ => some (p, (nm, 0)) | _ => none) := by
          simpa [List.append_assoc] using htail
        simp only [List.map_cons, List.zip_cons_cons, List.filterMap_cons, Fir.bindAll]
        cases hr : repOf P cert feat (fsh.var x) with
        | nat b =>
          simp only []
          intro y baseNm d hl
          by_cases hyx : y = x
          · subst hyx
            simp only [List.lookup, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hl
            obtain ⟨rfl, rfl⟩ := hl
            dsimp only at hvr
            rw [hr] at hvr
            obtain ⟨n, _, hn, rfl, rfl⟩ := TVR_nat_inv hvr
            refine ⟨n, ?_, hn, fun w' hloc => ?_⟩
            · rw [get?_bindAll_not_mem hpsNd.1, Src.NatMap.get?_insert_self]
            · rw [List.find?_append, hnoneBase] at hloc
              simp only [Option.none_or, List.find?_cons, beq_self_eq_true, Option.some.injEq,
                Prod.mk.injEq] at hloc
              obtain ⟨_, rfl⟩ := hloc
              exact ⟨by omega, by simp⟩
          · have hb : (y == x) = false := beq_false_of_ne hyx
            simp only [List.lookup, hb] at hl
            exact htail' y baseNm d hl
        | irr | w8 | w16 | w32 | w64 | «enum» _ | data _ | obj =>
          exact htail'

/-- Capture agreement between a join point's definition environment `localsDef` and a current
environment `localsCur`: every captured name bound in `localsCur` maps to the same value as in
`localsDef`. Works identically for both unfiltered and `filterJpCaptures`-filtered join points! -/
def CapAgree (capNames : List String) (localsDef localsCur : Environment F Nat) : Prop :=
  ∀ nm ∈ capNames, ∀ w, localsCur.find? (·.1 == nm) = some (nm, w) →
    localsDef.find? (·.1 == nm) = some (nm, w)

omit [Field F] in
theorem CapAgree.refl (capNames : List String) (locals : Environment F Nat) :
    CapAgree capNames locals locals :=
  fun _ _ _ h => h

omit [Field F] in
theorem CapAgree.cons_unused {capNames : List String} {localsDef localsCur : Environment F Nat}
    {nx : String} {w0 : SourceValue F}
    (hfresh : nx ∉ capNames) (ha : CapAgree capNames localsDef localsCur) :
    CapAgree capNames localsDef ((nx, w0) :: localsCur) := by
  intro nm hnm w hloc
  have hne : nx ≠ nm := fun heq => hfresh (heq ▸ hnm)
  have hneB : (nx == nm) = false := beq_false_of_ne hne
  simp only [List.find?_cons, hneB] at hloc
  exact ha nm hnm w hloc

omit [Field F] in
theorem CapAgree.of_capZip {capNames capNames' : List String}
    {localsDef localsCur : Environment F Nat} {capVals : List (SourceValue F)}
    (hnd : capNames'.Nodup) (hcap : EvalCapArgs localsCur capNames' capVals)
    (ha : CapAgree capNames localsDef localsCur) :
    CapAgree capNames localsDef (capNames'.zip capVals) := by
  intro nm hnm w hloc
  have hmem : (nm, w) ∈ capNames'.zip capVals := List.mem_of_find?_eq_some hloc
  have hnm' : nm ∈ capNames' := (List.of_mem_zip hmem).1
  rw [find?_eq_of_evalCapArgs hnd hcap hnm'] at hloc
  exact ha nm hnm w hloc

omit [Field F] in
theorem CapAgree.append_right {capNames : List String}
    {localsDef base extra : Environment F Nat}
    (hdisj : ∀ p ∈ extra, p.1 ∉ capNames)
    (ha : CapAgree capNames localsDef base) :
    CapAgree capNames localsDef (base ++ extra) := by
  intro nm hnm w hloc
  rw [List.find?_append] at hloc
  cases hfb : base.find? (·.1 == nm) with
  | some p =>
    rw [hfb] at hloc
    simp only [Option.some_or, Option.some.injEq] at hloc
    subst hloc
    exact ha nm hnm w hfb
  | none =>
    rw [hfb] at hloc
    simp only [Option.none_or] at hloc
    have hmem := List.mem_of_find?_eq_some hloc
    exact False.elim (hdisj (nm, w) hmem hnm)

omit [Field F] in
theorem evalCapArgs_of_capAgree {localsDef localsCur : Environment F Nat} :
    ∀ {nms : List String} {ws : List (SourceValue F)},
      CapAgree nms localsDef localsCur → EvalCapArgs localsCur nms ws →
      EvalCapArgs localsDef nms ws
  | [], [], _, _ => trivial
  | nm :: _nms, w :: _ws, ha, ⟨hd, tl⟩ =>
    ⟨ha nm List.mem_cons_self w hd,
     evalCapArgs_of_capAgree (fun x hx => ha x (List.mem_cons_of_mem _ hx)) tl⟩
  | [], _ :: _, _, h => False.elim h
  | _ :: _, [], _, h => False.elim h

end TypedEnvsOnly

section TypedEnvsDec

variable {F : Type} [Field F] [DecidableEq F]

/-- Depth-indexed typed join-point stack relation. -/
inductive TJEnvRel (P : Program) (cert : ShapeCert) (feat : Features) (world : World F) :
    Nat → Heap F → FunShapes → List TJEntry → List Fir.JEntry → Environment F Nat → Prop where
  | nil {d : Nat} {h : Heap F} {fsh : FunShapes} {locals : Environment F Nat} :
      TJEnvRel P cert feat world d h fsh [] [] locals
  | cons {d : Nat} {h : Heap F} {fsh : FunShapes} {ji : TJEntry} {jrest : List TJEntry}
      {je : Fir.JEntry} {Jrest : List Fir.JEntry} {locals localsDef : Environment F Nat}
      (idEq : ji.id = je.id)
      (fnQual : qualifyName ji.fnName = qualified ji.fnName)
      (paramsOk : Fir.Shape.ParamsOk fsh je.params (fsh.join je.id))
      (repsEq : ji.paramReps = je.params.map fun p => repOf P cert feat (fsh.var p))
      (retEq : ji.retRep = repOf P cert feat fsh.ret)
      (capAgree : CapAgree (ji.capVars.map Prod.fst) localsDef locals)
      (sound : ∀ d' < d, ∀ h1, Heap.Extends h h1 →
        ∀ capWs vs ws r h2,
          EvalCapArgs localsDef (ji.capVars.map Prod.fst) capWs →
          TVRs P cert feat h1 ji.paramReps vs ws →
          Fir.Shape.ValsOk cert dummyEnc (fsh.join je.id) vs →
          EvalFnN world d' (qualified ji.fnName) (capWs ++ ws) h1 r h2 →
          ∃ k v, Fir.eval P k (Fir.bindAll je.env je.params vs) (je.after Jrest) je.body = .ok v ∧
            TVR P cert feat h2 (repOf P cert feat fsh.ret) v r)
      (tail : TJEnvRel P cert feat world d h fsh jrest Jrest locals) :
      TJEnvRel P cert feat world d h fsh (ji :: jrest) (je :: Jrest) locals

theorem TJEnvRel.extend {P : Program} {cert : ShapeCert} {feat : Features} {world : World F}
    {d : Nat} {h h' : Heap F} (ext : Heap.Extends h h')
    {fsh : FunShapes} {jenv : List TJEntry} {J : List Fir.JEntry} {locals : Environment F Nat}
    (hr : TJEnvRel P cert feat world d h fsh jenv J locals) :
    TJEnvRel P cert feat world d h' fsh jenv J locals := by
  induction hr with
  | nil => exact .nil
  | cons idEq fnQual pOk rEq retEq ca snd _ ih =>
    exact .cons idEq fnQual pOk rEq retEq ca
      (fun d' hd' h1 ext1 => snd d' hd' h1 (ext.trans ext1)) ih

theorem TJEnvRel.mono_depth {P : Program} {cert : ShapeCert} {feat : Features} {world : World F}
    {d₁ d₂ : Nat} (hle : d₁ ≤ d₂)
    {h : Heap F} {fsh : FunShapes} {jenv : List TJEntry} {J : List Fir.JEntry}
    {locals : Environment F Nat}
    (hr : TJEnvRel P cert feat world d₂ h fsh jenv J locals) :
    TJEnvRel P cert feat world d₁ h fsh jenv J locals := by
  induction hr with
  | nil => exact .nil
  | cons idEq fnQual pOk rEq retEq ca snd _ ih =>
    exact .cons idEq fnQual pOk rEq retEq ca
      (fun d' hd' => snd d' (Nat.lt_of_lt_of_le hd' hle)) ih

theorem TJEnvRel.cons_unused {P : Program} {cert : ShapeCert} {feat : Features} {world : World F}
    {d : Nat} {h : Heap F} {fsh : FunShapes} {jenv : List TJEntry} {J : List Fir.JEntry}
    {locals : Environment F Nat} {nx : String} {wx : SourceValue F}
    (hfresh : nx ∉ jenv.flatMap (fun je => je.capVars.map Prod.fst))
    (hr : TJEnvRel P cert feat world d h fsh jenv J locals) :
    TJEnvRel P cert feat world d h fsh jenv J ((nx, wx) :: locals) := by
  induction hr with
  | nil => exact .nil
  | cons idEq fnQual pOk rEq retEq ca snd _ ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at hfresh
    exact .cons idEq fnQual pOk rEq retEq (ca.cons_unused hfresh.1) snd (ih hfresh.2)

theorem TJEnvRel.of_capZip {P : Program} {cert : ShapeCert} {feat : Features} {world : World F}
    {d : Nat} {h : Heap F} {fsh : FunShapes} {jenv : List TJEntry} {J : List Fir.JEntry}
    {locals : Environment F Nat} {capNames : List String} {capVals : List (SourceValue F)}
    (hnd : capNames.Nodup) (hcap : EvalCapArgs locals capNames capVals)
    (hr : TJEnvRel P cert feat world d h fsh jenv J locals) :
    TJEnvRel P cert feat world d h fsh jenv J (capNames.zip capVals) := by
  induction hr with
  | nil => exact .nil
  | cons idEq fnQual pOk rEq retEq ca snd _ ih =>
    exact .cons idEq fnQual pOk rEq retEq (ca.of_capZip hnd hcap) snd (ih hcap)

theorem TJEnvRel.append_right {P : Program} {cert : ShapeCert} {feat : Features} {world : World F}
    {d : Nat} {h : Heap F} {fsh : FunShapes} {jenv : List TJEntry} {J : List Fir.JEntry}
    {base extra : Environment F Nat}
    (hdisj : ∀ p ∈ extra, p.1 ∉ jenv.flatMap (fun je => je.capVars.map Prod.fst))
    (hr : TJEnvRel P cert feat world d h fsh jenv J base) :
    TJEnvRel P cert feat world d h fsh jenv J (base ++ extra) := by
  induction hr with
  | nil => exact .nil
  | cons idEq fnQual pOk rEq retEq ca snd _ ih =>
    exact .cons idEq fnQual pOk rEq retEq
      (ca.append_right (fun p hp hm => hdisj p hp (List.mem_append_left _ hm)))
      snd
      (ih (fun p hp hm => hdisj p hp (List.mem_append_right _ hm)))

theorem TJEnvRel.find_lookup {P : Program} {cert : ShapeCert} {feat : Features} {world : World F}
    {d : Nat} {h : Heap F} {fsh : FunShapes} {jenv : List TJEntry} {J : List Fir.JEntry}
    {locals : Environment F Nat}
    (hr : TJEnvRel P cert feat world d h fsh jenv J locals)
    {j : JoinId} {ji : TJEntry} (hfind : jenv.find? (·.id == j) = some ji) :
    ∃ je Jrest localsDef,
      lookupJ j J = some (je, Jrest) ∧
      qualifyName ji.fnName = qualified ji.fnName ∧
      Fir.Shape.ParamsOk fsh je.params (fsh.join j) ∧
      ji.paramReps = je.params.map (fun p => repOf P cert feat (fsh.var p)) ∧
      CapAgree (ji.capVars.map Prod.fst) localsDef locals ∧
      (∀ d' < d, ∀ h1, Heap.Extends h h1 →
        ∀ capWs vs ws r h2,
          EvalCapArgs localsDef (ji.capVars.map Prod.fst) capWs →
          TVRs P cert feat h1 ji.paramReps vs ws →
          Fir.Shape.ValsOk cert dummyEnc (fsh.join j) vs →
          EvalFnN world d' (qualified ji.fnName) (capWs ++ ws) h1 r h2 →
          ∃ k v, Fir.eval P k (Fir.bindAll je.env je.params vs) (je.after Jrest) je.body = .ok v ∧
            TVR P cert feat h2 (repOf P cert feat fsh.ret) v r) := by
  induction hr with
  | nil => simp at hfind
  | @cons ji' jrest je' Jrest loc' locDef' idEq fnQual pOk rEq retEq ca snd _ ih =>
    simp only [List.find?_cons] at hfind
    by_cases hEq : ji'.id = j
    · have hb : (ji'.id == j) = true := beq_iff_eq.mpr hEq
      rw [hb] at hfind
      simp only [Option.some.injEq] at hfind
      subst hfind
      have hje : je'.id = j := idEq ▸ hEq
      rw [hje] at pOk snd
      exact ⟨je', Jrest, locDef', by simp [lookupJ, hje], fnQual, pOk, rEq, ca, snd⟩
    · have hb : (ji'.id == j) = false := beq_false_of_ne hEq
      rw [hb] at hfind
      have hneJe : je'.id ≠ j := idEq ▸ hEq
      obtain ⟨je, Jrest', locDef, hlook, hq, hpOk, hrEq, hca, hsnd⟩ := ih hfind
      exact ⟨je, Jrest', locDef, by simp [lookupJ, hneJe, hlook], hq, hpOk, hrEq, hca, hsnd⟩

/-- Semantic side-condition on the target representation `toR` of a coercion `coerceEAux`:
either `toR` is `.obj` or `.nat natLimit` (unconstrained targets), or `v` satisfies `ValOk`
at a shape whose representation is `toR` (guaranteeing any elided bound/tag invariants). -/
def CoerceTargetOk (P : Program) (cert : ShapeCert) (feat : Features) (toR : Rep) (v : Fir.Val) :
    Prop :=
  toR = .obj ∨ toR = .nat natLimit ∨
  ∃ s : Shape, repOf P cert feat s = toR ∧ Fir.Shape.ValOk cert dummyEnc s v

theorem CoerceTargetOk.of_valOk {P : Program} {cert : ShapeCert} {feat : Features}
    {s : Shape} {v : Fir.Val} (hv : Fir.Shape.ValOk cert dummyEnc s v) :
    CoerceTargetOk P cert feat (repOf P cert feat s) v :=
  Or.inr (Or.inr ⟨s, rfl, hv⟩)

theorem CoerceTargetOk.nat_bound {P : Program} {cert : ShapeCert} {feat : Features}
    {b n : Nat} (h : CoerceTargetOk P cert feat (.nat b) (.lit (.nat n))) (hn : n < natLimit) :
    n < min b natLimit := by
  rcases h with h1 | h2 | ⟨s, hrep, hv⟩
  · cases h1
  · cases h2; exact Nat.lt_min.mpr ⟨hn, hn⟩
  · exact valOk_nat_bound hrep hv hn

theorem CoerceTargetOk.w8_bound {P : Program} {cert : ShapeCert} {feat : Features}
    {n : Nat} (h : CoerceTargetOk P cert feat .w8 (.lit (.nat n))) : n < 256 := by
  rcases h with h1 | h2 | ⟨s, hrep, hv⟩
  · cases h1
  · cases h2
  · obtain ⟨m, hm, heq⟩ := valOk_w8_bound hrep hv
    cases heq; exact hm

theorem CoerceTargetOk.w16_bound {P : Program} {cert : ShapeCert} {feat : Features}
    {n : Nat} (h : CoerceTargetOk P cert feat .w16 (.lit (.nat n))) : n < 65536 := by
  rcases h with h1 | h2 | ⟨s, hrep, hv⟩
  · cases h1
  · cases h2
  · obtain ⟨m, hm, heq⟩ := valOk_w16_bound hrep hv
    cases heq; exact hm

theorem CoerceTargetOk.data_inv {P : Program} {cert : ShapeCert} {feat : Features}
    {d : Nat} {v : Fir.Val} (h : CoerceTargetOk P cert feat (.data d) v) :
    ∃ D c fl fs,
      cert.data? d = some D ∧ (c.key, fl) ∈ D.ctors ∧
      Fir.Shape.ValsOk cert dummyEnc fl fs ∧ v = .ctor c fs := by
  rcases h with h1 | h2 | ⟨s, hrep, hv⟩
  · cases h1
  · cases h2
  · exact (valOk_data_inv hrep hv).2

theorem CoerceTargetOk.enum_inv {P : Program} {cert : ShapeCert} {feat : Features}
    {ind : Src.CId} {v : Fir.Val} (h : CoerceTargetOk P cert feat (.enum ind) v) :
    ∃ ks c, cert.enum? ind = some ks ∧ c.key ∈ ks ∧ v = .ctor c [] := by
  rcases h with h1 | h2 | ⟨s, hrep, hv⟩
  · cases h1
  · cases h2
  · exact (valOk_enum_inv hrep hv).2

/-- Depth-indexed typed function soundness hypothesis for `Prog::f<f>`. -/
def TFunSoundN (P : Program) (cert : ShapeCert) (feat : Features) (world : World F) (d : Nat) :
    Prop :=
  ∀ d' < d, ∀ (f : FunId) (fd : Fun),
    P.fun? f = some fd → f < P.size →
    ∀ (vs : List Fir.Val) (ws : List (SourceValue F)) (h : Heap F) (r : SourceValue F) (h' : Heap F),
      TVRs P cert feat h ((fd.params.map Prod.fst).map fun p => repOf P cert feat ((cert.fn f).var p)) vs ws →
      Fir.Shape.ValsOk cert dummyEnc (cert.fn f).params vs →
      EvalFnN world d' (qualified (funName f)) ws h r h' →
      ∃ k v, Fir.evalCall P k f vs = .ok v ∧
        TVR P cert feat h' (repOf P cert feat (cert.fn f).ret) v r

/-! ### Backward Simulation of `coerceEAux`, `coerceE`, `tArgRaw`, `tArgE`, `tArgEs`, `wrapBool` -/

private theorem eval_coerceEAux_zero {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld P cert sched lp world)
    (hnd : (objCtorNames P).Nodup)
    (fromR toR : Rep) (e : Lower.Expr) (st st' : TState) (res : Lower.Expr)
    {dDepth : Nat} {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F}
    {Q : Fir.Val → Prop} :
    let cx : TCx := { P, cert, feat := scanFeatures P, sched }
    coerceEAux 0 cx fromR toR e st = .ok (res, st') →
    isNatCoreRep fromR = true →
    isNatCoreRep toR = true →
    DemandLe st'.demand lp.demand →
    EvalExprN world dDepth [] locals (qualifyExprF F res) h r h' →
    (∀ w0 hm, EvalExprN world dDepth [] locals (qualifyExprF F e) h w0 hm →
      ∃ v, Q v ∧ TVR P cert (scanFeatures P) hm fromR v w0 ∧ Heap.Extends h hm) →
    (∀ v, Q v → CoerceTargetOk P cert (scanFeatures P) toR v) →
    ∃ v, Q v ∧ TVR P cert (scanFeatures P) h' toR v r ∧ Heap.Extends h h' := by
  intro cx hco hcf hct hdem ev he hTarget
  unfold coerceEAux at hco
  by_cases heq : (fromR == toR) = true
  · simp only [heq, ↓reduceIte, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hco
    obtain ⟨rfl, rfl⟩ := hco
    have hfrEq : fromR = toR := beq_iff_eq.mp heq
    subst hfrEq
    exact he r h' ev
  · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hco
    -- Abstract private helpers `tLift`, `tFreshLocal`, `tMark` inside `coerceEAux 0`.
    have go : ∀ (fromR toR : Rep)
        {fL : {α : Type} → Except String α → TLowerM α}
        {fF : TLowerM String} {fM : (Demand → Demand) → TLowerM Unit},
        (match fromR, toR with
        | .nat a, .nat b => (if a ≤ b then pure e else pure e : TLowerM Lower.Expr)
        | .w8, .nat _ | .w8, .w16 => pure e
        | .w16, .nat _ => pure e
        | .nat a, .w8 =>
          if a ≤ 256 then pure e
          else do
            fM fun d => { d with needCheckU56 := true }
            let tmp ← fF
            return letE tmp e (seqE (callE "check_u8" [vE tmp]) (vE tmp))
        | .nat a, .w16 =>
          if a ≤ 65536 then pure e
          else do
            fM fun d => { d with needCheckU16 := true }
            let tmp ← fF
            return letE tmp e (seqE (callE "check_u16" [vE tmp]) (vE tmp))
        | .nat _, .w32 | .w8, .w32 | .w16, .w32 => do
          fM fun d => { d with needU32OfField := true }
          return callE "u32_of_field" [e]
        | .w32, .nat _ | .w32, .w8 | .w32, .w16 =>
          pure (callE "UInt32::compact_field" [callE "UInt32::compact" [e]])
        | .nat _, .w64 | .w8, .w64 | .w16, .w64 => do
          fM fun d => { d with needU64Bitwise := true }
          return callE "UInt64::from_field" [e]
        | .w64, .nat _ | .w64, .w8 | .w64, .w16 => do
          fM fun d => { d with needU64Bitwise := true }
          return callE "UInt64::to_field" [e]
        | .w32, .w64 => do
          fM fun d => { d with needU64Bitwise := true }
          return callE "UInt64::from_field" [callE "UInt32::compact_field" [callE "UInt32::compact" [e]]]
        | .w64, .w32 => do
          fM fun d => { d with needU64Bitwise := true }
          let tmp ← fF
          return letE tmp e <| callE "UInt32::from_bytes"
            [.array [.index (vE tmp) 0, .index (vE tmp) 1, .index (vE tmp) 2, .index (vE tmp) 3]]
        | .irr, .obj => do fM fun d => { d with needObj := true }; return seqE e erasedE
        | .nat _, .obj | .w8, .obj | .w16, .obj => do
          fM fun d => { d with needObj := true }; return natE e
        | .w32, .obj => do
          fM fun d => { d with needObj := true }
          return natE (callE "UInt32::compact_field" [callE "UInt32::compact" [e]])
        | .w64, .obj => do
          fM fun d => { d with needObj := true, needU64Bitwise := true }
          return natE (callE "UInt64::to_field" [e])
        | .enum ind, .obj => do
          fM fun d => { d with needObj := true }
          let some ks := cx.cert.enum? ind | fL (throw s!"coerce: unknown enum {ind}")
          let arms ← ks.mapM fun k => do
            let some (idx, entry) := cx.ctorEntry? k | fL (throw "coerce enum: missing ctor")
            let nm := ctorNameOf idx entry.key
            return (Aiur.Generic.Pattern.construct (.named (enumName ind) []) nm [], mk nm [])
          return matchE e arms
        | .data d, .obj => fL (throw s!"coerce: recursive data {d} → Obj exceeded depth")
        | .obj, .irr => do
          fM fun d => { d with needObj := true }; return matchE e [(pC "E" [], .tuple [])]
        | .obj, .nat _ | .obj, .w8 | .obj, .w16 => do
          fM fun d => { d with needObj := true }
          let tmp ← fF; return matchE e [(pN (.bind tmp), vE tmp)]
        | .obj, .w32 => do
          fM fun d => { d with needObj := true, needU32OfField := true }
          let tmp ← fF; return matchE e [(pN (.bind tmp), callE "u32_of_field" [vE tmp])]
        | .obj, .w64 => do
          fM fun d => { d with needObj := true, needU64Bitwise := true }
          let tmp ← fF; return matchE e [(pN (.bind tmp), callE "UInt64::from_field" [vE tmp])]
        | .obj, .enum ind => do
          fM fun d => { d with needObj := true }
          let some ks := cx.cert.enum? ind | fL (throw s!"coerce: unknown enum {ind}")
          let arms ← ks.mapM fun k => do
            let some (idx, entry) := cx.ctorEntry? k | fL (throw "coerce obj→enum: missing ctor")
            let nm := ctorNameOf idx entry.key
            return (pC nm [], Aiur.Generic.Expr.construct (enumName ind) (some []) nm [])
          return matchE e arms
        | .obj, .data d => fL (throw s!"coerce: recursive Obj → data {d} exceeded depth")
        | _, _ => fL (throw s!"unsupported coercion from {reprStr fromR} to {reprStr toR}")) st = .ok (res, st') →
        (∀ {α} (x : Except String α) s, fL x s = match x with | .ok a => .ok (a, s) | .error err => .error err) →
        (∀ s, fF s = .ok (localName s.nextLocal, { s with nextLocal := s.nextLocal + 1 })) →
        (∀ u s, fM u s = .ok ((), { s with demand := u s.demand })) →
        isNatCoreRep fromR = true →
        isNatCoreRep toR = true →
        (∀ w0 hm, EvalExprN world dDepth [] locals (qualifyExprF F e) h w0 hm →
          ∃ v, Q v ∧ TVR P cert (scanFeatures P) hm fromR v w0 ∧ Heap.Extends h hm) →
        (∀ v, Q v → CoerceTargetOk P cert (scanFeatures P) toR v) →
        ∃ v, Q v ∧ TVR P cert (scanFeatures P) h' toR v r ∧ Heap.Extends h h' := by
        intro fromR toR fL fF fM h0 hfL hfF hfM hcf hct he hTarget
        cases fromR <;> cases toR
        all_goals try exact absurd hcf (by decide)
        all_goals try exact absurd hct (by decide)
        all_goals try (simp [hfL, throw, throwThe, MonadExceptOf.throw] at h0; done)
        · -- .irr, .obj
          simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, hfM,
            Except.ok.injEq, Prod.mk.injEq] at h0
          obtain ⟨rfl, rfl⟩ := h0
          simp only [seqE, erasedE, mk, qualifyExprF, qualifyExpr, qualifyPat, qualifyName_obj,
            Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at ev
          obtain ⟨w0, hm, evE, evEr⟩ := evalExprN_let_wildcard_inv ev
          obtain ⟨v, hvQ, htvr, ext1⟩ := he w0 hm evE
          obtain ⟨rfl, rfl⟩ := TVR_irr_inv htvr
          obtain ⟨ws, hargs, rfl⟩ := evalExprN_construct_inv evEr
          cases hargs
          exact ⟨.erased, hvQ, .obj .erased, ext1⟩
        · -- .nat a, .nat b
          rename_i a b
          have hres : res = e := by
            by_cases hab : a ≤ b <;>
              (simp only [hab, ↓reduceIte, pure, StateT.pure, Except.pure, Except.ok.injEq,
                Prod.mk.injEq] at h0; exact h0.1.symm)
          subst hres
          obtain ⟨v, hvQ, htvr, ext⟩ := he r h' ev
          obtain ⟨n, _, hn, rfl, rfl⟩ := TVR_nat_inv htvr
          exact ⟨.lit (.nat n), hvQ, .nat ((hTarget _ hvQ).nat_bound hn), ext⟩
        · -- .nat a, .w8
          rename_i a
          by_cases ha : a ≤ 256
          · simp only [ha, ↓reduceIte, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
            obtain ⟨rfl, rfl⟩ := h0
            obtain ⟨v, hvQ, htvr, ext⟩ := he r h' ev
            obtain ⟨n, hsm, _, rfl, rfl⟩ := TVR_nat_inv htvr
            exact ⟨.lit (.nat n), hvQ, .w8 (by omega), ext⟩
          · simp only [ha, ↓reduceIte, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure,
              hfM, hfF, Except.ok.injEq, Prod.mk.injEq] at h0
            obtain ⟨rfl, rfl⟩ := h0
            simp only [letE, seqE, callE, vE, qualifyExprF, qualifyExpr, qualifyPat,
              qualifyName_check_u8, Option.map_some, Aiur.Generic.Expr.map,
              Aiur.Generic.Pattern.map, List.map] at ev
            obtain ⟨w0, hm, evE, evBody⟩ := evalExprN_let_bind_inv ev
            obtain ⟨v, hvQ, htvr, ext1⟩ := he w0 hm evE
            obtain ⟨n, _, hn, rfl, rfl⟩ := TVR_nat_inv htvr
            obtain ⟨_, hm2, evChk, evRet⟩ := evalExprN_let_wildcard_inv evBody
            obtain ⟨_, v1, hm1, _, ev1, hcal⟩ := evalExprN_call1_inv evChk
            obtain ⟨hl1, rfl⟩ := evalExprN_var_inv ev1
            simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hl1
            obtain ⟨_, rfl⟩ := hl1
            have hneed56 : lp.demand.needCheckU56 = true := hdem.needCheckU56 rfl
            have hneNone : lp.tier ≠ .none :=
              tier_ne_none_of_usesRangeCheck lw.lowered (by simp [hneed56])
            obtain ⟨_, rfl, b, hb, hbEq⟩ :=
              eval_check_u8 (lw.byteCheck hneNone) (lw.hasCheckU8 (Or.inl hneed56)) hcal.toEvalFn
            have hnb : n = b := fc.natCast_inj56 hn (by unfold natLimit; omega) (Value.field.inj hbEq)
            subst hnb
            obtain ⟨hl2, rfl⟩ := evalExprN_var_inv evRet
            simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hl2
            obtain ⟨_, rfl⟩ := hl2
            exact ⟨.lit (.nat n), hvQ, .w8 (by omega), ext1⟩
        · -- .nat a, .w16
          rename_i a
          by_cases ha : a ≤ 65536
          · simp only [ha, ↓reduceIte, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
            obtain ⟨rfl, rfl⟩ := h0
            obtain ⟨v, hvQ, htvr, ext⟩ := he r h' ev
            obtain ⟨n, hsm, _, rfl, rfl⟩ := TVR_nat_inv htvr
            exact ⟨.lit (.nat n), hvQ, .w16 (by omega), ext⟩
          · simp only [ha, ↓reduceIte, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure,
              hfM, hfF, Except.ok.injEq, Prod.mk.injEq] at h0
            obtain ⟨rfl, rfl⟩ := h0
            simp only [letE, seqE, callE, vE, qualifyExprF, qualifyExpr, qualifyPat,
              qualifyName_check_u16, Option.map_some, Aiur.Generic.Expr.map,
              Aiur.Generic.Pattern.map, List.map] at ev
            obtain ⟨w0, hm, evE, evBody⟩ := evalExprN_let_bind_inv ev
            obtain ⟨v, hvQ, htvr, ext1⟩ := he w0 hm evE
            obtain ⟨n, _, hn, rfl, rfl⟩ := TVR_nat_inv htvr
            obtain ⟨_, hm2, evChk, evRet⟩ := evalExprN_let_wildcard_inv evBody
            obtain ⟨_, v1, hm1, _, ev1, hcal⟩ := evalExprN_call1_inv evChk
            obtain ⟨hl1, rfl⟩ := evalExprN_var_inv ev1
            simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hl1
            obtain ⟨_, rfl⟩ := hl1
            have hneed16 : lp.demand.needCheckU16 = true := hdem.needCheckU16 rfl
            have hneNone : lp.tier ≠ .none :=
              tier_ne_none_of_usesRangeCheck lw.lowered (by simp [hneed16])
            obtain ⟨_, rfl, b, hb, hbEq⟩ :=
              eval_check_u16 (lw.byteCheck hneNone) (lw.hasCheckU16 hneed16) hcal.toEvalFn
            have hnb : n = b := fc.natCast_inj56 hn (by unfold natLimit; omega) (Value.field.inj hbEq)
            subst hnb
            obtain ⟨hl2, rfl⟩ := evalExprN_var_inv evRet
            simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hl2
            obtain ⟨_, rfl⟩ := hl2
            exact ⟨.lit (.nat n), hvQ, .w16 (by omega), ext1⟩
        · -- .nat a, .obj
          simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, hfM,
            Except.ok.injEq, Prod.mk.injEq] at h0
          obtain ⟨rfl, rfl⟩ := h0
          simp only [natE, mk, qualifyExprF, qualifyExpr, qualifyName_obj, Option.map_some,
            Aiur.Generic.Expr.map, List.map] at ev
          obtain ⟨ws, hargs, rfl⟩ := evalExprN_construct_inv ev
          cases hargs with | cons evE htl =>
          cases htl
          obtain ⟨v, hvQ, htvr, ext1⟩ := he _ h' evE
          obtain ⟨n, _, hn, rfl, rfl⟩ := TVR_nat_inv htvr
          exact ⟨.lit (.nat n), hvQ, .obj (.nat hn), ext1⟩
        · -- .w8, .nat b
          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
          obtain ⟨rfl, rfl⟩ := h0
          obtain ⟨v, hvQ, htvr, ext⟩ := he r h' ev
          obtain ⟨n, hn8, rfl, rfl⟩ := TVR_w8_inv htvr
          exact ⟨.lit (.nat n), hvQ, .nat ((hTarget _ hvQ).nat_bound (lt_trans hn8 (by decide))), ext⟩
        · -- .w8, .w16
          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
          obtain ⟨rfl, rfl⟩ := h0
          obtain ⟨v, hvQ, htvr, ext⟩ := he r h' ev
          obtain ⟨n, hn8, rfl, rfl⟩ := TVR_w8_inv htvr
          exact ⟨.lit (.nat n), hvQ, .w16 (by omega), ext⟩
        · -- .w8, .obj
          simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, hfM,
            Except.ok.injEq, Prod.mk.injEq] at h0
          obtain ⟨rfl, rfl⟩ := h0
          simp only [natE, mk, qualifyExprF, qualifyExpr, qualifyName_obj, Option.map_some,
            Aiur.Generic.Expr.map, List.map] at ev
          obtain ⟨ws, hargs, rfl⟩ := evalExprN_construct_inv ev
          cases hargs with | cons evE htl =>
          cases htl
          obtain ⟨v, hvQ, htvr, ext1⟩ := he _ h' evE
          obtain ⟨n, hn8, rfl, rfl⟩ := TVR_w8_inv htvr
          exact ⟨.lit (.nat n), hvQ, .obj (.nat (lt_trans hn8 (by decide))), ext1⟩
        · -- .w16, .nat b
          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
          obtain ⟨rfl, rfl⟩ := h0
          obtain ⟨v, hvQ, htvr, ext⟩ := he r h' ev
          obtain ⟨n, hn16, rfl, rfl⟩ := TVR_w16_inv htvr
          exact ⟨.lit (.nat n), hvQ, .nat ((hTarget _ hvQ).nat_bound (lt_trans hn16 (by decide))), ext⟩
        · -- .w16, .obj
          simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, hfM,
            Except.ok.injEq, Prod.mk.injEq] at h0
          obtain ⟨rfl, rfl⟩ := h0
          simp only [natE, mk, qualifyExprF, qualifyExpr, qualifyName_obj, Option.map_some,
            Aiur.Generic.Expr.map, List.map] at ev
          obtain ⟨ws, hargs, rfl⟩ := evalExprN_construct_inv ev
          cases hargs with | cons evE htl =>
          cases htl
          obtain ⟨v, hvQ, htvr, ext1⟩ := he _ h' evE
          obtain ⟨n, hn16, rfl, rfl⟩ := TVR_w16_inv htvr
          exact ⟨.lit (.nat n), hvQ, .obj (.nat (lt_trans hn16 (by decide))), ext1⟩
        · -- .enum ind, .obj
          rename_i ind
          obtain ⟨s1, _, _, h0⟩ := tMark_step_inv h0 hfM
            (fun _ => by constructor <;> first | exact id | (intro _; rfl))
          cases hE : cx.cert.enum? ind with
          | none => simp [hE, hfL, throw, throwThe, MonadExceptOf.throw] at h0
          | some ks =>
            simp only [hE] at h0
            obtain ⟨arms, s2, hmap, h0⟩ := tBind_step_inv h0
            simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
            obtain ⟨rfl, rfl⟩ := h0
            simp only [matchE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
            obtain ⟨w0, hm, bs, body, evE, hsel, evB⟩ := evalExprN_match_inv ev
            obtain ⟨v, hvQ, htvr, ext1⟩ := he w0 hm evE
            obtain ⟨ks', c, idx, entry, hE', hmem', hget, hkey, har, rfl, rfl⟩ := TVR_enum_inv htvr
            have hselInv : ∀ (ls : List CtorKey) (sA sB : TState) (as_ : List (Lower.Pat × Lower.Expr))
                (bs : Environment F Nat) (body : Aiur.Generic.Expr F),
                (ls.mapM (m := TLowerM) fun k =>
                  match cx.ctorEntry? k with
                  | some (idx', entry') =>
                    StateT.pure (Aiur.Generic.Pattern.construct (.named (enumName ind) []) (ctorNameOf idx' entry'.key) [],
                      mk (ctorNameOf idx' entry'.key) [])
                  | _ => fL (Except.error "coerce enum: missing ctor")) sA = .ok (as_, sB) →
                SourceSemantics.selectArm world [] hm (.construct (enumQName ind) (ctorNameOf idx c.key) [])
                  (as_.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) = .ok (some (bs, body)) →
                bs = [] ∧ body = qualifyExprF F (mk (ctorNameOf idx c.key) []) := by
              intro ls; induction ls with
              | nil =>
                intro sA sB as_ bs body hm0 hs
                simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
                  Except.ok.injEq, Prod.mk.injEq] at hm0
                obtain ⟨rfl, rfl⟩ := hm0; cases hs
              | cons k kt ihk =>
                intro sA sB as_ bs body hm0 hs
                rw [List.mapM_cons] at hm0
                obtain ⟨arm1, sa, h1, hm0⟩ := tBind_step_inv hm0
                obtain ⟨at_, sb, htl, hm0⟩ := tBind_step_inv hm0
                simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm0
                obtain ⟨rfl, rfl⟩ := hm0
                cases hce : cx.ctorEntry? k with
                | none => simp [hce, hfL] at h1
                | some ie =>
                  rcases ie with ⟨idx', entry'⟩
                  simp only [hce, StateT.pure, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1
                  obtain ⟨rfl, rfl⟩ := h1
                  simp only [List.map_cons, SourceSemantics.selectArm, qualifyPatF, qualifyPat,
                    qualifyTy, qualifyName_enumName, Aiur.Generic.Pattern.map, World.matchPattern,
                    matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol,
                    List.map_nil, List.isEmpty_nil, ↓reduceIte, List.length_nil, bne_self_eq_false,
                    Bool.false_or, Bool.or_false, bind, Except.bind, pure, Except.pure] at hs
                  by_cases hnm : ctorNameOf idx c.key = ctorNameOf idx' entry'.key
                  · have hbf : (ctorNameOf idx c.key != ctorNameOf idx' entry'.key) = false :=
                      by simp [hnm]
                    simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hs
                    obtain ⟨rfl, rfl⟩ := hs
                    exact ⟨rfl, by rw [hnm]⟩
                  · have hbt : (ctorNameOf idx c.key != ctorNameOf idx' entry'.key) = true :=
                      bne_iff_ne.mpr hnm
                    simp only [hbt, ↓reduceIte] at hs
                    exact ihk sA sb at_ bs body htl hs
            have hmap' : List.map
                ((fun a => (Aiur.Generic.Pattern.map Nat.cast a.1, Aiur.Generic.Expr.map Nat.cast a.2)) ∘
                  fun a => (qualifyPat a.1, qualifyExpr a.2)) arms =
                arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2) := rfl
            rw [List.map_map, hmap'] at hsel
            obtain ⟨rfl, rfl⟩ := hselInv ks s1 s2 arms _ _ hmap hsel
            simp only [mk, qualifyExprF, qualifyExpr, qualifyName_obj, Option.map_some,
              Aiur.Generic.Expr.map, List.map_nil] at evB
            obtain ⟨ws, hargs, rfl⟩ := evalExprN_construct_inv evB
            cases hargs
            exact ⟨.ctor c [], hvQ, .obj (.ctor hget hkey (by simp [har]) .nil), ext1⟩
        · -- .obj, .irr
          simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, hfM,
            Except.ok.injEq, Prod.mk.injEq] at h0
          obtain ⟨rfl, rfl⟩ := h0
          simp only [matchE, pC, qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, objTy,
            qualifyName_obj, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at ev
          obtain ⟨w0, hm, bs, body, evE, hsel, evB⟩ := evalExprN_match_inv ev
          obtain ⟨v, hvQ, htvr, ext1⟩ := he w0 hm evE
          have hvr := TVR_obj_inv htvr
          cases w0 with
          | field _ | tuple _ | ptr _ _ =>
            simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, bind, Except.bind,
              pure, Except.pure] at hsel
          | construct en cn args =>
            simp only [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
              constructorName, Ty.subst, Ty.toCore, Instance.symbol, List.map_nil, List.isEmpty_nil,
              ↓reduceIte, List.length_nil, bind, Except.bind, pure, Except.pure] at hsel
            by_cases hcond : (en != objQName || cn != "E" || 0 != args.length) = true
            · simp [hcond] at hsel
            · have hcf0 : (en != objQName || cn != "E" || 0 != args.length) = false :=
                Bool.eq_false_iff.mpr hcond
              rw [hcf0] at hsel
              simp only [Bool.false_eq_true, ↓reduceIte] at hsel
              simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hcf0
              obtain ⟨⟨rfl, rfl⟩, hlen0⟩ := hcf0
              cases args with
              | cons _ _ => simp at hlen0
              | nil =>
                simp [matchListWith] at hsel
                obtain ⟨rfl, rfl⟩ := hsel
                have hvEq := VR_E_inv hvr
                subst hvEq
                obtain ⟨rfl, rfl⟩ := evalExprN_tuple0_inv evB
                exact ⟨.erased, hvQ, .irr, ext1⟩
        · -- .obj, .nat b
          simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, hfM, hfF,
            Except.ok.injEq, Prod.mk.injEq] at h0
          obtain ⟨rfl, rfl⟩ := h0
          simp only [matchE, pN, vE, qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, objTy,
            qualifyName_obj, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at ev
          obtain ⟨w0, hm, bs, body, evE, hsel, evB⟩ := evalExprN_match_inv ev
          obtain ⟨v, hvQ, htvr, ext1⟩ := he w0 hm evE
          have hvr := TVR_obj_inv htvr
          cases w0 with
          | field _ | tuple _ | ptr _ _ =>
            simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, bind, Except.bind,
              pure, Except.pure] at hsel
          | construct en cn args =>
            simp only [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
              constructorName, Ty.subst, Ty.toCore, Instance.symbol, List.map_nil, List.isEmpty_nil,
              ↓reduceIte, List.length_cons, List.length_nil, bind, Except.bind, pure, Except.pure] at hsel
            by_cases hcond : (en != objQName || cn != "N" || 1 != args.length) = true
            · simp [hcond] at hsel
            · have hcf0 : (en != objQName || cn != "N" || 1 != args.length) = false :=
                Bool.eq_false_iff.mpr hcond
              rw [hcf0] at hsel
              simp only [Bool.false_eq_true, ↓reduceIte] at hsel
              simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hcf0
              obtain ⟨⟨rfl, rfl⟩, hlen1⟩ := hcf0
              rcases args with _ | ⟨x, _ | _⟩ <;> try (simp at hlen1)
              simp [matchListWith, matchPatternWith] at hsel
              obtain ⟨rfl, rfl⟩ := hsel
              obtain ⟨n, hn, rfl, rfl⟩ := VR_N_inv hvr
              obtain ⟨hl, rfl⟩ := evalExprN_var_inv evB
              simp only [List.cons_append, List.nil_append, List.find?_cons, beq_self_eq_true,
                Option.some.injEq, Prod.mk.injEq] at hl
              obtain ⟨_, rfl⟩ := hl
              exact ⟨.lit (.nat n), hvQ, .nat ((hTarget _ hvQ).nat_bound hn), ext1⟩
        · -- .obj, .w8
          simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, hfM, hfF,
            Except.ok.injEq, Prod.mk.injEq] at h0
          obtain ⟨rfl, rfl⟩ := h0
          simp only [matchE, pN, vE, qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, objTy,
            qualifyName_obj, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at ev
          obtain ⟨w0, hm, bs, body, evE, hsel, evB⟩ := evalExprN_match_inv ev
          obtain ⟨v, hvQ, htvr, ext1⟩ := he w0 hm evE
          have hvr := TVR_obj_inv htvr
          cases w0 with
          | field _ | tuple _ | ptr _ _ =>
            simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, bind, Except.bind,
              pure, Except.pure] at hsel
          | construct en cn args =>
            simp only [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
              constructorName, Ty.subst, Ty.toCore, Instance.symbol, List.map_nil, List.isEmpty_nil,
              ↓reduceIte, List.length_cons, List.length_nil, bind, Except.bind, pure, Except.pure] at hsel
            by_cases hcond : (en != objQName || cn != "N" || 1 != args.length) = true
            · simp [hcond] at hsel
            · have hcf0 : (en != objQName || cn != "N" || 1 != args.length) = false :=
                Bool.eq_false_iff.mpr hcond
              rw [hcf0] at hsel
              simp only [Bool.false_eq_true, ↓reduceIte] at hsel
              simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hcf0
              obtain ⟨⟨rfl, rfl⟩, hlen1⟩ := hcf0
              rcases args with _ | ⟨x, _ | _⟩ <;> try (simp at hlen1)
              simp [matchListWith, matchPatternWith] at hsel
              obtain ⟨rfl, rfl⟩ := hsel
              obtain ⟨n, _, rfl, rfl⟩ := VR_N_inv hvr
              obtain ⟨hl, rfl⟩ := evalExprN_var_inv evB
              simp only [List.cons_append, List.nil_append, List.find?_cons, beq_self_eq_true,
                Option.some.injEq, Prod.mk.injEq] at hl
              obtain ⟨_, rfl⟩ := hl
              exact ⟨.lit (.nat n), hvQ, .w8 ((hTarget _ hvQ).w8_bound), ext1⟩
        · -- .obj, .w16
          simp only [bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, hfM, hfF,
            Except.ok.injEq, Prod.mk.injEq] at h0
          obtain ⟨rfl, rfl⟩ := h0
          simp only [matchE, pN, vE, qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, objTy,
            qualifyName_obj, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at ev
          obtain ⟨w0, hm, bs, body, evE, hsel, evB⟩ := evalExprN_match_inv ev
          obtain ⟨v, hvQ, htvr, ext1⟩ := he w0 hm evE
          have hvr := TVR_obj_inv htvr
          cases w0 with
          | field _ | tuple _ | ptr _ _ =>
            simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, bind, Except.bind,
              pure, Except.pure] at hsel
          | construct en cn args =>
            simp only [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
              constructorName, Ty.subst, Ty.toCore, Instance.symbol, List.map_nil, List.isEmpty_nil,
              ↓reduceIte, List.length_cons, List.length_nil, bind, Except.bind, pure, Except.pure] at hsel
            by_cases hcond : (en != objQName || cn != "N" || 1 != args.length) = true
            · simp [hcond] at hsel
            · have hcf0 : (en != objQName || cn != "N" || 1 != args.length) = false :=
                Bool.eq_false_iff.mpr hcond
              rw [hcf0] at hsel
              simp only [Bool.false_eq_true, ↓reduceIte] at hsel
              simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hcf0
              obtain ⟨⟨rfl, rfl⟩, hlen1⟩ := hcf0
              rcases args with _ | ⟨x, _ | _⟩ <;> try (simp at hlen1)
              simp [matchListWith, matchPatternWith] at hsel
              obtain ⟨rfl, rfl⟩ := hsel
              obtain ⟨n, _, rfl, rfl⟩ := VR_N_inv hvr
              obtain ⟨hl, rfl⟩ := evalExprN_var_inv evB
              simp only [List.cons_append, List.nil_append, List.find?_cons, beq_self_eq_true,
                Option.some.injEq, Prod.mk.injEq] at hl
              obtain ⟨_, rfl⟩ := hl
              exact ⟨.lit (.nat n), hvQ, .w16 ((hTarget _ hvQ).w16_bound), ext1⟩
        · -- .obj, .enum ind
          rename_i ind
          obtain ⟨s1, _, _, h0⟩ := tMark_step_inv h0 hfM
            (fun _ => by constructor <;> first | exact id | (intro _; rfl))
          cases hE : cx.cert.enum? ind with
          | none => simp [hE, hfL, throw, throwThe, MonadExceptOf.throw] at h0
          | some ks =>
            simp only [hE] at h0
            obtain ⟨arms, s2, hmap, h0⟩ := tBind_step_inv h0
            simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
            obtain ⟨rfl, rfl⟩ := h0
            simp only [matchE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
            obtain ⟨w0, hm, bs, body, evE, hsel, evB⟩ := evalExprN_match_inv ev
            obtain ⟨v, hvQ, htvr, ext1⟩ := he w0 hm evE
            have hvr := TVR_obj_inv htvr
            have hselInv : ∀ (ls : List CtorKey) (sA sB : TState) (as_ : List (Lower.Pat × Lower.Expr))
                (bs : Environment F Nat) (body : Aiur.Generic.Expr F),
                (∀ k ∈ ls, k ∈ ks) →
                (ls.mapM (m := TLowerM) fun k =>
                  match cx.ctorEntry? k with
                  | some (idx', entry') =>
                    StateT.pure (pC (ctorNameOf idx' entry'.key) [],
                      Aiur.Generic.Expr.construct (enumName ind) (some []) (ctorNameOf idx' entry'.key) [])
                  | _ => fL (Except.error "coerce obj→enum: missing ctor")) sA = .ok (as_, sB) →
                SourceSemantics.selectArm world [] hm w0
                  (as_.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) = .ok (some (bs, body)) →
                ∃ k idx' entry', k ∈ ks ∧ P.ctors[idx']? = some entry' ∧ entry'.key = k ∧
                  w0 = .construct objQName (ctorNameOf idx' entry'.key) [] ∧
                  bs = [] ∧
                  body = qualifyExprF F (.construct (enumName ind) (some []) (ctorNameOf idx' entry'.key) []) := by
              intro ls; induction ls with
              | nil =>
                intro sA sB as_ bs body _ hm0 hs
                simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
                  Except.ok.injEq, Prod.mk.injEq] at hm0
                obtain ⟨rfl, rfl⟩ := hm0; cases hs
              | cons k kt ihk =>
                intro sA sB as_ bs body hsub hm0 hs
                rw [List.mapM_cons] at hm0
                obtain ⟨arm1, sa, h1, hm0⟩ := tBind_step_inv hm0
                obtain ⟨at_, sb, htl, hm0⟩ := tBind_step_inv hm0
                simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm0
                obtain ⟨rfl, rfl⟩ := hm0
                cases hce : cx.ctorEntry? k with
                | none => simp [hce, hfL] at h1
                | some ie =>
                  rcases ie with ⟨idx', entry'⟩
                  simp only [hce, StateT.pure, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1
                  obtain ⟨rfl, rfl⟩ := h1
                  cases w0 with
                  | field _ | tuple _ | ptr _ _ =>
                    simp only [List.map_cons, SourceSemantics.selectArm, pC, qualifyPatF, qualifyPat,
                      qualifyTy, objTy, qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern,
                      matchPatternWith, bind, Except.bind, pure, Except.pure] at hs
                    exact ihk sA sb at_ bs body (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) htl hs
                  | construct en cn args =>
                    simp only [List.map_cons, SourceSemantics.selectArm, pC, qualifyPatF, qualifyPat,
                      qualifyTy, objTy, qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern,
                      matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol,
                      List.map_nil, List.isEmpty_nil, ↓reduceIte, List.length_nil,
                      bind, Except.bind, pure, Except.pure] at hs
                    by_cases hcond : (en != objQName || cn != ctorNameOf idx' entry'.key || 0 != args.length) = true
                    · simp only [hcond, ↓reduceIte] at hs
                      exact ihk sA sb at_ bs body (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) htl hs
                    · have hcf0 : (en != objQName || cn != ctorNameOf idx' entry'.key || 0 != args.length) = false :=
                        Bool.eq_false_iff.mpr hcond
                      rw [hcf0] at hs
                      simp only [Bool.false_eq_true, ↓reduceIte] at hs
                      simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hcf0
                      obtain ⟨⟨rfl, rfl⟩, hlen0⟩ := hcf0
                      cases args with
                      | cons _ _ => simp at hlen0
                      | nil =>
                        simp [matchListWith] at hs
                        obtain ⟨rfl, rfl⟩ := hs
                        obtain ⟨hget', hkey'⟩ := ctorEntry?_sound hce
                        exact ⟨k, idx', entry', hsub k List.mem_cons_self, hget', hkey', rfl, rfl, rfl⟩
            have hmap' : List.map
                ((fun a => (Aiur.Generic.Pattern.map Nat.cast a.1, Aiur.Generic.Expr.map Nat.cast a.2)) ∘
                  fun a => (qualifyPat a.1, qualifyExpr a.2)) arms =
                arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2) := rfl
            rw [List.map_map, hmap'] at hsel
            obtain ⟨k, idx', entry', hkMem, hget', hkey', rfl, rfl, rfl⟩ :=
              hselInv ks s1 s2 arms _ _ (fun _ hx => hx) hmap hsel
            obtain ⟨c, fs, rfl, hckey, hflen, hvrs⟩ := VR_ctor_inv hnd hget' hvr
            cases hvrs
            simp only [qualifyExprF, qualifyExpr, qualifyName_enumName, Option.map_some,
              Aiur.Generic.Expr.map, List.map_nil] at evB
            obtain ⟨ws, hargs, rfl⟩ := evalExprN_construct_inv evB
            cases hargs
            have har0 : entry'.arity = 0 := by simpa using hflen.symm
            have hkeyEq : entry'.key = c.key := hckey.symm
            refine ⟨.ctor c [], hvQ, ?_, ext1⟩
            rw [hkeyEq]
            exact .enumVal hE (by rw [← hkeyEq, hkey']; exact hkMem) hget' hkeyEq har0
    exact go fromR toR hco (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) hcf hct he hTarget

theorem eval_coerceEAux {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld P cert sched lp world)
    (hwf : cert.WF) (_hkeys : (P.ctors.map (·.key)).Nodup) (hnd : (objCtorNames P).Nodup)
    (hdatas : datasNatCoreReps P cert (scanFeatures P) = true) :
    ∀ (fuel : Nat) (fromR toR : Rep) (e : Lower.Expr) (st st' : TState) (res : Lower.Expr)
      {dDepth : Nat} {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F}
      {Q : Fir.Val → Prop},
      let cx : TCx := { P, cert, feat := scanFeatures P, sched }
      coerceEAux fuel cx fromR toR e st = .ok (res, st') →
      isNatCoreRep fromR = true →
      isNatCoreRep toR = true →
      DemandLe st'.demand lp.demand →
      EvalExprN world dDepth [] locals (qualifyExprF F res) h r h' →
      (∀ w0 hm, EvalExprN world dDepth [] locals (qualifyExprF F e) h w0 hm →
        ∃ v, Q v ∧ TVR P cert (scanFeatures P) hm fromR v w0 ∧ Heap.Extends h hm) →
      (∀ v, Q v → CoerceTargetOk P cert (scanFeatures P) toR v) →
      ∃ v, Q v ∧ TVR P cert (scanFeatures P) h' toR v r ∧ Heap.Extends h h' := by
  intro fuel
  induction fuel with
  | zero => exact eval_coerceEAux_zero fc lw hnd
  | succ fuel' ih =>
    intro fromR toR e st st' res dDepth locals h h' r Q cx hco hcf hct hdem ev he hTarget
    unfold coerceEAux at hco
    by_cases heq : (fromR == toR) = true
    · simp only [heq, ↓reduceIte, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hco
      obtain ⟨rfl, rfl⟩ := hco
      have hfrEq : fromR = toR := beq_iff_eq.mp heq
      subst hfrEq
      exact he r h' ev
    · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hco
      -- Split on the two recursive `.data d ↔ .obj` cases; all other cases delegate directly to `fuel = 0`!
      cases fromR with
      | data d =>
        cases toR with
        | obj =>
          have go : ∀ {fFL : Nat → TLowerM (List String)}
              {fL : {α : Type} → Except String α → TLowerM α}
              {fM : (Demand → Demand) → TLowerM Unit},
              (do fM fun d0 => { d0 with needObj := true }
                  let some D := cx.cert.data? d | fL (throw s!"coerce: unknown data {d}")
                  let arms ← D.ctors.mapM fun ((k, fl) : CtorKey × List Shape) => do
                    let some (idx, entry) := cx.ctorEntry? k | fL (throw "coerce data: missing ctor")
                    let nm := ctorNameOf idx entry.key
                    let fvars ← fFL fl.length
                    let fieldExprs ← (fl.zip fvars).mapM fun ((sh, fv) : Shape × String) => do
                      let fr := cx.rep sh
                      let raw : Lower.Expr := if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.load (vE fv) else vE fv
                      let asObj ← coerceEAux fuel' cx fr .obj raw
                      return Aiur.Generic.Expr.store asObj
                    return (Aiur.Generic.Pattern.construct (.named (dataName d) []) nm (fvars.map .bind),
                      mk nm fieldExprs)
                  return matchE e arms) st = .ok (res, st') →
              (∀ n s, fFL n s = .ok ((List.range n).map (fun i => localName (s.nextLocal + i)),
                { s with nextLocal := s.nextLocal + n })) →
              (∀ {α} (x : Except String α) s, fL x s = match x with | .ok a => .ok (a, s) | .error err => .error err) →
              (∀ u s, fM u s = .ok ((), { s with demand := u s.demand })) →
              ∃ v, Q v ∧ TVR P cert (scanFeatures P) h' .obj v r ∧ Heap.Extends h h' := by
            intro fFL fL fM h0 hfFL hfL hfM
            obtain ⟨s1, _, _, h0⟩ := tMark_step_inv h0 hfM
              (fun _ => by constructor <;> first | exact id | (intro _; rfl))
            cases hD : cx.cert.data? d with
            | none => simp [hD, hfL, throw, throwThe, MonadExceptOf.throw] at h0
            | some D =>
              simp only [hD] at h0
              obtain ⟨arms, s2, hmap, h0⟩ := tBind_step_inv h0
              simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
              obtain ⟨rfl, rfl⟩ := h0
              simp only [matchE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
              obtain ⟨w0, hm, bs, body, evE, hsel, evB⟩ := evalExprN_match_inv ev
              obtain ⟨v, hvQ, htvr, ext1⟩ := he w0 hm evE
              obtain ⟨D', c, fl, idx, entry, fs, ws, hD', hcMem, hget, hkey, hflen, hfllen, hfields, rfl, rfl⟩ :=
                TVR_data_inv htvr
              rw [hD, Option.some.injEq] at hD'; subst hD'
              have hwsLen : ws.length = fl.length := by
                have ⟨h1, h2⟩ := hfields.length_eq; omega
              -- Step 1: evaluate the per-field `mapM` back to `VRs`.
              have hfieldEv :
                  ∀ (fl' : List Shape) (fvars : List String) (fs' : List Fir.Val) (ws' : List (SourceValue F))
                    (sA sB : TState) (fes : List Lower.Expr)
                    (loc' : Environment F Nat) (hA hB : Heap F) (ps : List (SourceValue F)),
                    (∀ sh ∈ fl', sh ∈ fl) →
                    TVRDataFields P cert (scanFeatures P) hA d fl' fs' ws' →
                    EvalCapArgs loc' fvars ws' →
                    ((fl'.zip fvars).mapM (m := TLowerM) fun ((sh, fv) : Shape × String) => do
                      let fr := cx.rep sh
                      let raw := if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .load (vE fv) else vE fv
                      let asObj ← coerceEAux fuel' cx fr .obj raw
                      pure (Aiur.Generic.Expr.store asObj)) sA = .ok (fes, sB) →
                    DemandLe sB.demand lp.demand →
                    EvalArgsN world dDepth [] loc' (fes.map (qualifyExprF F)) hA ps hB →
                    VRs P objQName bytesQName hB fs' ps ∧ Heap.Extends hA hB := by
                intro fl'; induction fl' with
                | nil =>
                  intro fvars fs' ws' sA sB fes loc' hA hB ps _ hdf hcap hfm _ hargs
                  cases hdf
                  cases fvars with
                  | nil =>
                    simp only [List.zip_nil_left, List.mapM, List.mapM.loop, pure, StateT.pure,
                      Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfm
                    obtain ⟨rfl, rfl⟩ := hfm
                    cases hargs
                    exact ⟨.nil, Heap.Extends.refl _⟩
                  | cons _ _ => exact False.elim hcap
                | cons sh sht ihf =>
                  intro fvars fs' ws' sA sB fes loc' hA hB ps hsub hdf hcap hfm hdemB hargs
                  cases fvars with
                  | nil => cases hdf <;> exact False.elim hcap
                  | cons fv fvt =>
                    cases hcap_eq : ws' with
                    | nil => rw [hcap_eq] at hdf; cases hdf
                    | cons wRaw wRest =>
                      rw [hcap_eq] at hdf hcap
                      obtain ⟨hlocFv, hcapRest⟩ := hcap
                      simp only [List.zip_cons_cons, List.mapM_cons] at hfm
                      obtain ⟨fe1, sMid, hfe1, hfm⟩ := tBind_step_inv hfm
                      obtain ⟨fet, sEnd, hfet, hfm⟩ := tBind_step_inv hfm
                      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfm
                      obtain ⟨rfl, rfl⟩ := hfm
                      obtain ⟨asObj, sMid', hco1, hfe1⟩ := tBind_step_inv hfe1
                      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfe1
                      obtain ⟨rfl, rfl⟩ := hfe1
                      have hleRest : TStateLe sMid' sEnd := by
                        have aux : ∀ (prs : List (Shape × String)) (x0 x1 : TState) (es0 : List Lower.Expr),
                            (prs.mapM (m := TLowerM) fun ((s0, f0) : Shape × String) => do
                              let fr := cx.rep s0
                              let raw := if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .load (vE f0) else vE f0
                              let asObj ← coerceEAux fuel' cx fr .obj raw
                              pure (Aiur.Generic.Expr.store asObj)) x0 = .ok (es0, x1) →
                            TStateLe x0 x1 := by
                          intro prs; induction prs with
                          | nil =>
                            intro x0 x1 es0 hm'; simp only [List.mapM, List.mapM.loop, pure,
                              StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm'
                            obtain ⟨_, rfl⟩ := hm'; exact TStateLe.refl _
                          | cons p0 pt0 ihp0 =>
                            intro x0 x1 es0 hm'; rw [List.mapM_cons] at hm'
                            obtain ⟨_, xa, ha, hm'⟩ := tBind_step_inv hm'
                            obtain ⟨_, xb, hb, hm'⟩ := tBind_step_inv hm'
                            simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm'
                            obtain ⟨_, rfl⟩ := hm'
                            obtain ⟨_, xa', hca, ha⟩ := tBind_step_inv ha
                            simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ha
                            obtain ⟨_, rfl⟩ := ha
                            exact (coerceEAux_spec _ _ _ _ _ _ _ _ hca).1.trans (ihp0 xa' xb _ hb)
                        exact aux _ sMid' sEnd fet hfet
                      simp only [List.map_cons] at hargs
                      cases hargs with
                      | cons evSt evRest =>
                        rename_i p1 hMid psRest
                        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evSt
                        obtain ⟨wObj, hPre, evObj, rfl, rfl⟩ := evalExprN_store_inv evSt
                        have hcoreSh : isNatCoreRep (cx.rep sh) = true :=
                          datasNatCoreReps_field hdatas hD hcMem (hsub sh List.mem_cons_self)
                        cases hdf with
                        | consInline hnp htvr1 hdfRest =>
                          rename_i v1 vsRest
                          obtain ⟨v1', hv1Eq, htvrObj, extObj⟩ :=
                            ih (cx.rep sh) .obj _ sA sMid' asObj hco1 hcoreSh rfl
                              (hleRest.demand.trans hdemB) evObj
                              (Q := fun v' => v' = v1)
                              (fun w1 hm1 evRaw => by
                                dsimp only [cx, TCx.rep] at evRaw
                                simp only [hnp, Bool.false_eq_true, ↓reduceIte, vE, qualifyExprF,
                                  qualifyExpr, Aiur.Generic.Expr.map] at evRaw
                                obtain ⟨hl', rfl⟩ := evalExprN_var_inv evRaw
                                rw [hlocFv, Option.some.injEq, Prod.mk.injEq] at hl'
                                obtain ⟨_, rfl⟩ := hl'
                                exact ⟨v1, rfl, htvr1, Heap.Extends.refl _⟩)
                              (fun _ _ => Or.inl rfl)
                          subst hv1Eq
                          have hvr1 := TVR_obj_inv htvrObj
                          have extSt : Heap.Extends hA (hPre ++ [wObj]) :=
                            extObj.trans (Heap.Extends.append_right hPre [wObj])
                          obtain ⟨hvrsRest, extRest⟩ :=
                            ihf fvt vsRest wRest sMid' sEnd fet loc' (hPre ++ [wObj]) hB psRest
                              (fun s' hs' => hsub s' (List.mem_cons_of_mem _ hs'))
                              (hdfRest.extend extSt) hcapRest hfet hdemB evRest
                          have htype : wObj.type = .enum objQName := hvr1.type_eq
                          have hatAddr : hB[hPre.length]? = some wObj :=
                            extRest.getElem?_eq (by simp)
                          rw [htype]
                          exact ⟨.cons hatAddr (hvr1.extend ((Heap.Extends.append_right hPre [wObj]).trans extRest)) hvrsRest,
                            extSt.trans extRest⟩
                        | consPtr hp hatA htvr1 hdfRest =>
                          rename_i v1 vsRest addr1 wDeref
                          obtain ⟨v1', hv1Eq, htvrObj, extObj⟩ :=
                            ih (cx.rep sh) .obj _ sA sMid' asObj hco1 hcoreSh rfl
                              (hleRest.demand.trans hdemB) evObj
                              (Q := fun v' => v' = v1)
                              (fun w1 hm1 evRaw => by
                                dsimp only [cx, TCx.rep] at evRaw
                                simp only [hp, ↓reduceIte, vE, qualifyExprF, qualifyExpr,
                                  Aiur.Generic.Expr.map] at evRaw
                                obtain ⟨vp, evVar, hload⟩ := evalExprN_load_inv evRaw
                                obtain ⟨hl', rfl⟩ := evalExprN_var_inv evVar
                                rw [hlocFv, Option.some.injEq, Prod.mk.injEq] at hl'
                                obtain ⟨_, rfl⟩ := hl'
                                simp [loadValue, hatA] at hload
                                subst hload
                                exact ⟨v1, rfl, htvr1, Heap.Extends.refl _⟩)
                              (fun _ _ => Or.inl rfl)
                          subst hv1Eq
                          have hvr1 := TVR_obj_inv htvrObj
                          have extSt : Heap.Extends hA (hPre ++ [wObj]) :=
                            extObj.trans (Heap.Extends.append_right hPre [wObj])
                          obtain ⟨hvrsRest, extRest⟩ :=
                            ihf fvt vsRest wRest sMid' sEnd fet loc' (hPre ++ [wObj]) hB psRest
                              (fun s' hs' => hsub s' (List.mem_cons_of_mem _ hs'))
                              (hdfRest.extend extSt) hcapRest hfet hdemB evRest
                          have htype : wObj.type = .enum objQName := hvr1.type_eq
                          have hatAddr : hB[hPre.length]? = some wObj :=
                            extRest.getElem?_eq (by simp)
                          rw [htype]
                          exact ⟨.cons hatAddr (hvr1.extend ((Heap.Extends.append_right hPre [wObj]).trans extRest)) hvrsRest,
                            extSt.trans extRest⟩
              -- Step 2: invert `selectArm` over `D.ctors` to find the matched constructor arm.
              have harmsInv : ∀ (cs : List (CtorKey × List Shape)) (sA sB : TState)
                  (as_ : List (Lower.Pat × Lower.Expr)) (bs : Environment F Nat) (body : Aiur.Generic.Expr F),
                  (∀ x ∈ cs, x ∈ D.ctors) →
                  (cs.mapM (m := TLowerM) fun ((k, fl') : CtorKey × List Shape) => do
                    let some (idx', entry') := cx.ctorEntry? k | fL (throw "coerce data: missing ctor")
                    let nm := ctorNameOf idx' entry'.key
                    let fvars ← fFL fl'.length
                    let fieldExprs ← (fl'.zip fvars).mapM fun ((sh, fv) : Shape × String) => do
                      let fr := cx.rep sh
                      let raw := if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .load (vE fv) else vE fv
                      let asObj ← coerceEAux fuel' cx fr .obj raw
                      return Aiur.Generic.Expr.store asObj
                    return (Aiur.Generic.Pattern.construct (.named (dataName d) []) nm (fvars.map .bind),
                      mk nm fieldExprs)) sA = .ok (as_, sB) →
                  DemandLe sB.demand lp.demand →
                  SourceSemantics.selectArm world [] hm (.construct (dataQName d) (ctorNameOf idx c.key) ws)
                    (as_.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) = .ok (some (bs, body)) →
                  ∃ fvars fes sF1 sF2,
                    fvars.Nodup ∧ fvars.length = fl.length ∧
                    bs = fvars.zip ws ∧
                    body = qualifyExprF F (mk (ctorNameOf idx c.key) fes) ∧
                    DemandLe sF2.demand lp.demand ∧
                    ((fl.zip fvars).mapM (m := TLowerM) fun ((sh, fv) : Shape × String) => do
                      let fr := cx.rep sh
                      let raw := if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .load (vE fv) else vE fv
                      let asObj ← coerceEAux fuel' cx fr .obj raw
                      pure (Aiur.Generic.Expr.store asObj)) sF1 = .ok (fes, sF2) := by
                intro cs; induction cs with
                | nil =>
                  intro sA sB as_ bs body _ hm0 _ hs
                  simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
                    Except.ok.injEq, Prod.mk.injEq] at hm0
                  obtain ⟨rfl, rfl⟩ := hm0; cases hs
                | cons cf ct ihc =>
                  intro sA sB as_ bs body hsub hm0 hdemB hs
                  rcases cf with ⟨k, fl'⟩
                  rw [List.mapM_cons] at hm0
                  obtain ⟨arm1, sArm, h1, hm0⟩ := tBind_step_inv hm0
                  obtain ⟨at_, sEnd, htl, hm0⟩ := tBind_step_inv hm0
                  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm0
                  obtain ⟨rfl, rfl⟩ := hm0
                  -- Monotonicity of tail `htl`
                  have hleTail : TStateLe sArm sEnd := by
                    have aux : ∀ (l0 : List (CtorKey × List Shape)) (x0 x1 : TState) (a0 : List (Lower.Pat × Lower.Expr)),
                        (l0.mapM (m := TLowerM) fun ((k0, fl0) : CtorKey × List Shape) => do
                          let some (idx', entry') := cx.ctorEntry? k0 | fL (throw "coerce data: missing ctor")
                          let nm := ctorNameOf idx' entry'.key
                          let fvars ← fFL fl0.length
                          let fieldExprs ← (fl0.zip fvars).mapM fun ((sh, fv) : Shape × String) => do
                            let fr := cx.rep sh
                            let raw := if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .load (vE fv) else vE fv
                            let asObj ← coerceEAux fuel' cx fr .obj raw
                            return Aiur.Generic.Expr.store asObj
                          return (Aiur.Generic.Pattern.construct (.named (dataName d) []) nm (fvars.map .bind),
                            mk nm fieldExprs)) x0 = .ok (a0, x1) → TStateLe x0 x1 := by
                      intro l0; induction l0 with
                      | nil =>
                        intro x0 x1 a0 hm'; simp only [List.mapM, List.mapM.loop, pure, StateT.pure,
                          Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm'
                        obtain ⟨_, rfl⟩ := hm'; exact TStateLe.refl _
                      | cons c0 ct0 ih0 =>
                        intro x0 x1 a0 hm'; rw [List.mapM_cons] at hm'
                        obtain ⟨_, xa, ha, hm'⟩ := tBind_step_inv hm'
                        obtain ⟨_, xb, hb, hm'⟩ := tBind_step_inv hm'
                        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm'
                        obtain ⟨_, rfl⟩ := hm'
                        cases hce0 : cx.ctorEntry? c0.1 with
                        | none => simp [hce0, hfL, throw, throwThe, MonadExceptOf.throw] at ha
                        | some _ =>
                          simp only [hce0] at ha
                          obtain ⟨_, xa1, hfv0, ha⟩ := tBind_step_inv ha
                          rw [hfFL] at hfv0; simp only [Except.ok.injEq, Prod.mk.injEq] at hfv0
                          obtain ⟨rfl, rfl⟩ := hfv0
                          obtain ⟨_, xa2, hfe0, ha⟩ := tBind_step_inv ha
                          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ha
                          obtain ⟨_, rfl⟩ := ha
                          have hleA : TStateLe x0 { x0 with nextLocal := x0.nextLocal + c0.2.length } :=
                            ⟨Nat.le_add_right _ _, Nat.le_refl _, rfl, DemandLe.refl _⟩
                          have hleB : TStateLe { x0 with nextLocal := x0.nextLocal + c0.2.length } xa2 := by
                            have auxF : ∀ (prs : List (Shape × String)) (y0 y1 : TState) (es0 : List Lower.Expr),
                                (prs.mapM (m := TLowerM) fun ((s0, f0) : Shape × String) => do
                                  let fr := cx.rep s0
                                  let raw := if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then .load (vE f0) else vE f0
                                  let asObj ← coerceEAux fuel' cx fr .obj raw
                                  pure (Aiur.Generic.Expr.store asObj)) y0 = .ok (es0, y1) → TStateLe y0 y1 := by
                              intro prs; induction prs with
                              | nil =>
                                intro y0 y1 es0 hfm'; simp only [List.mapM, List.mapM.loop, pure,
                                  StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfm'
                                obtain ⟨_, rfl⟩ := hfm'; exact TStateLe.refl _
                              | cons p0 pt0 ihp0 =>
                                intro y0 y1 es0 hfm'; rw [List.mapM_cons] at hfm'
                                obtain ⟨_, ya, hya, hfm'⟩ := tBind_step_inv hfm'
                                obtain ⟨_, yb, hyb, hfm'⟩ := tBind_step_inv hfm'
                                simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfm'
                                obtain ⟨_, rfl⟩ := hfm'
                                obtain ⟨_, ya', hca, hya⟩ := tBind_step_inv hya
                                simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hya
                                obtain ⟨_, rfl⟩ := hya
                                exact (coerceEAux_spec _ _ _ _ _ _ _ _ hca).1.trans (ihp0 ya' yb _ hyb)
                            exact auxF _ _ xa2 _ hfe0
                          exact (hleA.trans hleB).trans (ih0 xa2 xb _ hb)
                    exact aux ct sArm sEnd at_ htl
                  cases hce : cx.ctorEntry? k with
                  | none => simp [hce, hfL, throw, throwThe, MonadExceptOf.throw] at h1
                  | some ie =>
                    rcases ie with ⟨idx', entry'⟩
                    simp only [hce] at h1
                    obtain ⟨fvars, sFv, hfv, h1⟩ := tBind_step_inv h1
                    rw [hfFL] at hfv
                    simp only [Except.ok.injEq, Prod.mk.injEq] at hfv
                    obtain ⟨rfl, rfl⟩ := hfv
                    obtain ⟨fes, sFe, hfe, h1⟩ := tBind_step_inv h1
                    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1
                    obtain ⟨rfl, rfl⟩ := h1
                    set fvs := (List.range fl'.length).map fun i => localName (sA.nextLocal + i)
                    have hpatMap :
                        List.map (Aiur.Generic.Pattern.map Nat.cast)
                          (List.map qualifyPat (fvs.map Aiur.Generic.Pattern.bind)) =
                        fvs.map (Aiur.Generic.Pattern.bind : String → Aiur.Generic.Pattern F) := by
                      induction fvs with
                      | nil => rfl
                      | cons _ _ _ => simp [qualifyPat, Aiur.Generic.Pattern.map]
                    simp only [List.map_cons, SourceSemantics.selectArm, qualifyPatF, qualifyPat,
                      qualifyTy, qualifyName_dataName, Aiur.Generic.Pattern.map, World.matchPattern,
                      matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol,
                      List.map_nil, List.isEmpty_nil, ↓reduceIte, hpatMap, List.length_map,
                      bne_self_eq_false, Bool.false_or, bind, Except.bind, pure, Except.pure] at hs
                    by_cases hcond : (ctorNameOf idx c.key != ctorNameOf idx' entry'.key || fvs.length != ws.length) = true
                    · simp only [hcond, ↓reduceIte] at hs
                      exact ihc sFe sEnd at_ bs body (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) htl hdemB hs
                    · have hcf0 : (ctorNameOf idx c.key != ctorNameOf idx' entry'.key || fvs.length != ws.length) = false :=
                        Bool.eq_false_iff.mpr hcond
                      rw [hcf0] at hs
                      simp only [Bool.false_eq_true, ↓reduceIte] at hs
                      simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hcf0
                      obtain ⟨hnmEq, hlenEq⟩ := hcf0
                      obtain ⟨hget', hkey'⟩ := ctorEntry?_sound hce
                      rw [← hkey] at hnmEq
                      obtain ⟨rfl, hentryEq⟩ := ctorNameOf_inj_of_nodup hnd hget hget' hnmEq
                      subst hentryEq
                      have hkEq : k = c.key := hkey'.symm.trans hkey
                      have hflEq : fl' = fl := hwf d D hD c.key fl' fl (hkEq ▸ hsub (k, fl') List.mem_cons_self) hcMem
                      subst hkEq hflEq
                      have hndFvs : fvs.Nodup :=
                        List.Nodup.map (fun _ _ heq => by have := localName_inj heq; omega) List.nodup_range
                      rw [matchListWith_attach_eq_t, matchListWith_binds fvs ws hlenEq.symm] at hs
                      obtain ⟨rfl, rfl⟩ := hs
                      exact ⟨fvs, fes, _, sFe, hndFvs, by simp [fvs], rfl, by rw [hkey],
                        hleTail.demand.trans hdemB, hfe⟩
              have hmap' : List.map
                  ((fun a => (Aiur.Generic.Pattern.map Nat.cast a.1, Aiur.Generic.Expr.map Nat.cast a.2)) ∘
                    fun a => (qualifyPat a.1, qualifyExpr a.2)) arms =
                  arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2) := rfl
              rw [List.map_map, hmap'] at hsel
              obtain ⟨fvars, fes, sF1, sF2, hfvNd, hfvLen, rfl, rfl, hdemF, hfe⟩ :=
                harmsInv D.ctors s1 s2 arms _ _ (fun _ hx => hx) hmap hdem hsel
              simp only [mk, qualifyExprF, qualifyExpr, qualifyName_obj, Option.map_some,
                Aiur.Generic.Expr.map, List.map_map] at evB
              obtain ⟨ps, hargsEv, rfl⟩ := evalExprN_construct_inv evB
              have hargsEv' : EvalArgsN world dDepth [] (fvars.zip ws ++ locals)
                  (fes.map (qualifyExprF F)) hm ps h' := hargsEv
              have hcapWs : EvalCapArgs (fvars.zip ws ++ locals) fvars ws :=
                EvalCapArgs.of_zip_nodup hfvNd (by omega)
              obtain ⟨hvrs, ext2⟩ :=
                hfieldEv fl fvars fs ws sF1 sF2 fes (fvars.zip ws ++ locals) hm h' ps
                  (fun _ hx => hx) hfields hcapWs hfe hdemF hargsEv'
              exact ⟨.ctor c fs, hvQ, .obj (.ctor hget hkey hflen hvrs), ext1.trans ext2⟩
          exact go hco (freshLocals_poly _ (fun _ => rfl) (fun _ _ => rfl))
            (fun _ _ => rfl) (fun _ _ => rfl)
        | irr | nat _ | w8 | w16 | w32 | w64 | «enum» _ | data _ =>
          exact eval_coerceEAux_zero fc lw hnd (.data d) _ e st st' res
            (by unfold coerceEAux; simp only [heq, Bool.false_eq_true, ↓reduceIte]; exact hco)
            hcf hct hdem ev he hTarget
      | obj =>
        cases toR with
        | data d =>
          have go : ∀ {fFL : Nat → TLowerM (List String)}
              {fL : {α : Type} → Except String α → TLowerM α}
              {fM : (Demand → Demand) → TLowerM Unit},
              (do fM fun d0 => { d0 with needObj := true }
                  let some D := cx.cert.data? d | fL (throw s!"coerce: unknown data {d}")
                  let arms ← D.ctors.mapM fun ((k, fl) : CtorKey × List Shape) => do
                    let some (idx, entry) := cx.ctorEntry? k | fL (throw "coerce obj→data: missing ctor")
                    let nm := ctorNameOf idx entry.key
                    let fvars ← fFL fl.length
                    let fieldExprs ← (fl.zip fvars).mapM fun ((sh, fv) : Shape × String) => do
                      let fr := cx.rep sh
                      let typed ← coerceEAux fuel' cx .obj fr (.load (vE fv))
                      return if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.store typed else typed
                    return (pC nm (fvars.map .bind),
                      Aiur.Generic.Expr.construct (dataName d) (some []) nm fieldExprs)
                  return matchE e arms) st = .ok (res, st') →
              (∀ n s, fFL n s = .ok ((List.range n).map (fun i => localName (s.nextLocal + i)),
                { s with nextLocal := s.nextLocal + n })) →
              (∀ {α} (x : Except String α) s, fL x s = match x with | .ok a => .ok (a, s) | .error err => .error err) →
              (∀ u s, fM u s = .ok ((), { s with demand := u s.demand })) →
              ∃ v, Q v ∧ TVR P cert (scanFeatures P) h' (.data d) v r ∧ Heap.Extends h h' := by
            intro fFL fL fM h0 hfFL hfL hfM
            obtain ⟨s1, _, _, h0⟩ := tMark_step_inv h0 hfM
              (fun _ => by constructor <;> first | exact id | (intro _; rfl))
            cases hD : cx.cert.data? d with
            | none => simp [hD, hfL, throw, throwThe, MonadExceptOf.throw] at h0
            | some D =>
              simp only [hD] at h0
              obtain ⟨arms, s2, hmap, h0⟩ := tBind_step_inv h0
              simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
              obtain ⟨rfl, rfl⟩ := h0
              simp only [matchE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
              obtain ⟨w0, hm, bs, body, evE, hsel, evB⟩ := evalExprN_match_inv ev
              obtain ⟨v, hvQ, htvr, ext1⟩ := he w0 hm evE
              have hvr := TVR_obj_inv htvr
              -- Invert `selectArm` over `D.ctors`
              have harmsInv : ∀ (cs : List (CtorKey × List Shape)) (sA sB : TState)
                  (as_ : List (Lower.Pat × Lower.Expr)) (bs : Environment F Nat) (body : Aiur.Generic.Expr F),
                  (∀ x ∈ cs, x ∈ D.ctors) →
                  (cs.mapM (m := TLowerM) fun ((k, fl') : CtorKey × List Shape) => do
                    let some (idx', entry') := cx.ctorEntry? k | fL (throw "coerce obj→data: missing ctor")
                    let nm := ctorNameOf idx' entry'.key
                    let fvars ← fFL fl'.length
                    let fieldExprs ← (fl'.zip fvars).mapM fun ((sh, fv) : Shape × String) => do
                      let fr := cx.rep sh
                      let typed ← coerceEAux fuel' cx .obj fr (.load (vE fv))
                      return if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.store typed else typed
                    return (pC nm (fvars.map .bind),
                      Aiur.Generic.Expr.construct (dataName d) (some []) nm fieldExprs)) sA = .ok (as_, sB) →
                  DemandLe sB.demand lp.demand →
                  SourceSemantics.selectArm world [] hm w0
                    (as_.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) = .ok (some (bs, body)) →
                  ∃ k fl' idx' entry' ps fvars fes sF1 sF2,
                    (k, fl') ∈ D.ctors ∧ P.ctors[idx']? = some entry' ∧ entry'.key = k ∧
                    w0 = .construct objQName (ctorNameOf idx' entry'.key) ps ∧
                    ps.length = fl'.length ∧ fvars.Nodup ∧ fvars.length = fl'.length ∧
                    bs = fvars.zip ps ∧
                    body = qualifyExprF F (.construct (dataName d) (some []) (ctorNameOf idx' entry'.key) fes) ∧
                    DemandLe sF2.demand lp.demand ∧
                    ((fl'.zip fvars).mapM (m := TLowerM) fun ((sh, fv) : Shape × String) => do
                      let fr := cx.rep sh
                      let typed ← coerceEAux fuel' cx .obj fr (.load (vE fv))
                      pure (if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.store typed else typed)) sF1 =
                      .ok (fes, sF2) := by
                intro cs; induction cs with
                | nil =>
                  intro sA sB as_ bs body _ hm0 _ hs
                  simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
                    Except.ok.injEq, Prod.mk.injEq] at hm0
                  obtain ⟨rfl, rfl⟩ := hm0; cases hs
                | cons cf ct ihc =>
                  intro sA sB as_ bs body hsub hm0 hdemB hs
                  rcases cf with ⟨k, fl'⟩
                  rw [List.mapM_cons] at hm0
                  obtain ⟨arm1, sArm, h1, hm0⟩ := tBind_step_inv hm0
                  obtain ⟨at_, sEnd, htl, hm0⟩ := tBind_step_inv hm0
                  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm0
                  obtain ⟨rfl, rfl⟩ := hm0
                  have hleTail : TStateLe sArm sEnd := by
                    have aux : ∀ (l0 : List (CtorKey × List Shape)) (x0 x1 : TState) (a0 : List (Lower.Pat × Lower.Expr)),
                        (l0.mapM (m := TLowerM) fun ((k0, fl0) : CtorKey × List Shape) => do
                          let some (idx', entry') := cx.ctorEntry? k0 | fL (throw "coerce obj→data: missing ctor")
                          let nm := ctorNameOf idx' entry'.key
                          let fvars ← fFL fl0.length
                          let fieldExprs ← (fl0.zip fvars).mapM fun ((sh, fv) : Shape × String) => do
                            let fr := cx.rep sh
                            let typed ← coerceEAux fuel' cx .obj fr (.load (vE fv))
                            return if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.store typed else typed
                          return (pC nm (fvars.map .bind),
                            Aiur.Generic.Expr.construct (dataName d) (some []) nm fieldExprs)) x0 = .ok (a0, x1) →
                          TStateLe x0 x1 := by
                      intro l0; induction l0 with
                      | nil =>
                        intro x0 x1 a0 hm'; simp only [List.mapM, List.mapM.loop, pure, StateT.pure,
                          Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm'
                        obtain ⟨_, rfl⟩ := hm'; exact TStateLe.refl _
                      | cons c0 ct0 ih0 =>
                        intro x0 x1 a0 hm'; rw [List.mapM_cons] at hm'
                        obtain ⟨_, xa, ha, hm'⟩ := tBind_step_inv hm'
                        obtain ⟨_, xb, hb, hm'⟩ := tBind_step_inv hm'
                        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm'
                        obtain ⟨_, rfl⟩ := hm'
                        cases hce0 : cx.ctorEntry? c0.1 with
                        | none => simp [hce0, hfL, throw, throwThe, MonadExceptOf.throw] at ha
                        | some _ =>
                          simp only [hce0] at ha
                          obtain ⟨_, xa1, hfv0, ha⟩ := tBind_step_inv ha
                          rw [hfFL] at hfv0; simp only [Except.ok.injEq, Prod.mk.injEq] at hfv0
                          obtain ⟨rfl, rfl⟩ := hfv0
                          obtain ⟨_, xa2, hfe0, ha⟩ := tBind_step_inv ha
                          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ha
                          obtain ⟨_, rfl⟩ := ha
                          have hleA : TStateLe x0 { x0 with nextLocal := x0.nextLocal + c0.2.length } :=
                            ⟨Nat.le_add_right _ _, Nat.le_refl _, rfl, DemandLe.refl _⟩
                          have hleB : TStateLe { x0 with nextLocal := x0.nextLocal + c0.2.length } xa2 := by
                            have auxF : ∀ (prs : List (Shape × String)) (y0 y1 : TState) (es0 : List Lower.Expr),
                                (prs.mapM (m := TLowerM) fun ((s0, f0) : Shape × String) => do
                                  let fr := cx.rep s0
                                  let typed ← coerceEAux fuel' cx .obj fr (.load (vE f0))
                                  pure (if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.store typed else typed)) y0 =
                                  .ok (es0, y1) → TStateLe y0 y1 := by
                              intro prs; induction prs with
                              | nil =>
                                intro y0 y1 es0 hfm'; simp only [List.mapM, List.mapM.loop, pure,
                                  StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfm'
                                obtain ⟨_, rfl⟩ := hfm'; exact TStateLe.refl _
                              | cons p0 pt0 ihp0 =>
                                intro y0 y1 es0 hfm'; rw [List.mapM_cons] at hfm'
                                obtain ⟨_, ya, hya, hfm'⟩ := tBind_step_inv hfm'
                                obtain ⟨_, yb, hyb, hfm'⟩ := tBind_step_inv hfm'
                                simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfm'
                                obtain ⟨_, rfl⟩ := hfm'
                                obtain ⟨_, ya', hca, hya⟩ := tBind_step_inv hya
                                simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hya
                                obtain ⟨_, rfl⟩ := hya
                                exact (coerceEAux_spec _ _ _ _ _ _ _ _ hca).1.trans (ihp0 ya' yb _ hyb)
                            exact auxF _ _ xa2 _ hfe0
                          exact (hleA.trans hleB).trans (ih0 xa2 xb _ hb)
                    exact aux ct sArm sEnd at_ htl
                  cases hce : cx.ctorEntry? k with
                  | none => simp [hce, hfL, throw, throwThe, MonadExceptOf.throw] at h1
                  | some ie =>
                    rcases ie with ⟨idx', entry'⟩
                    simp only [hce] at h1
                    obtain ⟨fvars, sFv, hfv, h1⟩ := tBind_step_inv h1
                    rw [hfFL] at hfv
                    simp only [Except.ok.injEq, Prod.mk.injEq] at hfv
                    obtain ⟨rfl, rfl⟩ := hfv
                    obtain ⟨fes, sFe, hfe, h1⟩ := tBind_step_inv h1
                    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1
                    obtain ⟨rfl, rfl⟩ := h1
                    set fvs := (List.range fl'.length).map fun i => localName (sA.nextLocal + i)
                    have hpatMap :
                        List.map (Aiur.Generic.Pattern.map Nat.cast)
                          (List.map qualifyPat (fvs.map Aiur.Generic.Pattern.bind)) =
                        fvs.map (Aiur.Generic.Pattern.bind : String → Aiur.Generic.Pattern F) := by
                      induction fvs with
                      | nil => rfl
                      | cons _ _ _ => simp [qualifyPat, Aiur.Generic.Pattern.map]
                    cases w0 with
                    | field _ | tuple _ | ptr _ _ =>
                      simp only [List.map_cons, SourceSemantics.selectArm, pC, qualifyPatF, qualifyPat,
                        qualifyTy, objTy, qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern,
                        matchPatternWith, bind, Except.bind, pure, Except.pure] at hs
                      exact ihc sFe sEnd at_ bs body (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) htl hdemB hs
                    | construct en cn ps =>
                      simp only [List.map_cons, SourceSemantics.selectArm, pC, qualifyPatF, qualifyPat,
                        qualifyTy, objTy, qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern,
                        matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol,
                        List.map_nil, List.isEmpty_nil, ↓reduceIte, hpatMap, List.length_map,
                        bind, Except.bind, pure, Except.pure] at hs
                      by_cases hcond : (en != objQName || cn != ctorNameOf idx' entry'.key || fvs.length != ps.length) = true
                      · simp only [hcond, ↓reduceIte] at hs
                        exact ihc sFe sEnd at_ bs body (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) htl hdemB hs
                      · have hcf0 : (en != objQName || cn != ctorNameOf idx' entry'.key || fvs.length != ps.length) = false :=
                          Bool.eq_false_iff.mpr hcond
                        rw [hcf0] at hs
                        simp only [Bool.false_eq_true, ↓reduceIte] at hs
                        simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hcf0
                        obtain ⟨⟨rfl, rfl⟩, hlenEq⟩ := hcf0
                        rw [matchListWith_attach_eq_t, matchListWith_binds fvs ps hlenEq.symm] at hs
                        obtain ⟨rfl, rfl⟩ := hs
                        obtain ⟨hget', hkey'⟩ := ctorEntry?_sound hce
                        have hndFvs : fvs.Nodup :=
                          List.Nodup.map (fun _ _ heq => by have := localName_inj heq; omega) List.nodup_range
                        exact ⟨k, fl', idx', entry', ps, fvs, fes, _, sFe,
                          hsub (k, fl') List.mem_cons_self, hget', hkey', rfl, by simpa [fvs] using hlenEq.symm,
                          hndFvs, by simp [fvs], rfl, rfl, hleTail.demand.trans hdemB, hfe⟩
              have hmap' : List.map
                  ((fun a => (Aiur.Generic.Pattern.map Nat.cast a.1, Aiur.Generic.Expr.map Nat.cast a.2)) ∘
                    fun a => (qualifyPat a.1, qualifyExpr a.2)) arms =
                  arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2) := rfl
              rw [List.map_map, hmap'] at hsel
              obtain ⟨k, fl, idx, entry, ps, fvars, fes, sF1, sF2, hmemD, hget, hkey, rfl, hpsLen,
                hfvNd, hfvLen, rfl, rfl, hdemF, hfe⟩ :=
                harmsInv D.ctors s1 s2 arms _ _ (fun _ hx => hx) hmap hdem hsel
              obtain ⟨c, fs, rfl, hckey, hflen, hvrs⟩ := VR_ctor_inv hnd hget hvr
              have hck : c.key = k := hckey.trans hkey
              -- Use `CoerceTargetOk` + `cert.WF` to recover `ValsOk cert dummyEnc fl fs`!
              obtain ⟨D', c', fl', fs', hD', hmemD', hvalsOk', hcEq⟩ := (hTarget _ hvQ).data_inv
              cases hcEq
              rw [hD, Option.some.injEq] at hD'; subst hD'
              have hflEq : fl' = fl := hwf d D hD c.key fl' fl hmemD' (hck ▸ hmemD)
              subst fl'
              -- Evaluate `fes` back to `TVRDataFields`
              have hfieldEv :
                  ∀ (fl' : List Shape) (fvars' : List String) (fs' : List Fir.Val) (ps' : List (SourceValue F))
                    (sA sB : TState) (fes' : List Lower.Expr)
                    (loc' : Environment F Nat) (hA hB : Heap F) (wsOut : List (SourceValue F)),
                    (∀ sh ∈ fl', sh ∈ fl) →
                    VRs P objQName bytesQName hA fs' ps' →
                    Fir.Shape.ValsOk cert dummyEnc fl' fs' →
                    EvalCapArgs loc' fvars' ps' →
                    ((fl'.zip fvars').mapM (m := TLowerM) fun ((sh, fv) : Shape × String) => do
                      let fr := cx.rep sh
                      let typed ← coerceEAux fuel' cx .obj fr (.load (vE fv))
                      pure (if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.store typed else typed)) sA =
                      .ok (fes', sB) →
                    DemandLe sB.demand lp.demand →
                    EvalArgsN world dDepth [] loc' (fes'.map (qualifyExprF F)) hA wsOut hB →
                    TVRDataFields P cert (scanFeatures P) hB d fl' fs' wsOut ∧ Heap.Extends hA hB := by
                intro fl'; induction fl' with
                | nil =>
                  intro fvars' fs' ps' sA sB fes' loc' hA hB wsOut _ hvrs' hvok hcap hfm _ hargs
                  cases hvok; cases hvrs'
                  cases fvars' with
                  | nil =>
                    simp only [List.zip_nil_left, List.mapM, List.mapM.loop, pure, StateT.pure,
                      Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfm
                    obtain ⟨rfl, rfl⟩ := hfm
                    cases hargs
                    exact ⟨.nil, Heap.Extends.refl _⟩
                  | cons _ _ => exact False.elim hcap
                | cons sh sht ihf =>
                  intro fvars' fs' ps' sA sB fes' loc' hA hB wsOut hsub hvrs' hvok hcap hfm hdemB hargs
                  cases hvok with | @cons _ v1 _ vsRest hv1 hvRest =>
                  cases hvrs' with | @cons _ _ addr1 wObj1 psRest hatA hvr1 hvrsRest =>
                  cases fvars' with
                  | nil => exact False.elim hcap
                  | cons fv fvt =>
                    obtain ⟨hlocFv, hcapRest⟩ := hcap
                    simp only [List.zip_cons_cons, List.mapM_cons] at hfm
                    obtain ⟨fe1, sMid, hfe1, hfm⟩ := tBind_step_inv hfm
                    obtain ⟨fet, sEnd, hfet, hfm⟩ := tBind_step_inv hfm
                    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfm
                    obtain ⟨rfl, rfl⟩ := hfm
                    obtain ⟨typed, sMid', hco1, hfe1⟩ := tBind_step_inv hfe1
                    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfe1
                    obtain ⟨rfl, rfl⟩ := hfe1
                    have hleRest : TStateLe sMid' sEnd := by
                      have aux : ∀ (prs : List (Shape × String)) (x0 x1 : TState) (es0 : List Lower.Expr),
                          (prs.mapM (m := TLowerM) fun ((s0, f0) : Shape × String) => do
                            let fr := cx.rep s0
                            let typed ← coerceEAux fuel' cx .obj fr (.load (vE f0))
                            pure (if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.store typed else typed)) x0 =
                            .ok (es0, x1) → TStateLe x0 x1 := by
                        intro prs; induction prs with
                        | nil =>
                          intro x0 x1 es0 hm'; simp only [List.mapM, List.mapM.loop, pure,
                            StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm'
                          obtain ⟨_, rfl⟩ := hm'; exact TStateLe.refl _
                        | cons p0 pt0 ihp0 =>
                          intro x0 x1 es0 hm'; rw [List.mapM_cons] at hm'
                          obtain ⟨_, xa, ha, hm'⟩ := tBind_step_inv hm'
                          obtain ⟨_, xb, hb, hm'⟩ := tBind_step_inv hm'
                          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm'
                          obtain ⟨_, rfl⟩ := hm'
                          obtain ⟨_, xa', hca, ha⟩ := tBind_step_inv ha
                          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ha
                          obtain ⟨_, rfl⟩ := ha
                          exact (coerceEAux_spec _ _ _ _ _ _ _ _ hca).1.trans (ihp0 xa' xb _ hb)
                      exact aux _ sMid' sEnd fet hfet
                    simp only [List.map_cons] at hargs
                    cases hargs with
                    | cons ev1 evRest =>
                      rename_i wOut1 hMid wsRest
                      have hcoreSh : isNatCoreRep (cx.rep sh) = true :=
                        datasNatCoreReps_field hdatas hD (hck ▸ hmemD) (hsub sh List.mem_cons_self)
                      have hloadCb : ∀ w1 hm1,
                          EvalExprN world dDepth [] loc' (qualifyExprF F (.load (vE fv))) hA w1 hm1 →
                          ∃ v', v' = v1 ∧ TVR P cert (scanFeatures P) hm1 .obj v' w1 ∧ Heap.Extends hA hm1 := by
                        intro w1 hm1 evLd
                        simp only [vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evLd
                        obtain ⟨vp, evV, hload⟩ := evalExprN_load_inv evLd
                        obtain ⟨hl', rfl⟩ := evalExprN_var_inv evV
                        rw [hlocFv, Option.some.injEq, Prod.mk.injEq] at hl'
                        obtain ⟨_, rfl⟩ := hl'
                        have htyEq : wObj1.type = .enum objQName := hvr1.type_eq
                        simp [loadValue, hatA, htyEq] at hload
                        subst hload
                        exact ⟨v1, rfl, .obj hvr1, Heap.Extends.refl _⟩
                      cases hp : dataFieldNeedsPtr P cert (scanFeatures P) d (repOf P cert (scanFeatures P) sh) with
                      | false =>
                        dsimp only [cx, TCx.rep] at ev1
                        simp only [hp, Bool.false_eq_true, ↓reduceIte] at ev1
                        obtain ⟨v1', hv1Eq, htvr1, ext1'⟩ :=
                          ih .obj (cx.rep sh) _ sA sMid' typed hco1 rfl hcoreSh
                            (hleRest.demand.trans hdemB) ev1 hloadCb
                            (fun v' hEq => hEq ▸ CoerceTargetOk.of_valOk hv1)
                        subst hv1Eq
                        obtain ⟨hdfRest, extRest⟩ :=
                          ihf fvt vsRest psRest sMid' sEnd fet loc' hMid hB wsRest
                            (fun s' hs' => hsub s' (List.mem_cons_of_mem _ hs'))
                            (hvrsRest.extend ext1') hvRest hcapRest hfet hdemB evRest
                        exact ⟨.consInline hp (htvr1.extend extRest) hdfRest, ext1'.trans extRest⟩
                      | true =>
                        dsimp only [cx, TCx.rep] at ev1
                        simp only [hp, ↓reduceIte, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev1
                        obtain ⟨wTyped, hPre, evTy, rfl, rfl⟩ := evalExprN_store_inv ev1
                        obtain ⟨v1', hv1Eq, htvr1, ext1'⟩ :=
                          ih .obj (cx.rep sh) _ sA sMid' typed hco1 rfl hcoreSh
                            (hleRest.demand.trans hdemB) evTy hloadCb
                            (fun v' hEq => hEq ▸ CoerceTargetOk.of_valOk hv1)
                        subst hv1Eq
                        have extSt : Heap.Extends hA (hPre ++ [wTyped]) :=
                          ext1'.trans (Heap.Extends.append_right hPre [wTyped])
                        obtain ⟨hdfRest, extRest⟩ :=
                          ihf fvt vsRest psRest sMid' sEnd fet loc' (hPre ++ [wTyped]) hB wsRest
                            (fun s' hs' => hsub s' (List.mem_cons_of_mem _ hs'))
                            (hvrsRest.extend extSt) hvRest hcapRest hfet hdemB evRest
                        have hatAddr : hB[hPre.length]? = some wTyped :=
                          extRest.getElem?_eq (by simp)
                        exact ⟨.consPtr hp hatAddr
                          (htvr1.extend ((Heap.Extends.append_right hPre [wTyped]).trans extRest)) hdfRest,
                          extSt.trans extRest⟩
              simp only [qualifyExprF, qualifyExpr, qualifyName_dataName, Option.map_some,
                Aiur.Generic.Expr.map, List.map_map] at evB
              obtain ⟨wsOut, hargsEv, rfl⟩ := evalExprN_construct_inv evB
              have hargsEv' : EvalArgsN world dDepth [] (fvars.zip ps ++ locals)
                  (fes.map (qualifyExprF F)) hm wsOut h' := hargsEv
              have hcapPs : EvalCapArgs (fvars.zip ps ++ locals) fvars ps :=
                EvalCapArgs.of_zip_nodup hfvNd (by omega)
              obtain ⟨hdf, ext2⟩ :=
                hfieldEv fl fvars fs ps sF1 sF2 fes (fvars.zip ps ++ locals) hm h' wsOut
                  (fun _ hx => hx) hvrs hvalsOk' hcapPs hfe hdemF hargsEv'
              have hflLen : fl.length = entry.arity := by
                have := hvrs.length_eq; omega
              refine ⟨.ctor c fs, hvQ, ?_, ext1.trans ext2⟩
              rw [hkey, ← hck]
              exact .dataVal hD (hck ▸ hmemD) hget (hkey.trans hck.symm) hflen hflLen hdf
          exact go hco (freshLocals_poly _ (fun _ => rfl) (fun _ _ => rfl))
            (fun _ _ => rfl) (fun _ _ => rfl)
        | irr | nat _ | w8 | w16 | w32 | w64 | «enum» _ | obj =>
          exact eval_coerceEAux_zero fc lw hnd .obj _ e st st' res
            (by unfold coerceEAux; simp only [heq, Bool.false_eq_true, ↓reduceIte]; exact hco)
            hcf hct hdem ev he hTarget
      | irr | nat _ | w8 | w16 | w32 | w64 | «enum» _ =>
        exact eval_coerceEAux_zero fc lw hnd _ toR e st st' res
          (by unfold coerceEAux; simp only [heq, Bool.false_eq_true, ↓reduceIte]; cases toR <;> exact hco)
          hcf hct hdem ev he hTarget

theorem eval_coerceE {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld P cert sched lp world)
    (hwf : cert.WF) (hkeys : (P.ctors.map (·.key)).Nodup) (hnd : (objCtorNames P).Nodup)
    (hdatas : datasNatCoreReps P cert (scanFeatures P) = true)
    {fromR toR : Rep} {e : Lower.Expr} {st st' : TState} {res : Lower.Expr}
    {dDepth : Nat} {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F}
    {Q : Fir.Val → Prop}
    (hco : coerceE { P, cert, feat := scanFeatures P, sched } fromR toR e st = .ok (res, st'))
    (hcf : isNatCoreRep fromR = true) (hct : isNatCoreRep toR = true)
    (hdem : DemandLe st'.demand lp.demand)
    (ev : EvalExprN world dDepth [] locals (qualifyExprF F res) h r h')
    (he : ∀ w0 hm, EvalExprN world dDepth [] locals (qualifyExprF F e) h w0 hm →
      ∃ v, Q v ∧ TVR P cert (scanFeatures P) hm fromR v w0 ∧ Heap.Extends h hm)
    (hTarget : ∀ v, Q v → CoerceTargetOk P cert (scanFeatures P) toR v) :
    ∃ v, Q v ∧ TVR P cert (scanFeatures P) h' toR v r ∧ Heap.Extends h h' :=
  eval_coerceEAux fc lw hwf hkeys hnd hdatas _ fromR toR e st st' res hco hcf hct hdem ev he hTarget

theorem eval_tArgRaw {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {world : World F} {dDepth : Nat} {fsh : FunShapes} {vm : TVarMap}
    {a : Arg} {st st' : TState} {e : Lower.Expr} {r : Rep}
    {ρ : Env} {locals : Environment F Nat} {h h' : Heap F} {w : SourceValue F}
    (ha : tArgRaw { P, cert, feat := scanFeatures P, sched } vm a st = .ok ((e, r), st'))
    (henv : TEnvRel P cert (scanFeatures P) h fsh vm ρ locals)
    (ev : EvalExprN world dDepth [] locals (qualifyExprF F e) h w h') :
    ∃ v, a.eval ρ = some v ∧ TVR P cert (scanFeatures P) h' r v w ∧ Heap.Extends h h' := by
  cases a with
  | var x =>
    unfold tArgRaw at ha
    cases hl : vm.lookup x with
    | none => simp only [hl] at ha; exact False.elim (tLift_throw_elim ha (fun _ _ => rfl))
    | some nr =>
      rcases nr with ⟨nx, rx⟩
      simp only [hl, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ha
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ha
      simp only [vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
      obtain ⟨hloc, rfl⟩ := evalExprN_var_inv ev
      obtain ⟨v, hρ, htvr⟩ := henv.rel x nx rx w hl hloc
      exact ⟨v, hρ, htvr, Heap.Extends.refl _⟩
  | lit l =>
    cases l with
    | nat n =>
      unfold tArgRaw at ha
      by_cases hn : n < natLimit
      · simp only [hn, ↓reduceIte, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ha
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ha
        simp only [litE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
        obtain ⟨rfl, rfl⟩ := evalExprN_literal_inv ev
        exact ⟨.lit (.nat n), rfl, .nat (Nat.lt_min.mpr ⟨Nat.lt_succ_self _, hn⟩), Heap.Extends.refl _⟩
      · simp only [hn, ↓reduceIte] at ha; exact False.elim (tLift_throw_elim ha (fun _ _ => rfl))
    | str s =>
      unfold tArgRaw at ha
      obtain ⟨s1, _, _, ha⟩ := tMark_step_inv ha (fun _ _ => rfl)
        (fun _ => by constructor <;> first | exact id | (intro _; rfl))
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ha
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ha
      simp only [strE, mk, qualifyExprF, qualifyExpr, qualifyName_obj, Option.map_some,
        Aiur.Generic.Expr.map, List.map] at ev
      obtain ⟨ws, hargs, rfl⟩ := evalExprN_construct_inv ev
      cases hargs with | cons evB htl =>
      cases htl
      obtain ⟨hb, ext⟩ := eval_bytesE evB
      exact ⟨.lit (.str s), rfl, .obj (.str hb), ext⟩
  | erased =>
    unfold tArgRaw at ha
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ha
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ha
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map] at ev
    obtain ⟨rfl, rfl⟩ := evalExprN_tuple0_inv ev
    exact ⟨.erased, rfl, .irr, Heap.Extends.refl _⟩

theorem eval_tArgE {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld P cert sched lp world)
    (hwf : cert.WF) (hkeys : (P.ctors.map (·.key)).Nodup) (hnd : (objCtorNames P).Nodup)
    (hdatas : datasNatCoreReps P cert (scanFeatures P) = true)
    {dDepth : Nat} {fsh : FunShapes} {vm : TVarMap} {a : Arg} {target : Rep}
    {st st' : TState} {e : Lower.Expr}
    {ρ : Env} {locals : Environment F Nat} {h h' : Heap F} {w : SourceValue F}
    (ha : tArgE { P, cert, feat := scanFeatures P, sched } vm a target st = .ok (e, st'))
    (hvmCore : ∀ p ∈ vm, isNatCoreRep p.2.2 = true)
    (htCore : isNatCoreRep target = true)
    (hdem : DemandLe st'.demand lp.demand)
    (henv : TEnvRel P cert (scanFeatures P) h fsh vm ρ locals)
    (ev : EvalExprN world dDepth [] locals (qualifyExprF F e) h w h')
    (hTarget : ∀ v, a.eval ρ = some v → CoerceTargetOk P cert (scanFeatures P) target v) :
    ∃ v, a.eval ρ = some v ∧ TVR P cert (scanFeatures P) h' target v w ∧ Heap.Extends h h' := by
  unfold tArgE at ha
  obtain ⟨⟨ea, ra⟩, s1, hraw, hco⟩ := tBind_step_inv ha
  have hraCore : isNatCoreRep ra = true := (tArgRaw_spec hraw).2.2 hvmCore
  exact eval_coerceE fc lw hwf hkeys hnd hdatas hco hraCore htCore hdem ev
    (fun w0 hm ev0 => eval_tArgRaw hraw henv ev0) hTarget

/-- Backward evaluation of a sequence of typed arguments `(as.zip paramReps).mapM tArgE`
checked against `ArgsOk fsh as σs`. -/
theorem eval_tArgEs {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld P cert sched lp world)
    (hwf : cert.WF) (hkeys : (P.ctors.map (·.key)).Nodup) (hnd : (objCtorNames P).Nodup)
    (hdatas : datasNatCoreReps P cert (scanFeatures P) = true)
    {dDepth : Nat} {fsh : FunShapes} {vm : TVarMap} {ρ : Env} {locals : Environment F Nat}
    (hvmCore : ∀ p ∈ vm, isNatCoreRep p.2.2 = true)
    (hEnvOk : Fir.Shape.EnvOk cert dummyEnc fsh ρ) :
    ∀ {as : List Arg} {σs : List Shape} {st st' : TState} {argEs : List Lower.Expr}
      {h h' : Heap F} {ws : List (SourceValue F)},
      Fir.Shape.ArgsOk fsh as σs →
      (∀ σ ∈ σs, isNatCoreRep (repOf P cert (scanFeatures P) σ) = true) →
      ((as.zip (σs.map fun σ => repOf P cert (scanFeatures P) σ)).mapM (m := TLowerM)
        fun (a, pr) => tArgE { P, cert, feat := scanFeatures P, sched } vm a pr) st = .ok (argEs, st') →
      DemandLe st'.demand lp.demand →
      TEnvRel P cert (scanFeatures P) h fsh vm ρ locals →
      EvalArgsN world dDepth [] locals (argEs.map (qualifyExprF F)) h ws h' →
      ∃ vs, evalArgs ρ as = some vs ∧
        Fir.Shape.ValsOk cert dummyEnc σs vs ∧
        TVRs P cert (scanFeatures P) h' (σs.map fun σ => repOf P cert (scanFeatures P) σ) vs ws ∧
        Heap.Extends h h' := by
  intro as
  induction as with
  | nil =>
    intro σs st st' argEs h h' ws hargs _ hmap _ _ ev
    cases hargs
    simp only [List.map_nil, List.zip_nil_left, List.mapM, List.mapM.loop, pure, StateT.pure,
      Except.pure, Except.ok.injEq, Prod.mk.injEq] at hmap
    obtain ⟨rfl, rfl⟩ := hmap
    cases ev
    exact ⟨[], rfl, .nil, .nil, Heap.Extends.refl _⟩
  | cons a at_ ih =>
    intro σs st st' argEs h h' ws hargs hcore hmap hdem henv ev
    cases hargs with
    | cons ha htl =>
      rename_i σ σt
      simp only [List.map_cons, List.zip_cons_cons, List.mapM_cons] at hmap
      obtain ⟨e1, s1, h1, hmap⟩ := tBind_step_inv hmap
      obtain ⟨et, s2, h2, hmap⟩ := tBind_step_inv hmap
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hmap
      obtain ⟨rfl, rfl⟩ := hmap
      have hle2 : TStateLe s1 s2 := by
        have aux : ∀ (l0 : List (Arg × Rep)) (x0 x1 : TState) (es0 : List Lower.Expr),
            (l0.mapM (m := TLowerM) fun (a0, pr0) =>
              tArgE { P, cert, feat := scanFeatures P, sched } vm a0 pr0) x0 = .ok (es0, x1) →
            TStateLe x0 x1 := by
          intro l0; induction l0 with
          | nil =>
            intro x0 x1 es0 hm'; simp only [List.mapM, List.mapM.loop, pure, StateT.pure,
              Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm'
            obtain ⟨_, rfl⟩ := hm'; exact TStateLe.refl _
          | cons hd0 tl0 ih0 =>
            intro x0 x1 es0 hm'; rw [List.mapM_cons] at hm'
            obtain ⟨_, xa, hxa, hm'⟩ := tBind_step_inv hm'
            obtain ⟨_, xb, hxb, hm'⟩ := tBind_step_inv hm'
            simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm'
            obtain ⟨_, rfl⟩ := hm'
            exact (tArgE_spec hxa).1.trans (ih0 xa xb _ hxb)
        exact aux _ s1 s2 et h2
      simp only [List.map_cons] at ev
      cases ev with
      | cons ev1 evRest =>
        rename_i w1 hm1 wt
        obtain ⟨v1, hv1, htvr1, ext1⟩ :=
          eval_tArgE fc lw hwf hkeys hnd hdatas h1 hvmCore (hcore σ List.mem_cons_self)
            (hle2.demand.trans hdem) henv ev1
            (fun v hv => CoerceTargetOk.of_valOk (Fir.Proof.Shape.argSound hEnvOk ha hv))
        have hvok1 := Fir.Proof.Shape.argSound hEnvOk ha hv1
        obtain ⟨vst, hvst, hvokRest, htvrsRest, ext2⟩ :=
          ih htl (fun σ' hσ' => hcore σ' (List.mem_cons_of_mem _ hσ')) h2 hdem (henv.extend ext1) evRest
        refine ⟨v1 :: vst, ?_, .cons hvok1 hvokRest, .cons (htvr1.extend ext2) htvrsRest, ext1.trans ext2⟩
        rw [Fir.evalArgs_cons, hv1, hvst]; rfl

/-- Backward simulation of `TypedLower.wrapBool` for `.enum ind` and `.obj` targets. -/
theorem eval_wrapBool {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {world : World F} (hkeys : (P.ctors.map (·.key)).Nodup)
    {dDepth : Nat} {locals : Environment F Nat} {condExpr res : Lower.Expr}
    {target : Rep} {st st' : TState} {h h' : Heap F} {r : SourceValue F} {b : Bool}
    {fL : {α : Type} → Except String α → TLowerM α}
    {fM : (Demand → Demand) → TLowerM Unit}
    (hw : (let cx : TCx := { P, cert, feat := scanFeatures P, sched }
           match target with
           | .enum ind =>
             match cx.boolEnum? with
             | some (bind, tt, ff) =>
               if bind == ind then
                 pure (matchE condExpr
                   [(.literal 0, .construct (enumName ind) (some []) ff []),
                    (.wildcard, .construct (enumName ind) (some []) tt [])])
               else fL (throw "wrapBool: enum mismatch")
             | none => fL (throw "wrapBool: Bool enum missing")
           | .obj => do
             fM fun d => { d with needObj := true }
             let some (tt, ff) := (Lower.Cx.mk cx.P).boolNames
               | fL (throw "wrapBool: Bool pins missing")
             pure (matchE condExpr [(.literal 0, mk ff []), (.wildcard, mk tt [])])
           | _ => fL (throw s!"wrapBool: unexpected target rep {reprStr target}")) st = .ok (res, st'))
    (hfL : ∀ {α} (x : Except String α) s, fL x s = match x with | .ok a => .ok (a, s) | .error err => .error err)
    (hfM : ∀ u s, fM u s = .ok ((), { s with demand := u s.demand }))
    (ev : EvalExprN world dDepth [] locals (qualifyExprF F res) h r h')
    (hcond : ∀ v hm, EvalExprN world dDepth [] locals (qualifyExprF F condExpr) h v hm →
      v = .field (if b then (1 : F) else 0) ∧ Heap.Extends h hm)
    (hTarget : ∀ v, Fir.boolVal P b = some v → CoerceTargetOk P cert (scanFeatures P) target v) :
    ∃ v, Fir.boolVal P b = some v ∧ TVR P cert (scanFeatures P) h' target v r ∧ Heap.Extends h h' := by
  set cx : TCx := { P, cert, feat := scanFeatures P, sched }
  cases target with
  | «enum» ind =>
    cases hbe : cx.boolEnum? with
    | none => simp [hbe, hfL, throw, throwThe, MonadExceptOf.throw] at hw
    | some p =>
      rcases p with ⟨bind_, ttNm, ffNm⟩
      simp only [hbe] at hw
      by_cases hbi : (bind_ == ind) = true
      · simp only [hbi, ↓reduceIte, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        have hbiEq : bind_ = ind := beq_iff_eq.mp hbi
        subst hbiEq
        obtain ⟨tt, ff, it, et, if_, ef, htt, hff, hct, hcf, hetAr, hefAr, rfl, rfl⟩ :=
          boolEnum?_sound hbe
        dsimp only [cx] at htt hff
        obtain ⟨vc, hm, evC, hbr⟩ := evalExprN_match_lit_wild_inv ev
        obtain ⟨rfl, ext1⟩ := hcond vc hm evC
        cases b with
        | false =>
          rcases hbr with ⟨_, evF⟩ | ⟨hne, _⟩
          · simp only [qualifyExprF, qualifyExpr, qualifyName_enumName, Option.map_some,
              Aiur.Generic.Expr.map, List.map_nil] at evF
            obtain ⟨ws, hargs, rfl⟩ := evalExprN_construct_inv evF
            cases hargs
            obtain ⟨cf, hcfInfo, hcfKey, _⟩ := ctorInfo?_of_ctorEntry? hkeys hcf
            have hbv : Fir.boolVal P false = some (.ctor cf []) := by
              simp [Fir.boolVal, hff, hcfInfo]
            obtain ⟨ks, c', hE, hmem, hcEq⟩ := (hTarget _ hbv).enum_inv
            cases hcEq
            obtain ⟨hgetF, hkeyF⟩ := ctorEntry?_sound hcf
            refine ⟨.ctor cf [], hbv, ?_, ext1⟩
            rw [hkeyF, ← hcfKey]
            exact .enumVal hE hmem hgetF (hkeyF.trans hcfKey.symm) hefAr
          · exact False.elim (hne (by simp))
        | true =>
          rcases hbr with ⟨heq, _⟩ | ⟨_, evT⟩
          · exact False.elim ((one_ne_zero (α := F)) (by simpa using Value.field.inj heq))
          · simp only [qualifyExprF, qualifyExpr, qualifyName_enumName, Option.map_some,
              Aiur.Generic.Expr.map, List.map_nil] at evT
            obtain ⟨ws, hargs, rfl⟩ := evalExprN_construct_inv evT
            cases hargs
            obtain ⟨ct, hctInfo, hctKey, _⟩ := ctorInfo?_of_ctorEntry? hkeys hct
            have hbv : Fir.boolVal P true = some (.ctor ct []) := by
              simp [Fir.boolVal, htt, hctInfo]
            obtain ⟨ks, c', hE, hmem, hcEq⟩ := (hTarget _ hbv).enum_inv
            cases hcEq
            obtain ⟨hgetT, hkeyT⟩ := ctorEntry?_sound hct
            refine ⟨.ctor ct [], hbv, ?_, ext1⟩
            rw [hkeyT, ← hctKey]
            exact .enumVal hE hmem hgetT (hkeyT.trans hctKey.symm) hetAr
      · simp [hbi, hfL, throw, throwThe, MonadExceptOf.throw] at hw
  | obj =>
    obtain ⟨s1, _, _, hw⟩ := tMark_step_inv hw hfM
      (fun _ => by constructor <;> first | exact id | (intro _; rfl))
    cases hbn : (Lower.Cx.mk cx.P).boolNames with
    | none => simp [hbn, hfL, throw, throwThe, MonadExceptOf.throw] at hw
    | some p =>
      rcases p with ⟨ttNm, ffNm⟩
      simp only [hbn, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      obtain ⟨tt, ff, it, et, if_, ef, htt, hff, hct, hcf, hetAr, hefAr, rfl, rfl⟩ :=
        boolNames_sound hbn
      dsimp only [cx] at htt hff
      obtain ⟨vc, hm, evC, hbr⟩ := evalExprN_match_lit_wild_inv ev
      obtain ⟨rfl, ext1⟩ := hcond vc hm evC
      cases b with
      | false =>
        rcases hbr with ⟨_, evF⟩ | ⟨hne, _⟩
        · simp only [mk, qualifyExprF, qualifyExpr, qualifyName_obj, Option.map_some,
            Aiur.Generic.Expr.map, List.map_nil] at evF
          obtain ⟨ws, hargs, rfl⟩ := evalExprN_construct_inv evF
          cases hargs
          obtain ⟨cf, hcfInfo, hcfKey, _⟩ := ctorInfo?_of_ctorEntry? hkeys hcf
          have hbv : Fir.boolVal P false = some (.ctor cf []) := by
            simp [Fir.boolVal, hff, hcfInfo]
          obtain ⟨hgetF, hkeyF⟩ := ctorEntry?_sound hcf
          refine ⟨.ctor cf [], hbv, ?_, ext1⟩
          rw [hkeyF, ← hcfKey]
          exact .obj (.ctor hgetF (hkeyF.trans hcfKey.symm) (by simp [hefAr]) .nil)
        · exact False.elim (hne (by simp))
      | true =>
        rcases hbr with ⟨heq, _⟩ | ⟨_, evT⟩
        · exact False.elim ((one_ne_zero (α := F)) (by simpa using Value.field.inj heq))
        · simp only [mk, qualifyExprF, qualifyExpr, qualifyName_obj, Option.map_some,
            Aiur.Generic.Expr.map, List.map_nil] at evT
          obtain ⟨ws, hargs, rfl⟩ := evalExprN_construct_inv evT
          cases hargs
          obtain ⟨ct, hctInfo, hctKey, _⟩ := ctorInfo?_of_ctorEntry? hkeys hct
          have hbv : Fir.boolVal P true = some (.ctor ct []) := by
            simp [Fir.boolVal, htt, hctInfo]
          obtain ⟨hgetT, hkeyT⟩ := ctorEntry?_sound hct
          refine ⟨.ctor ct [], hbv, ?_, ext1⟩
          rw [hkeyT, ← hctKey]
          exact .obj (.ctor hgetT (hkeyT.trans hctKey.symm) (by simp [hetAr]) .nil)
  | irr | nat _ | w8 | w16 | w32 | w64 | data _ =>
    simp [hfL, throw, throwThe, MonadExceptOf.throw] at hw

/-! ### Backward Simulation of `tPrimE`, `stepDownNat`, `tRhsE`, and `tCaseE` -/

omit [DecidableEq F] in
private theorem TVR_nat_fieldBound {P : Program} {cert : ShapeCert} {feat : Features}
    {h : Heap F} {r : Rep} {n : Nat} {w : SourceValue F}
    (hcore : isNatCoreRep r = true)
    (htvr : TVR P cert feat h r (.lit (.nat n)) w) : n < r.fieldBound := by
  cases htvr with
  | nat hlt => exact hlt
  | w8 hlt => exact hlt
  | w16 hlt => exact hlt
  | obj hvr =>
    cases hvr with | nat hlt => exact hlt
  | w32 _ | w64 _ => simp [isNatCoreRep] at hcore

private theorem eval_tArgRaw_to_nat {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld P cert sched lp world)
    (hwf : cert.WF) (hkeys : (P.ctors.map (·.key)).Nodup) (hnd : (objCtorNames P).Nodup)
    (hdatas : datasNatCoreReps P cert (scanFeatures P) = true)
    {dDepth : Nat} {fsh : FunShapes} {vm : TVarMap} {a : Arg}
    {st1 s1 st2 s2 : TState} {ea xa : Lower.Expr} {ra : Rep}
    {ρ : Env} {locals : Environment F Nat} {h h' : Heap F} {w : SourceValue F}
    (hraw : tArgRaw { P, cert, feat := scanFeatures P, sched } vm a st1 = .ok ((ea, ra), s1))
    (hco : coerceE { P, cert, feat := scanFeatures P, sched } ra (.nat natLimit) ea st2 = .ok (xa, s2))
    (hvmCore : ∀ p ∈ vm, isNatCoreRep p.2.2 = true)
    (hdem : DemandLe s2.demand lp.demand)
    (henv : TEnvRel P cert (scanFeatures P) h fsh vm ρ locals)
    (ev : EvalExprN world dDepth [] locals (qualifyExprF F xa) h w h') :
    ∃ n, a.eval ρ = some (.lit (.nat n)) ∧ n < ra.fieldBound ∧ n < natLimit ∧
      w = .field (n : F) ∧ Heap.Extends h h' := by
  have hraCore : isNatCoreRep ra = true := (tArgRaw_spec hraw).2.2 hvmCore
  obtain ⟨v, ⟨haEv, hfb⟩, htvr, ext⟩ :=
    eval_coerceE fc lw hwf hkeys hnd hdatas hco hraCore rfl hdem ev
      (Q := fun v => a.eval ρ = some v ∧ ∀ n, v = .lit (.nat n) → n < ra.fieldBound)
      (fun w0 hm ev0 => by
        obtain ⟨v0, hv0, htvr0, ext0⟩ := eval_tArgRaw hraw henv ev0
        exact ⟨v0, ⟨hv0, fun n hn => TVR_nat_fieldBound hraCore (hn ▸ htvr0)⟩, htvr0, ext0⟩)
      (fun _ _ => Or.inr (Or.inl rfl))
  obtain ⟨n, _, hn, rfl, rfl⟩ := TVR_nat_inv htvr
  exact ⟨n, haEv, hfb n rfl, hn, rfl, ext⟩

private theorem eval_tArgE_to_nat {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld P cert sched lp world)
    (hwf : cert.WF) (hkeys : (P.ctors.map (·.key)).Nodup) (hnd : (objCtorNames P).Nodup)
    (hdatas : datasNatCoreReps P cert (scanFeatures P) = true)
    {dDepth : Nat} {fsh : FunShapes} {vm : TVarMap} {a : Arg}
    {st st' : TState} {xa : Lower.Expr}
    {ρ : Env} {locals : Environment F Nat} {h h' : Heap F} {w : SourceValue F}
    (ha : tArgE { P, cert, feat := scanFeatures P, sched } vm a (.nat natLimit) st = .ok (xa, st'))
    (hvmCore : ∀ p ∈ vm, isNatCoreRep p.2.2 = true)
    (hdem : DemandLe st'.demand lp.demand)
    (henv : TEnvRel P cert (scanFeatures P) h fsh vm ρ locals)
    (ev : EvalExprN world dDepth [] locals (qualifyExprF F xa) h w h') :
    ∃ n, a.eval ρ = some (.lit (.nat n)) ∧ n < natLimit ∧ w = .field (n : F) ∧ Heap.Extends h h' := by
  obtain ⟨v, haEv, htvr, ext⟩ :=
    eval_tArgE fc lw hwf hkeys hnd hdatas ha hvmCore rfl hdem henv ev
      (fun _ _ => Or.inr (Or.inl rfl))
  obtain ⟨n, _, hn, rfl, rfl⟩ := TVR_nat_inv htvr
  exact ⟨n, haEv, hn, rfl, ext⟩

private theorem eval_tPrimE_divmod {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld P cert sched lp world)
    (hwf : cert.WF) (hkeys : (P.ctors.map (·.key)).Nodup) (hnd : (objCtorNames P).Nodup)
    (hdatas : datasNatCoreReps P cert (scanFeatures P) = true)
    {dDepth : Nat} {fsh : FunShapes} {vm : TVarMap} {a b : Arg} {target : Rep}
    {st st' : TState} {res : Lower.Expr} {isMod : Bool}
    {ρ : Env} {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F}
    (hvmCore : ∀ p ∈ vm, isNatCoreRep p.2.2 = true)
    (hlocVm : AllLocalLt st.nextLocal (vm.map fun p => p.2.1))
    (htCore : isNatCoreRep target = true)
    (hdem : DemandLe st'.demand lp.demand)
    (henv : TEnvRel P cert (scanFeatures P) h fsh vm ρ locals)
    {fM : (Demand → Demand) → TLowerM Unit} {fF : TLowerM String}
    (h0 : (let cx : TCx := { P, cert, feat := scanFeatures P, sched }
           do let xa ← tArgE cx vm a (.nat natLimit)
              let xb ← tArgE cx vm b (.nat natLimit)
              fM fun d => { d with needDivMod56 := true, needMul56 := true, needCheckU56 := true,
                                   needCheckU24 := true, needSubBorrow56 := true }
              let tx ← fF
              let ty ← fF
              let body := letE tx xa <| letE ty xb <|
                matchE (vE ty)
                  [(.literal 0, if isMod then vE tx else litE 0),
                   (.wildcard, .project (callE "divmod_56" [vE tx, vE ty]) (if isMod then 1 else 0))]
              coerceE cx (.nat natLimit) target body) st = .ok (res, st'))
    (hfM : ∀ u s, fM u s = .ok ((), { s with demand := u s.demand }))
    (hfF : ∀ s, fF s = .ok (localName s.nextLocal, { s with nextLocal := s.nextLocal + 1 }))
    (ev : EvalExprN world dDepth [] locals (qualifyExprF F res) h r h')
    (hTarget : ∀ v, evalRhs P ρ (.prim (if isMod then .natMod else .natDiv) [a, b]) = .ok v →
      CoerceTargetOk P cert (scanFeatures P) target v) :
    ∃ v, evalRhs P ρ (.prim (if isMod then .natMod else .natDiv) [a, b]) = .ok v ∧
      TVR P cert (scanFeatures P) h' target v r ∧ Heap.Extends h h' := by
  obtain ⟨xa, s1, h1, h0⟩ := tBind_step_inv h0
  obtain ⟨xb, s2, h2, h0⟩ := tBind_step_inv h0
  obtain ⟨s3, hle3, hdem3, h0⟩ := tMark_step_inv h0 hfM
    (fun _ => by constructor <;> first | exact id | (intro _; rfl))
  obtain ⟨tx, s4, htx, h0⟩ := tBind_step_inv h0
  rw [hfF] at htx; simp only [Except.ok.injEq, Prod.mk.injEq] at htx
  obtain ⟨rfl, rfl⟩ := htx
  obtain ⟨ty, s5, hty, hco⟩ := tBind_step_inv h0
  rw [hfF] at hty; simp only [Except.ok.injEq, Prod.mk.injEq] at hty
  obtain ⟨rfl, rfl⟩ := hty
  have hle1 := (tArgE_spec h1).1
  have hle2 := (tArgE_spec h2).1
  have hleCo := (coerceE_spec hco).1
  have hle45 : TStateLe s3 { s3 with nextLocal := s3.nextLocal + 1 + 1 } :=
    ⟨by dsimp only; omega, Nat.le_refl _, rfl, DemandLe.refl _⟩
  have hdemS3 : DemandLe s3.demand lp.demand := (hle45.trans hleCo).demand.trans hdem
  have hdemS2 : DemandLe s2.demand lp.demand := hle3.demand.trans hdemS3
  have hdemS1 : DemandLe s1.demand lp.demand := hle2.demand.trans hdemS2
  have hfreshTx : localName s3.nextLocal ∉ vm.map (fun p => p.2.1) :=
    hlocVm.not_mem ((hle1.trans hle2).trans hle3).nextLocal
  have htxNeTy : localName (s3.nextLocal + 1) ≠ localName s3.nextLocal := fun heq => by
    have := localName_inj heq; omega
  have htxNeTyB : (localName (s3.nextLocal + 1) == localName s3.nextLocal) = false :=
    beq_false_of_ne htxNeTy
  refine eval_coerceE fc lw hwf hkeys hnd hdatas hco rfl htCore hdem ev
    (Q := fun v => evalRhs P ρ (.prim (if isMod then .natMod else .natDiv) [a, b]) = .ok v)
    (fun w0 hm evBody => ?_) hTarget
  simp only [letE, qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
    Aiur.Generic.Pattern.map] at evBody
  obtain ⟨wx, hm1, evXa, evK1⟩ := evalExprN_let_bind_inv evBody
  obtain ⟨n1, haEv, hn1, rfl, ext1⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h1 hvmCore hdemS1 henv evXa
  obtain ⟨wy, hm2, evXb, evK2⟩ := evalExprN_let_bind_inv evK1
  have henv1 := (henv.extend ext1).cons_unused (nm := localName s3.nextLocal) (w := .field (n1 : F)) hfreshTx
  obtain ⟨n2, hbEv, hn2, rfl, ext2⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h2 hvmCore hdemS2 henv1 evXb
  obtain ⟨vy, hm3, evY, hbr⟩ := evalExprN_match_lit_wild_inv evK2
  simp only [vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evY
  obtain ⟨hly, rfl⟩ := evalExprN_var_inv evY
  simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hly
  obtain ⟨_, rfl⟩ := hly
  have hneedDm : lp.demand.needDivMod56 = true := hdemS3.needDivMod56 (by rw [hdem3])
  have hneedMul : lp.demand.needMul56 = true := hdemS3.needMul56 (by rw [hdem3])
  have hneedU56 : lp.demand.needCheckU56 = true := hdemS3.needCheckU56 (by rw [hdem3])
  have hneedU24 : lp.demand.needCheckU24 = true := hdemS3.needCheckU24 (by rw [hdem3])
  have hneedSub : lp.demand.needSubBorrow56 = true := hdemS3.needSubBorrow56 (by rw [hdem3])
  have hneNone : lp.tier ≠ .none := tier_ne_none_of_usesRangeCheck lw.lowered (by simp [hneedDm])
  rcases hbr with ⟨hn2zF, evZero⟩ | ⟨hn2nzF, evNz⟩
  · have hn2z : n2 = 0 := fc.natCast_inj56 hn2 (by unfold natLimit; omega) (by simpa using Value.field.inj hn2zF)
    subst hn2z
    cases isMod with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, litE, qualifyExprF, qualifyExpr,
        Aiur.Generic.Expr.map] at evZero
      obtain ⟨rfl, rfl⟩ := evalExprN_literal_inv evZero
      refine ⟨.lit (.nat 0), ?_, .nat (by unfold natLimit; omega), ext1.trans ext2⟩
      simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs]
    | true =>
      simp only [↓reduceIte, vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evZero
      obtain ⟨hlx, rfl⟩ := evalExprN_var_inv evZero
      simp only [List.find?_cons, htxNeTyB, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hlx
      obtain ⟨_, rfl⟩ := hlx
      refine ⟨.lit (.nat n1), ?_, .nat (Nat.lt_min.mpr ⟨hn1, hn1⟩), ext1.trans ext2⟩
      simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs]
  · simp only [callE, vE, qualifyExprF, qualifyExpr, qualifyName_divmod_56, Option.map_some,
      Aiur.Generic.Expr.map, List.map] at evNz
    obtain ⟨vt, evCall, hproj⟩ := evalExprN_project_inv evNz
    obtain ⟨_, vx', vy', _, _, _, evVx, evVy, hcal⟩ := evalExprN_call2_inv evCall
    obtain ⟨hlx, rfl⟩ := evalExprN_var_inv evVx
    simp only [List.find?_cons, htxNeTyB, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hlx
    obtain ⟨_, rfl⟩ := hlx
    obtain ⟨hly', rfl⟩ := evalExprN_var_inv evVy
    simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hly'
    obtain ⟨_, rfl⟩ := hly'
    obtain ⟨rfl, hn2Pos, hvtEq⟩ :=
      eval_divmod_56 fc (lw.byteCheck hneNone) (lw.hasSplit32_24 hneedMul)
        (lw.hasCheckU24 (Or.inl hneedU24)) (lw.hasCheckU56 (Or.inl hneedU56))
        (lw.hasSubBorrow56 hneedSub) (lw.hasMul56 hneedMul) (lw.hasDivMod56 hneedDm)
        hn1 hn2 hcal.toEvalFn
    have hvt := Value.tuple.inj hvtEq; subst hvt
    have hdivLt : n1 / n2 < natLimit := lt_of_le_of_lt (Nat.div_le_self n1 n2) hn1
    have hmodLt : n1 % n2 < natLimit := lt_of_le_of_lt (Nat.mod_le n1 n2) hn1
    cases isMod with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.getElem?_cons_zero,
        Option.some.injEq] at hproj
      subst hproj
      refine ⟨.lit (.nat (n1 / n2)), ?_, .nat (Nat.lt_min.mpr ⟨hdivLt, hdivLt⟩), ext1.trans ext2⟩
      simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs, Nat.ne_of_gt hn2Pos]
    | true =>
      simp only [↓reduceIte, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hproj
      subst hproj
      refine ⟨.lit (.nat (n1 % n2)), ?_, .nat (Nat.lt_min.mpr ⟨hmodLt, hmodLt⟩), ext1.trans ext2⟩
      simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs, Nat.ne_of_gt hn2Pos]

private theorem eval_tPrimE_bitwise {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld P cert sched lp world)
    (hwf : cert.WF) (hkeys : (P.ctors.map (·.key)).Nodup) (hnd : (objCtorNames P).Nodup)
    (hdatas : datasNatCoreReps P cert (scanFeatures P) = true)
    {dDepth : Nat} {fsh : FunShapes} {vm : TVarMap} {op : Prim} {a b : Arg} {target : Rep}
    {st st' : TState} {res : Lower.Expr}
    {ρ : Env} {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F}
    (hop : op = .natLand ∨ op = .natLor ∨ op = .natXor)
    (hvmCore : ∀ p ∈ vm, isNatCoreRep p.2.2 = true)
    (htCore : isNatCoreRep target = true)
    (hdem : DemandLe st'.demand lp.demand)
    (henv : TEnvRel P cert (scanFeatures P) h fsh vm ρ locals)
    {fM : (Demand → Demand) → TLowerM Unit}
    (h0 : (let cx : TCx := { P, cert, feat := scanFeatures P, sched }
           do let xa ← tArgE cx vm a (.nat natLimit)
              let xb ← tArgE cx vm b (.nat natLimit)
              fM fun d => { d with needU64Bitwise := true }
              let u64Op := match op with
                | .natLand => "UInt64::and" | .natLor => "UInt64::or" | _ => "UInt64::xor"
              let body := callE "UInt64::to_field" [callE u64Op [wordE xa, wordE xb]]
              coerceE cx (.nat natLimit) target body) st = .ok (res, st'))
    (hfM : ∀ u s, fM u s = .ok ((), { s with demand := u s.demand }))
    (ev : EvalExprN world dDepth [] locals (qualifyExprF F res) h r h')
    (hTarget : ∀ v, evalRhs P ρ (.prim op [a, b]) = .ok v →
      CoerceTargetOk P cert (scanFeatures P) target v) :
    ∃ v, evalRhs P ρ (.prim op [a, b]) = .ok v ∧
      TVR P cert (scanFeatures P) h' target v r ∧ Heap.Extends h h' := by
  obtain ⟨xa, s1, h1, h0⟩ := tBind_step_inv h0
  obtain ⟨xb, s2, h2, h0⟩ := tBind_step_inv h0
  obtain ⟨s3, hle3, hdem3, hco⟩ := tMark_step_inv h0 hfM
    (fun _ => by constructor <;> first | exact id | (intro _; rfl))
  have hle2 := (tArgE_spec h2).1
  have hleCo := (coerceE_spec hco).1
  have hdemS3 : DemandLe s3.demand lp.demand := hleCo.demand.trans hdem
  have hdemS2 : DemandLe s2.demand lp.demand := hle3.demand.trans hdemS3
  have hdemS1 : DemandLe s1.demand lp.demand := hle2.demand.trans hdemS2
  have hneedU64 : lp.demand.needU64Bitwise = true := hdemS3.needU64Bitwise (by rw [hdem3])
  have hu64 : U64Contracts world := lw.u64 (tier_eq_u64_of_needU64Bitwise lw.lowered hneedU64)
  refine eval_coerceE fc lw hwf hkeys hnd hdatas hco rfl htCore hdem ev
    (Q := fun v => evalRhs P ρ (.prim op [a, b]) = .ok v)
    (fun w0 hm evBody => ?_) hTarget
  simp only [callE, wordE, qualifyExprF, qualifyExpr, qualifyName_u64_to_field,
    qualifyName_u64_from_field, Option.map_some, Aiur.Generic.Expr.map, List.map] at evBody
  obtain ⟨_, wRes, hPre, _, evOp, hToF⟩ := evalExprN_call1_inv evBody
  rcases hop with rfl | rfl | rfl
  · simp only [qualifyName_u64_and] at evOp
    obtain ⟨_, wa, wb, hm1, hm2, _, evWa, evWb, hAnd⟩ := evalExprN_call2_inv evOp
    obtain ⟨_, v1, hm1', _, ev1, hFrom1⟩ := evalExprN_call1_inv evWa
    obtain ⟨n1, haEv, hn1, rfl, ext1⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h1 hvmCore hdemS1 henv ev1
    obtain ⟨n1', hn1', hEq1, hu1, rfl⟩ := hu64.from_field _ _ _ _ hFrom1.toEvalFn
    have h1eq : n1 = n1' := fc.natCast_inj56 hn1 hn1' (Value.field.inj hEq1)
    subst h1eq
    obtain ⟨_, v2, hm2', _, ev2, hFrom2⟩ := evalExprN_call1_inv evWb
    obtain ⟨n2, hbEv, hn2, rfl, ext2⟩ :=
      eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h2 hvmCore hdemS2 (henv.extend ext1) ev2
    obtain ⟨n2', hn2', hEq2, hu2, rfl⟩ := hu64.from_field _ _ _ _ hFrom2.toEvalFn
    have h2eq : n2 = n2' := fc.natCast_inj56 hn2 hn2' (Value.field.inj hEq2)
    subst h2eq
    obtain ⟨huRes, rfl⟩ := hu64.and n1 n2 wa wb _ _ _ hu1 hu2 hAnd.toEvalFn
    obtain ⟨hltRes, rfl, rfl⟩ := hu64.to_field (n1 &&& n2) wRes _ _ _ huRes hToF.toEvalFn
    exact ⟨.lit (.nat (n1 &&& n2)), by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs],
      .nat (Nat.lt_min.mpr ⟨hltRes, hltRes⟩), ext1.trans ext2⟩
  · simp only [qualifyName_u64_or] at evOp
    obtain ⟨_, wa, wb, hm1, hm2, _, evWa, evWb, hOr⟩ := evalExprN_call2_inv evOp
    obtain ⟨_, v1, hm1', _, ev1, hFrom1⟩ := evalExprN_call1_inv evWa
    obtain ⟨n1, haEv, hn1, rfl, ext1⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h1 hvmCore hdemS1 henv ev1
    obtain ⟨n1', hn1', hEq1, hu1, rfl⟩ := hu64.from_field _ _ _ _ hFrom1.toEvalFn
    have h1eq : n1 = n1' := fc.natCast_inj56 hn1 hn1' (Value.field.inj hEq1)
    subst h1eq
    obtain ⟨_, v2, hm2', _, ev2, hFrom2⟩ := evalExprN_call1_inv evWb
    obtain ⟨n2, hbEv, hn2, rfl, ext2⟩ :=
      eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h2 hvmCore hdemS2 (henv.extend ext1) ev2
    obtain ⟨n2', hn2', hEq2, hu2, rfl⟩ := hu64.from_field _ _ _ _ hFrom2.toEvalFn
    have h2eq : n2 = n2' := fc.natCast_inj56 hn2 hn2' (Value.field.inj hEq2)
    subst h2eq
    obtain ⟨huRes, rfl⟩ := hu64.or n1 n2 wa wb _ _ _ hu1 hu2 hOr.toEvalFn
    obtain ⟨hltRes, rfl, rfl⟩ := hu64.to_field (n1 ||| n2) wRes _ _ _ huRes hToF.toEvalFn
    exact ⟨.lit (.nat (n1 ||| n2)), by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs],
      .nat (Nat.lt_min.mpr ⟨hltRes, hltRes⟩), ext1.trans ext2⟩
  · simp only [qualifyName_u64_xor] at evOp
    obtain ⟨_, wa, wb, hm1, hm2, _, evWa, evWb, hXor⟩ := evalExprN_call2_inv evOp
    obtain ⟨_, v1, hm1', _, ev1, hFrom1⟩ := evalExprN_call1_inv evWa
    obtain ⟨n1, haEv, hn1, rfl, ext1⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h1 hvmCore hdemS1 henv ev1
    obtain ⟨n1', hn1', hEq1, hu1, rfl⟩ := hu64.from_field _ _ _ _ hFrom1.toEvalFn
    have h1eq : n1 = n1' := fc.natCast_inj56 hn1 hn1' (Value.field.inj hEq1)
    subst h1eq
    obtain ⟨_, v2, hm2', _, ev2, hFrom2⟩ := evalExprN_call1_inv evWb
    obtain ⟨n2, hbEv, hn2, rfl, ext2⟩ :=
      eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h2 hvmCore hdemS2 (henv.extend ext1) ev2
    obtain ⟨n2', hn2', hEq2, hu2, rfl⟩ := hu64.from_field _ _ _ _ hFrom2.toEvalFn
    have h2eq : n2 = n2' := fc.natCast_inj56 hn2 hn2' (Value.field.inj hEq2)
    subst h2eq
    obtain ⟨huRes, rfl⟩ := hu64.xor n1 n2 wa wb _ _ _ hu1 hu2 hXor.toEvalFn
    obtain ⟨hltRes, rfl, rfl⟩ := hu64.to_field (n1 ^^^ n2) wRes _ _ _ huRes hToF.toEvalFn
    exact ⟨.lit (.nat (n1 ^^^ n2)), by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs],
      .nat (Nat.lt_min.mpr ⟨hltRes, hltRes⟩), ext1.trans ext2⟩

private theorem eval_wrapBool_poly {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {world : World F} (hkeys : (P.ctors.map (·.key)).Nodup)
    {dDepth : Nat} {locals : Environment F Nat} {condExpr res : Lower.Expr}
    {target : Rep} {st st' : TState} {h h' : Heap F} {r : SourceValue F} {b : Bool}
    {fW : TCx → Lower.Expr → Rep → TLowerM Lower.Expr}
    {fL : {α : Type} → Except String α → TLowerM α}
    {fM : (Demand → Demand) → TLowerM Unit}
    (hw : fW { P, cert, feat := scanFeatures P, sched } condExpr target st = .ok (res, st'))
    (hdef : ∀ cx ce tgt s, fW cx ce tgt s =
      (match tgt with
       | .enum ind =>
         match cx.boolEnum? with
         | some (bind, tt, ff) =>
           if bind == ind then
             pure (matchE ce
               [(.literal 0, .construct (enumName ind) (some []) ff []),
                (.wildcard, .construct (enumName ind) (some []) tt [])])
           else fL (throw "wrapBool: enum mismatch")
         | none => fL (throw "wrapBool: Bool enum missing")
       | .obj => do
         fM fun d => { d with needObj := true }
         let some (tt, ff) := (Lower.Cx.mk cx.P).boolNames
           | fL (throw "wrapBool: Bool pins missing")
         pure (matchE ce [(.literal 0, mk ff []), (.wildcard, mk tt [])])
       | _ => fL (throw s!"wrapBool: unexpected target rep {reprStr tgt}")) s)
    (hfL : ∀ {α} (x : Except String α) s, fL x s = match x with | .ok a => .ok (a, s) | .error err => .error err)
    (hfM : ∀ u s, fM u s = .ok ((), { s with demand := u s.demand }))
    (ev : EvalExprN world dDepth [] locals (qualifyExprF F res) h r h')
    (hcond : ∀ v hm, EvalExprN world dDepth [] locals (qualifyExprF F condExpr) h v hm →
      v = .field (if b then (1 : F) else 0) ∧ Heap.Extends h hm)
    (hTarget : ∀ v, Fir.boolVal P b = some v → CoerceTargetOk P cert (scanFeatures P) target v) :
    ∃ v, Fir.boolVal P b = some v ∧ TVR P cert (scanFeatures P) h' target v r ∧ Heap.Extends h h' := by
  rw [hdef] at hw
  exact eval_wrapBool hkeys hw hfL hfM ev hcond hTarget

private theorem wrapBool_stateLe_poly {cx : TCx} {ce res : Lower.Expr} {target : Rep}
    {st st' : TState}
    {fW : TCx → Lower.Expr → Rep → TLowerM Lower.Expr}
    {fL : {α : Type} → Except String α → TLowerM α}
    {fM : (Demand → Demand) → TLowerM Unit}
    (hw : fW cx ce target st = .ok (res, st'))
    (hdef : ∀ cx ce tgt s, fW cx ce tgt s =
      (match tgt with
       | .enum ind =>
         match cx.boolEnum? with
         | some (bind, tt, ff) =>
           if bind == ind then
             pure (matchE ce
               [(.literal 0, .construct (enumName ind) (some []) ff []),
                (.wildcard, .construct (enumName ind) (some []) tt [])])
           else fL (throw "wrapBool: enum mismatch")
         | none => fL (throw "wrapBool: Bool enum missing")
       | .obj => do
         fM fun d => { d with needObj := true }
         let some (tt, ff) := (Lower.Cx.mk cx.P).boolNames
           | fL (throw "wrapBool: Bool pins missing")
         pure (matchE ce [(.literal 0, mk ff []), (.wildcard, mk tt [])])
       | _ => fL (throw s!"wrapBool: unexpected target rep {reprStr tgt}")) s)
    (hfL : ∀ {α} (x : Except String α) s, fL x s = match x with | .ok a => .ok (a, s) | .error err => .error err)
    (hfM : ∀ u s, fM u s = .ok ((), { s with demand := u s.demand })) :
    TStateLe st st' := by
  rw [hdef] at hw
  cases target with
  | «enum» ind =>
    cases hbe : cx.boolEnum? with
    | none => simp [hbe, hfL, throw, throwThe, MonadExceptOf.throw] at hw
    | some p =>
      simp only [hbe] at hw; split at hw
      · simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
        obtain ⟨_, rfl⟩ := hw; exact TStateLe.refl _
      · simp [hfL, throw, throwThe, MonadExceptOf.throw] at hw
  | obj =>
    obtain ⟨sM, hleM, _, hw⟩ := tMark_step_inv hw hfM
      (fun _ => by constructor <;> first | exact id | (intro _; rfl))
    cases hbn : (Lower.Cx.mk cx.P).boolNames with
    | none => simp [hbn, hfL, throw, throwThe, MonadExceptOf.throw] at hw
    | some p =>
      simp only [hbn, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
      obtain ⟨_, rfl⟩ := hw; exact hleM
  | _ => simp [hfL, throw, throwThe, MonadExceptOf.throw] at hw

private theorem wrapBool_scrutinee_eval_poly {world : World F} {dDepth : Nat}
    {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F}
    {cx : TCx} {ce res : Lower.Expr} {target : Rep} {st st' : TState}
    {fW : TCx → Lower.Expr → Rep → TLowerM Lower.Expr}
    {fL : {α : Type} → Except String α → TLowerM α}
    {fM : (Demand → Demand) → TLowerM Unit}
    (hw : fW cx ce target st = .ok (res, st'))
    (hdef : ∀ cx ce tgt s, fW cx ce tgt s =
      (match tgt with
       | .enum ind =>
         match cx.boolEnum? with
         | some (bind, tt, ff) =>
           if bind == ind then
             pure (matchE ce
               [(.literal 0, .construct (enumName ind) (some []) ff []),
                (.wildcard, .construct (enumName ind) (some []) tt [])])
           else fL (throw "wrapBool: enum mismatch")
         | none => fL (throw "wrapBool: Bool enum missing")
       | .obj => do
         fM fun d => { d with needObj := true }
         let some (tt, ff) := (Lower.Cx.mk cx.P).boolNames
           | fL (throw "wrapBool: Bool pins missing")
         pure (matchE ce [(.literal 0, mk ff []), (.wildcard, mk tt [])])
       | _ => fL (throw s!"wrapBool: unexpected target rep {reprStr tgt}")) s)
    (hfL : ∀ {α} (x : Except String α) s, fL x s = match x with | .ok a => .ok (a, s) | .error err => .error err)
    (hfM : ∀ u s, fM u s = .ok ((), { s with demand := u s.demand }))
    (ev : EvalExprN world dDepth [] locals (qualifyExprF F res) h r h') :
    ∃ v hm, EvalExprN world dDepth [] locals (qualifyExprF F ce) h v hm := by
  rw [hdef] at hw
  cases target with
  | «enum» ind =>
    cases hbe : cx.boolEnum? with
    | none => simp [hbe, hfL, throw, throwThe, MonadExceptOf.throw] at hw
    | some p =>
      simp only [hbe] at hw; split at hw
      · simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        obtain ⟨v0, hm0, ev0, _⟩ := evalExprN_match_lit_wild_inv ev
        exact ⟨v0, hm0, ev0⟩
      · simp [hfL, throw, throwThe, MonadExceptOf.throw] at hw
  | obj =>
    obtain ⟨_, _, _, hw⟩ := tMark_step_inv hw hfM
      (fun _ => by constructor <;> first | exact id | (intro _; rfl))
    cases hbn : (Lower.Cx.mk cx.P).boolNames with
    | none => simp [hbn, hfL, throw, throwThe, MonadExceptOf.throw] at hw
    | some p =>
      simp only [hbn, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      obtain ⟨v0, hm0, ev0, _⟩ := evalExprN_match_lit_wild_inv ev
      exact ⟨v0, hm0, ev0⟩
  | _ => simp [hfL, throw, throwThe, MonadExceptOf.throw] at hw

private theorem eval_constSubMatch_poly {world : World F} {d : Nat} {locals : Environment F Nat}
    (fc : FieldCompatible64 F) {fCS : Lower.Expr → Nat → Lower.Expr}
    {tmp : String} {n k : Nat} {h h' : Heap F} {r : SourceValue F}
    (hn : n < natLimit) (hk : k < natLimit)
    (hloc : locals.find? (·.1 == tmp) = some (tmp, .field (n : F)))
    (ev : EvalExprN world d [] locals (qualifyExprF F (fCS (vE tmp) k)) h r h')
    (hdef : ∀ xE m, fCS xE m = constSubMatchE xE m) :
    r = .field ((n - k : Nat) : F) ∧ h' = h := by
  rw [hdef] at ev
  exact evalExprN_constSubMatch fc hn hk hloc ev

/-- Backward simulation of `TypedLower.tPrimE` for all 16 non-word `Nat` primitives. -/
theorem eval_tPrimE {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld P cert sched lp world)
    (hwf : cert.WF) (hkeys : (P.ctors.map (·.key)).Nodup) (hnd : (objCtorNames P).Nodup)
    (hdatas : datasNatCoreReps P cert (scanFeatures P) = true)
    {dDepth : Nat} {fsh : FunShapes} {vm : TVarMap} {op : Prim} {as : List Arg} {target : Rep}
    {st st' : TState} {res : Lower.Expr}
    {ρ : Env} {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F}
    (hnoW : op.isWord = false)
    (hvmCore : ∀ p ∈ vm, isNatCoreRep p.2.2 = true)
    (hlocVm : AllLocalLt st.nextLocal (vm.map fun p => p.2.1))
    (htCore : isNatCoreRep target = true)
    (hprim : tPrimE { P, cert, feat := scanFeatures P, sched } vm op as target st = .ok (res, st'))
    (hdem : DemandLe st'.demand lp.demand)
    (henv : TEnvRel P cert (scanFeatures P) h fsh vm ρ locals)
    (ev : EvalExprN world dDepth [] locals (qualifyExprF F res) h r h')
    (hTarget : ∀ v, evalRhs P ρ (.prim op as) = .ok v →
      CoerceTargetOk P cert (scanFeatures P) target v) :
    ∃ v, evalRhs P ρ (.prim op as) = .ok v ∧
      TVR P cert (scanFeatures P) h' target v r ∧ Heap.Extends h h' := by
  set cx : TCx := { P, cert, feat := scanFeatures P, sched }
  cases op with
  | word _ _ => simp [Lam.Prim.isWord] at hnoW
  | natPred =>
    unfold tPrimE at hprim
    rcases as with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> dsimp only at hprim
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · obtain ⟨⟨ea, ra⟩, s1, hraw, hprim⟩ := tBind_step_inv hprim
      dsimp only at hprim
      obtain ⟨xa, s2, hco1, hprim⟩ := tBind_step_inv hprim
      obtain ⟨tmp, s3, htmp, hco2⟩ := tBind_step_inv hprim
      have htmpEq : tmp = localName s2.nextLocal ∧ s3 = { s2 with nextLocal := s2.nextLocal + 1 } := by
        have hstep : ∀ (fF : TLowerM String), fF s2 = .ok (tmp, s3) →
            (∀ s, fF s = .ok (localName s.nextLocal, { s with nextLocal := s.nextLocal + 1 })) →
            tmp = localName s2.nextLocal ∧ s3 = { s2 with nextLocal := s2.nextLocal + 1 } := by
          intro fF hf hdef; rw [hdef] at hf; simp only [Except.ok.injEq, Prod.mk.injEq] at hf
          exact ⟨hf.1.symm, hf.2.symm⟩
        exact hstep _ htmp (fun _ => rfl)
      obtain ⟨rfl, rfl⟩ := htmpEq
      have hdemS2 : DemandLe s2.demand lp.demand := (coerceE_spec hco2).1.demand.trans hdem
      refine eval_coerceE fc lw hwf hkeys hnd hdatas hco2 rfl htCore hdem ev
        (Q := fun v => evalRhs P ρ (.prim .natPred [a]) = .ok v)
        (fun w0 hm evBody => ?_) hTarget
      simp only [letE, qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
        Aiur.Generic.Pattern.map] at evBody
      obtain ⟨wa, hm1, evXa, evMatch⟩ := evalExprN_let_bind_inv evBody
      obtain ⟨n, haEv, hfb, hn, rfl, ext1⟩ :=
        eval_tArgRaw_to_nat fc lw hwf hkeys hnd hdatas hraw hco1 hvmCore hdemS2 henv evXa
      obtain ⟨vn, hm2, evV, hbr⟩ := evalExprN_match_lit_wild_inv evMatch
      simp only [vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evV
      obtain ⟨hl, rfl⟩ := evalExprN_var_inv evV
      simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨_, rfl⟩ := hl
      rcases hbr with ⟨hn0F, ev0⟩ | ⟨hnNeF, evSub⟩
      · have hn0 : n = 0 := fc.natCast_inj56 hn (by unfold natLimit; omega) (by simpa using Value.field.inj hn0F)
        subst hn0
        simp only [litE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev0
        obtain ⟨rfl, rfl⟩ := evalExprN_literal_inv ev0
        refine ⟨.lit (.nat 0), by simp [evalRhs, evalArgs, haEv, primResult, natArgs],
          .nat (Nat.lt_min.mpr ⟨by omega, by omega⟩), ext1⟩
      · have hnPos : 0 < n := by
          by_contra hle; have hn0 : n = 0 := by omega
          exact hnNeF (by simp [hn0])
        simp only [subE, vE, litE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evSub
        obtain ⟨vl, vr, _, evL, evR, hsub⟩ := evalExprN_binary_inv evSub
        obtain ⟨hll, rfl⟩ := evalExprN_var_inv evL
        simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hll
        obtain ⟨_, rfl⟩ := hll
        obtain ⟨rfl, rfl⟩ := evalExprN_literal_inv evR
        simp only [evalBinOp, Except.ok.injEq] at hsub
        rw [← hsub, ← Nat.cast_sub hnPos]
        refine ⟨.lit (.nat (n - 1)), by simp [evalRhs, evalArgs, haEv, primResult, natArgs],
          .nat (Nat.lt_min.mpr ⟨by omega, by omega⟩), ext1⟩
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
  | natAdd =>
    unfold tPrimE at hprim
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at hprim
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · obtain ⟨⟨ea, ra⟩, s1, hrawA, hprim⟩ := tBind_step_inv hprim
      dsimp only at hprim
      obtain ⟨⟨eb, rb⟩, s2, hrawB, hprim⟩ := tBind_step_inv hprim
      dsimp only at hprim
      obtain ⟨xa, s3, hcoA, hprim⟩ := tBind_step_inv hprim
      obtain ⟨xb, s4, hcoB, hprim⟩ := tBind_step_inv hprim
      by_cases hfast : (ra.isFieldNat && rb.isFieldNat && decide (ra.fieldBound + rb.fieldBound ≤ natLimit)) = true
      · simp only [hfast, ↓reduceIte] at hprim
        have hsumBound : ra.fieldBound + rb.fieldBound ≤ natLimit := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hfast; exact hfast.2
        have hdemS4 : DemandLe s4.demand lp.demand := (coerceE_spec hprim).1.demand.trans hdem
        have hdemS3 : DemandLe s3.demand lp.demand := (coerceE_spec hcoB).1.demand.trans hdemS4
        refine eval_coerceE fc lw hwf hkeys hnd hdatas hprim rfl htCore hdem ev
          (Q := fun v => evalRhs P ρ (.prim .natAdd [a, b]) = .ok v)
          (fun w0 hm evAdd => ?_) hTarget
        simp only [addE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evAdd
        obtain ⟨vl, vr, hm1, evL, evR, hadd⟩ := evalExprN_binary_inv evAdd
        obtain ⟨n1, haEv, hfb1, hn1, rfl, ext1⟩ :=
          eval_tArgRaw_to_nat fc lw hwf hkeys hnd hdatas hrawA hcoA hvmCore hdemS3 henv evL
        obtain ⟨n2, hbEv, hfb2, hn2, rfl, ext2⟩ :=
          eval_tArgRaw_to_nat fc lw hwf hkeys hnd hdatas hrawB hcoB hvmCore hdemS4 (henv.extend ext1) evR
        simp only [evalBinOp, Except.ok.injEq] at hadd
        rw [← hadd, ← Nat.cast_add]
        have hltSum : n1 + n2 < ra.fieldBound + rb.fieldBound := Nat.add_lt_add hfb1 hfb2
        refine ⟨.lit (.nat (n1 + n2)), by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs],
          .nat (Nat.lt_min.mpr ⟨hltSum, Nat.lt_of_lt_of_le hltSum hsumBound⟩), ext1.trans ext2⟩
      · simp only [hfast, Bool.false_eq_true, ↓reduceIte] at hprim
        obtain ⟨s5, hle5, hdem5, hprim⟩ := tMark_step_inv hprim (fun _ _ => rfl)
          (fun _ => by constructor <;> first | exact id | (intro _; rfl))
        obtain ⟨tmp, s6, htmp, hco2⟩ := tBind_step_inv hprim
        have htmpEq : tmp = localName s5.nextLocal ∧ s6 = { s5 with nextLocal := s5.nextLocal + 1 } := by
          have hstep : ∀ (fF : TLowerM String), fF s5 = .ok (tmp, s6) →
              (∀ s, fF s = .ok (localName s.nextLocal, { s with nextLocal := s.nextLocal + 1 })) →
              tmp = localName s5.nextLocal ∧ s6 = { s5 with nextLocal := s5.nextLocal + 1 } := by
            intro fF hf hdef; rw [hdef] at hf; simp only [Except.ok.injEq, Prod.mk.injEq] at hf
            exact ⟨hf.1.symm, hf.2.symm⟩
          exact hstep _ htmp (fun _ => rfl)
        obtain ⟨rfl, rfl⟩ := htmpEq
        have hle56 : TStateLe s5 { s5 with nextLocal := s5.nextLocal + 1 } :=
          ⟨Nat.le_succ _, Nat.le_refl _, rfl, DemandLe.refl _⟩
        have hdemS5 : DemandLe s5.demand lp.demand := (hle56.trans (coerceE_spec hco2).1).demand.trans hdem
        have hdemS4 : DemandLe s4.demand lp.demand := hle5.demand.trans hdemS5
        have hdemS3 : DemandLe s3.demand lp.demand := (coerceE_spec hcoB).1.demand.trans hdemS4
        have hneed56 : lp.demand.needCheckU56 = true := hdemS5.needCheckU56 (by rw [hdem5])
        have hneNone : lp.tier ≠ .none := tier_ne_none_of_usesRangeCheck lw.lowered (by simp [hneed56])
        refine eval_coerceE fc lw hwf hkeys hnd hdatas hco2 rfl htCore hdem ev
          (Q := fun v => evalRhs P ρ (.prim .natAdd [a, b]) = .ok v)
          (fun w0 hm evBody => ?_) hTarget
        simp only [letE, addE, seqE, callE, vE, qualifyExprF, qualifyExpr, qualifyPat,
          qualifyName_check_u56, Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map,
          List.map] at evBody
        obtain ⟨wSum, hm1, evAdd, evSeq⟩ := evalExprN_let_bind_inv evBody
        obtain ⟨vl, vr, hm0, evL, evR, hadd⟩ := evalExprN_binary_inv evAdd
        obtain ⟨n1, haEv, _, hn1, rfl, ext1⟩ :=
          eval_tArgRaw_to_nat fc lw hwf hkeys hnd hdatas hrawA hcoA hvmCore hdemS3 henv evL
        obtain ⟨n2, hbEv, _, hn2, rfl, ext2⟩ :=
          eval_tArgRaw_to_nat fc lw hwf hkeys hnd hdatas hrawB hcoB hvmCore hdemS4 (henv.extend ext1) evR
        simp only [evalBinOp, Except.ok.injEq] at hadd
        obtain ⟨_, hm2, evChk, evRet⟩ := evalExprN_let_wildcard_inv evSeq
        obtain ⟨_, vChk, _, _, evV1, hcal⟩ := evalExprN_call1_inv evChk
        obtain ⟨hl1, rfl⟩ := evalExprN_var_inv evV1
        simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hl1
        obtain ⟨_, rfl⟩ := hl1
        obtain ⟨_, rfl, m, hmLt, hmEq⟩ :=
          eval_check_u56 (lw.byteCheck hneNone) (lw.hasCheckU56 (Or.inl hneed56)) hcal.toEvalFn
        have hsumEq : n1 + n2 = m := by
          apply fc.natCast_inj
          · unfold fieldBound64 natLimit at *; omega
          · unfold fieldBound64 natLimit at *; omega
          · rw [Nat.cast_add]
            exact Value.field.inj (hadd.trans hmEq)
        obtain ⟨hl2, rfl⟩ := evalExprN_var_inv evRet
        simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hl2
        obtain ⟨_, rfl⟩ := hl2
        rw [hmEq, ← hsumEq]
        have hsumLt : n1 + n2 < natLimit := hsumEq ▸ hmLt
        exact ⟨.lit (.nat (n1 + n2)), by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs],
          .nat (Nat.lt_min.mpr ⟨hsumLt, hsumLt⟩), ext1.trans ext2⟩
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
  | natSub =>
    unfold tPrimE at hprim
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at hprim
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · obtain ⟨⟨ea, ra⟩, s1, hrawA, hprim⟩ := tBind_step_inv hprim
      dsimp only at hprim
      obtain ⟨xa, s2, hcoA, hprim⟩ := tBind_step_inv hprim
      have hsubSlow :
          (do let (eb, rb) ← tArgRaw cx vm b
              let xb ← coerceE cx rb (.nat natLimit) eb
              let _ ← (fun s => .ok ((), { s with demand := { s.demand with needSubBorrow56 := true } }) : TLowerM Unit)
              coerceE cx (.nat ra.fieldBound) target (.project (callE "sub_borrow_56" [xa, xb]) 0)) s2 = .ok (res, st') →
          ∃ v, evalRhs P ρ (.prim .natSub [a, b]) = .ok v ∧
            TVR P cert (scanFeatures P) h' target v r ∧ Heap.Extends h h' := by
        intro hslow
        obtain ⟨⟨eb, rb⟩, s3, hrawB, hslow⟩ := tBind_step_inv hslow
        dsimp only at hslow
        obtain ⟨xb, s4, hcoB, hslow⟩ := tBind_step_inv hslow
        obtain ⟨_, s5, hmk, hco2⟩ := tBind_step_inv hslow
        simp only [Except.ok.injEq, Prod.mk.injEq] at hmk
        obtain ⟨_, rfl⟩ := hmk
        have hdemS5 : DemandLe { s4 with demand := { s4.demand with needSubBorrow56 := true } }.demand lp.demand :=
          (coerceE_spec hco2).1.demand.trans hdem
        have hdemS4 : DemandLe s4.demand lp.demand :=
          (by constructor <;> first | exact id | (intro _; rfl) : DemandLe s4.demand _).trans hdemS5
        have hdemS2 : DemandLe s2.demand lp.demand :=
          ((tArgRaw_spec hrawB).1.trans (coerceE_spec hcoB).1).demand.trans hdemS4
        have hneedSub : lp.demand.needSubBorrow56 = true := hdemS5.needSubBorrow56 rfl
        have hneNone : lp.tier ≠ .none := tier_ne_none_of_usesRangeCheck lw.lowered (by simp [hneedSub])
        refine eval_coerceE fc lw hwf hkeys hnd hdatas hco2 rfl htCore hdem ev
          (Q := fun v => evalRhs P ρ (.prim .natSub [a, b]) = .ok v)
          (fun w0 hm evBody => ?_) hTarget
        simp only [callE, qualifyExprF, qualifyExpr, qualifyName_sub_borrow_56, Option.map_some,
          Aiur.Generic.Expr.map, List.map] at evBody
        obtain ⟨vt, evCall, hproj⟩ := evalExprN_project_inv evBody
        obtain ⟨_, va, vb, hm1, hm2, _, evA, evB, hcal⟩ := evalExprN_call2_inv evCall
        obtain ⟨n1, haEv, hfb1, hn1, rfl, ext1⟩ :=
          eval_tArgRaw_to_nat fc lw hwf hkeys hnd hdatas hrawA hcoA hvmCore hdemS2 henv evA
        obtain ⟨n2, hbEv, _, hn2, rfl, ext2⟩ :=
          eval_tArgRaw_to_nat fc lw hwf hkeys hnd hdatas hrawB hcoB hvmCore hdemS4 (henv.extend ext1) evB
        obtain ⟨rfl, hvtEq⟩ :=
          eval_sub_borrow_56 fc (lw.byteCheck hneNone) (lw.hasSubBorrow56 hneedSub) hn1 hn2 hcal.toEvalFn
        have hvt := Value.tuple.inj hvtEq; subst hvt
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hproj
        subst hproj
        exact ⟨.lit (.nat (n1 - n2)), by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs],
          .nat (Nat.lt_min.mpr ⟨by omega, by omega⟩), ext1.trans ext2⟩
      have hsubSlowPoly : ∀ (fM : (Demand → Demand) → TLowerM Unit),
          (do let (eb, rb) ← tArgRaw cx vm b
              let xb ← coerceE cx rb (.nat natLimit) eb
              fM fun d => { d with needSubBorrow56 := true }
              coerceE cx (.nat ra.fieldBound) target (.project (callE "sub_borrow_56" [xa, xb]) 0)) s2 = .ok (res, st') →
          (∀ u s, fM u s = .ok ((), { s with demand := u s.demand })) →
          ∃ v, evalRhs P ρ (.prim .natSub [a, b]) = .ok v ∧
            TVR P cert (scanFeatures P) h' target v r ∧ Heap.Extends h h' := by
        intro fM hs hfM
        apply hsubSlow
        have hEq : fM (fun d => { d with needSubBorrow56 := true }) =
            (fun s => .ok ((), { s with demand := { s.demand with needSubBorrow56 := true } }) : TLowerM Unit) := by
          funext s; exact hfM _ s
        rwa [hEq] at hs
      cases b with
      | lit l =>
        cases l with
        | nat k =>
          cases k with
          | zero =>
            have hdemS2 : DemandLe s2.demand lp.demand := (coerceE_spec hprim).1.demand.trans hdem
            refine eval_coerceE fc lw hwf hkeys hnd hdatas hprim rfl htCore hdem ev
              (Q := fun v => evalRhs P ρ (.prim .natSub [a, .lit (.nat 0)]) = .ok v)
              (fun w0 hm evXa => ?_) hTarget
            obtain ⟨n1, haEv, hfb1, hn1, rfl, ext1⟩ :=
              eval_tArgRaw_to_nat fc lw hwf hkeys hnd hdatas hrawA hcoA hvmCore hdemS2 henv evXa
            exact ⟨.lit (.nat n1),
              by simp only [evalRhs, evalArgs, haEv]; simp [Arg.eval, primResult, natArgs],
              .nat (Nat.lt_min.mpr ⟨hfb1, hn1⟩), ext1⟩
          | succ k' =>
            by_cases hle4 : k' + 1 ≤ 4
            · simp only [hle4, ↓reduceIte] at hprim
              obtain ⟨tmp, s3, htmp, hco2⟩ := tBind_step_inv hprim
              have htmpEq : tmp = localName s2.nextLocal ∧ s3 = { s2 with nextLocal := s2.nextLocal + 1 } := by
                have hstep : ∀ (fF : TLowerM String), fF s2 = .ok (tmp, s3) →
                    (∀ s, fF s = .ok (localName s.nextLocal, { s with nextLocal := s.nextLocal + 1 })) →
                    tmp = localName s2.nextLocal ∧ s3 = { s2 with nextLocal := s2.nextLocal + 1 } := by
                  intro fF hf hdef; rw [hdef] at hf; simp only [Except.ok.injEq, Prod.mk.injEq] at hf
                  exact ⟨hf.1.symm, hf.2.symm⟩
                exact hstep _ htmp (fun _ => rfl)
              obtain ⟨rfl, rfl⟩ := htmpEq
              have hdemS2 : DemandLe s2.demand lp.demand := (coerceE_spec hco2).1.demand.trans hdem
              refine eval_coerceE fc lw hwf hkeys hnd hdatas hco2 rfl htCore hdem ev
                (Q := fun v => evalRhs P ρ (.prim .natSub [a, .lit (.nat (k' + 1))]) = .ok v)
                (fun w0 hm evBody => ?_) hTarget
              simp only [letE, qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
                Aiur.Generic.Pattern.map] at evBody
              obtain ⟨wa, hm1, evXa, evCS⟩ := evalExprN_let_bind_inv evBody
              obtain ⟨n1, haEv, hfb1, hn1, rfl, ext1⟩ :=
                eval_tArgRaw_to_nat fc lw hwf hkeys hnd hdatas hrawA hcoA hvmCore hdemS2 henv evXa
              obtain ⟨rfl, rfl⟩ :=
                eval_constSubMatch_poly fc hn1 (by unfold natLimit; omega)
                  (by simp : ((localName s2.nextLocal, Value.field (n1 : F)) :: locals).find? (·.1 == localName s2.nextLocal) = _)
                  evCS (fun _ _ => rfl)
              exact ⟨.lit (.nat (n1 - (k' + 1))),
                by simp only [evalRhs, evalArgs, haEv]; simp [Arg.eval, primResult, natArgs],
                .nat (Nat.lt_min.mpr ⟨by omega, by omega⟩), ext1⟩
            · simp only [hle4, ↓reduceIte] at hprim
              exact hsubSlowPoly _ hprim (fun _ _ => rfl)
        | str _ => exact hsubSlowPoly _ hprim (fun _ _ => rfl)
      | var _ | erased => exact hsubSlowPoly _ hprim (fun _ _ => rfl)
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
  | natMul =>
    unfold tPrimE at hprim
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at hprim
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · obtain ⟨⟨ea, ra⟩, s1, hrawA, hprim⟩ := tBind_step_inv hprim
      dsimp only at hprim
      obtain ⟨⟨eb, rb⟩, s2, hrawB, hprim⟩ := tBind_step_inv hprim
      dsimp only at hprim
      obtain ⟨xa, s3, hcoA, hprim⟩ := tBind_step_inv hprim
      obtain ⟨xb, s4, hcoB, hprim⟩ := tBind_step_inv hprim
      by_cases hfast : (ra.isFieldNat && rb.isFieldNat && decide (ra.fieldBound * rb.fieldBound ≤ natLimit)) = true
      · simp only [hfast, ↓reduceIte] at hprim
        have hmulBound : ra.fieldBound * rb.fieldBound ≤ natLimit := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hfast; exact hfast.2
        have hdemS4 : DemandLe s4.demand lp.demand := (coerceE_spec hprim).1.demand.trans hdem
        have hdemS3 : DemandLe s3.demand lp.demand := (coerceE_spec hcoB).1.demand.trans hdemS4
        refine eval_coerceE fc lw hwf hkeys hnd hdatas hprim rfl htCore hdem ev
          (Q := fun v => evalRhs P ρ (.prim .natMul [a, b]) = .ok v)
          (fun w0 hm evMul => ?_) hTarget
        simp only [mulE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evMul
        obtain ⟨vl, vr, hm1, evL, evR, hmul⟩ := evalExprN_binary_inv evMul
        obtain ⟨n1, haEv, hfb1, hn1, rfl, ext1⟩ :=
          eval_tArgRaw_to_nat fc lw hwf hkeys hnd hdatas hrawA hcoA hvmCore hdemS3 henv evL
        obtain ⟨n2, hbEv, hfb2, hn2, rfl, ext2⟩ :=
          eval_tArgRaw_to_nat fc lw hwf hkeys hnd hdatas hrawB hcoB hvmCore hdemS4 (henv.extend ext1) evR
        simp only [evalBinOp, Except.ok.injEq] at hmul
        rw [← hmul, ← Nat.cast_mul]
        have hltProd : n1 * n2 < ra.fieldBound * rb.fieldBound :=
          Fir.Proof.Shape.mul_lt_mul_of_lt hfb1 hfb2
        refine ⟨.lit (.nat (n1 * n2)), by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs],
          .nat (Nat.lt_min.mpr ⟨hltProd, Nat.lt_of_lt_of_le hltProd hmulBound⟩), ext1.trans ext2⟩
      · simp only [hfast, Bool.false_eq_true, ↓reduceIte] at hprim
        obtain ⟨s5, hle5, hdem5, hco2⟩ := tMark_step_inv hprim (fun _ _ => rfl)
          (fun _ => by constructor <;> first | exact id | (intro _; rfl))
        have hdemS5 : DemandLe s5.demand lp.demand := (coerceE_spec hco2).1.demand.trans hdem
        have hdemS4 : DemandLe s4.demand lp.demand := hle5.demand.trans hdemS5
        have hdemS3 : DemandLe s3.demand lp.demand := (coerceE_spec hcoB).1.demand.trans hdemS4
        have hneedMul : lp.demand.needMul56 = true := hdemS5.needMul56 (by rw [hdem5])
        have hneedU56 : lp.demand.needCheckU56 = true := hdemS5.needCheckU56 (by rw [hdem5])
        have hneedU24 : lp.demand.needCheckU24 = true := hdemS5.needCheckU24 (by rw [hdem5])
        have hneNone : lp.tier ≠ .none := tier_ne_none_of_usesRangeCheck lw.lowered (by simp [hneedMul])
        refine eval_coerceE fc lw hwf hkeys hnd hdatas hco2 rfl htCore hdem ev
          (Q := fun v => evalRhs P ρ (.prim .natMul [a, b]) = .ok v)
          (fun w0 hm evBody => ?_) hTarget
        simp only [callE, qualifyExprF, qualifyExpr, qualifyName_mul_56, Option.map_some,
          Aiur.Generic.Expr.map, List.map] at evBody
        obtain ⟨_, va, vb, hm1, hm2, _, evA, evB, hcal⟩ := evalExprN_call2_inv evBody
        obtain ⟨n1, haEv, _, hn1, rfl, ext1⟩ :=
          eval_tArgRaw_to_nat fc lw hwf hkeys hnd hdatas hrawA hcoA hvmCore hdemS3 henv evA
        obtain ⟨n2, hbEv, _, hn2, rfl, ext2⟩ :=
          eval_tArgRaw_to_nat fc lw hwf hkeys hnd hdatas hrawB hcoB hvmCore hdemS4 (henv.extend ext1) evB
        obtain ⟨rfl, hprodLt, rfl⟩ :=
          eval_mul_56 fc (lw.byteCheck hneNone) (lw.hasSplit32_24 hneedMul)
            (lw.hasCheckU24 (Or.inl hneedU24)) (lw.hasCheckU56 (Or.inl hneedU56))
            (lw.hasMul56 hneedMul) hn1 hn2 hcal.toEvalFn
        exact ⟨.lit (.nat (n1 * n2)), by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs],
          .nat (Nat.lt_min.mpr ⟨hprodLt, hprodLt⟩), ext1.trans ext2⟩
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
  | natDiv =>
    unfold tPrimE at hprim
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at hprim
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact eval_tPrimE_divmod (isMod := false) fc lw hwf hkeys hnd hdatas hvmCore hlocVm htCore
        hdem henv hprim (fun _ _ => rfl) (fun _ => rfl) ev hTarget
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
  | natMod =>
    unfold tPrimE at hprim
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at hprim
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact eval_tPrimE_divmod (isMod := true) fc lw hwf hkeys hnd hdatas hvmCore hlocVm htCore
        hdem henv hprim (fun _ _ => rfl) (fun _ => rfl) ev hTarget
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
  | natPow =>
    unfold tPrimE at hprim
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at hprim
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · obtain ⟨xa, s1, h1, hprim⟩ := tBind_step_inv hprim
      obtain ⟨xb, s2, h2, hprim⟩ := tBind_step_inv hprim
      obtain ⟨s3, hle3, hdem3, hco⟩ := tMark_step_inv hprim (fun _ _ => rfl)
        (fun _ => by constructor <;> first | exact id | (intro _; rfl))
      have hdemS3 : DemandLe s3.demand lp.demand := (coerceE_spec hco).1.demand.trans hdem
      have hdemS2 : DemandLe s2.demand lp.demand := hle3.demand.trans hdemS3
      have hdemS1 : DemandLe s1.demand lp.demand := (tArgE_spec h2).1.demand.trans hdemS2
      have hneedPow : lp.demand.needPow56 = true := hdemS3.needPow56 (by rw [hdem3])
      have hneedDm : lp.demand.needDivMod56 = true := hdemS3.needDivMod56 (by rw [hdem3])
      have hneedMul : lp.demand.needMul56 = true := hdemS3.needMul56 (by rw [hdem3])
      have hneedU56 : lp.demand.needCheckU56 = true := hdemS3.needCheckU56 (by rw [hdem3])
      have hneedU24 : lp.demand.needCheckU24 = true := hdemS3.needCheckU24 (by rw [hdem3])
      have hneedSub : lp.demand.needSubBorrow56 = true := hdemS3.needSubBorrow56 (by rw [hdem3])
      have hneNone : lp.tier ≠ .none := tier_ne_none_of_usesRangeCheck lw.lowered (by simp [hneedDm])
      refine eval_coerceE fc lw hwf hkeys hnd hdatas hco rfl htCore hdem ev
        (Q := fun v => evalRhs P ρ (.prim .natPow [a, b]) = .ok v)
        (fun w0 hm evBody => ?_) hTarget
      simp only [callE, qualifyExprF, qualifyExpr, qualifyName_pow_56, Option.map_some,
        Aiur.Generic.Expr.map, List.map] at evBody
      obtain ⟨_, va, vb, _, _, _, evA, evB, hcal⟩ := evalExprN_call2_inv evBody
      obtain ⟨n1, haEv, hn1, rfl, ext1⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h1 hvmCore hdemS1 henv evA
      obtain ⟨n2, hbEv, hn2, rfl, ext2⟩ :=
        eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h2 hvmCore hdemS2 (henv.extend ext1) evB
      obtain ⟨rfl, hlt, rfl⟩ :=
        eval_pow_56 fc (lw.byteCheck hneNone) (lw.hasSplit32_24 hneedMul)
          (lw.hasCheckU24 (Or.inl hneedU24)) (lw.hasCheckU56 (Or.inl hneedU56))
          (lw.hasSubBorrow56 hneedSub) (lw.hasMul56 hneedMul) (lw.hasDivMod56 hneedDm)
          (lw.hasPow56Loop hneedPow) (lw.hasPow56 hneedPow) hn1 hn2 hcal.toEvalFn
      exact ⟨.lit (.nat (n1 ^ n2)), by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs],
        .nat (Nat.lt_min.mpr ⟨hlt, hlt⟩), ext1.trans ext2⟩
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
  | natGcd =>
    unfold tPrimE at hprim
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at hprim
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · obtain ⟨xa, s1, h1, hprim⟩ := tBind_step_inv hprim
      obtain ⟨xb, s2, h2, hprim⟩ := tBind_step_inv hprim
      obtain ⟨s3, hle3, hdem3, hco⟩ := tMark_step_inv hprim (fun _ _ => rfl)
        (fun _ => by constructor <;> first | exact id | (intro _; rfl))
      have hdemS3 : DemandLe s3.demand lp.demand := (coerceE_spec hco).1.demand.trans hdem
      have hdemS2 : DemandLe s2.demand lp.demand := hle3.demand.trans hdemS3
      have hdemS1 : DemandLe s1.demand lp.demand := (tArgE_spec h2).1.demand.trans hdemS2
      have hneedGcd : lp.demand.needGcd56 = true := hdemS3.needGcd56 (by rw [hdem3])
      have hneedDm : lp.demand.needDivMod56 = true := hdemS3.needDivMod56 (by rw [hdem3])
      have hneedMul : lp.demand.needMul56 = true := hdemS3.needMul56 (by rw [hdem3])
      have hneedU56 : lp.demand.needCheckU56 = true := hdemS3.needCheckU56 (by rw [hdem3])
      have hneedU24 : lp.demand.needCheckU24 = true := hdemS3.needCheckU24 (by rw [hdem3])
      have hneedSub : lp.demand.needSubBorrow56 = true := hdemS3.needSubBorrow56 (by rw [hdem3])
      have hneNone : lp.tier ≠ .none := tier_ne_none_of_usesRangeCheck lw.lowered (by simp [hneedDm])
      refine eval_coerceE fc lw hwf hkeys hnd hdatas hco rfl htCore hdem ev
        (Q := fun v => evalRhs P ρ (.prim .natGcd [a, b]) = .ok v)
        (fun w0 hm evBody => ?_) hTarget
      simp only [callE, qualifyExprF, qualifyExpr, qualifyName_gcd_56, Option.map_some,
        Aiur.Generic.Expr.map, List.map] at evBody
      obtain ⟨_, va, vb, _, _, _, evA, evB, hcal⟩ := evalExprN_call2_inv evBody
      obtain ⟨n1, haEv, hn1, rfl, ext1⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h1 hvmCore hdemS1 henv evA
      obtain ⟨n2, hbEv, hn2, rfl, ext2⟩ :=
        eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h2 hvmCore hdemS2 (henv.extend ext1) evB
      obtain ⟨rfl, hlt, rfl⟩ :=
        eval_gcd_56 fc (lw.byteCheck hneNone) (lw.hasSplit32_24 hneedMul)
          (lw.hasCheckU24 (Or.inl hneedU24)) (lw.hasCheckU56 (Or.inl hneedU56))
          (lw.hasSubBorrow56 hneedSub) (lw.hasMul56 hneedMul) (lw.hasDivMod56 hneedDm)
          (lw.hasGcd56 hneedGcd) hn1 hn2 hcal.toEvalFn
      exact ⟨.lit (.nat (Nat.gcd n1 n2)), by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs],
        .nat (Nat.lt_min.mpr ⟨hlt, hlt⟩), ext1.trans ext2⟩
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
  | natShl =>
    unfold tPrimE at hprim
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at hprim
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · obtain ⟨xa, s1, h1, hprim⟩ := tBind_step_inv hprim
      obtain ⟨xb, s2, h2, hprim⟩ := tBind_step_inv hprim
      obtain ⟨s3, hle3, hdem3, hco⟩ := tMark_step_inv hprim (fun _ _ => rfl)
        (fun _ => by constructor <;> first | exact id | (intro _; rfl))
      have hdemS3 : DemandLe s3.demand lp.demand := (coerceE_spec hco).1.demand.trans hdem
      have hdemS2 : DemandLe s2.demand lp.demand := hle3.demand.trans hdemS3
      have hdemS1 : DemandLe s1.demand lp.demand := (tArgE_spec h2).1.demand.trans hdemS2
      have hneedShl : lp.demand.needShl56 = true := hdemS3.needShl56 (by rw [hdem3])
      have hneedPow : lp.demand.needPow56 = true := hdemS3.needPow56 (by rw [hdem3])
      have hneedDm : lp.demand.needDivMod56 = true := hdemS3.needDivMod56 (by rw [hdem3])
      have hneedMul : lp.demand.needMul56 = true := hdemS3.needMul56 (by rw [hdem3])
      have hneedU56 : lp.demand.needCheckU56 = true := hdemS3.needCheckU56 (by rw [hdem3])
      have hneedU24 : lp.demand.needCheckU24 = true := hdemS3.needCheckU24 (by rw [hdem3])
      have hneedSub : lp.demand.needSubBorrow56 = true := hdemS3.needSubBorrow56 (by rw [hdem3])
      have hneNone : lp.tier ≠ .none := tier_ne_none_of_usesRangeCheck lw.lowered (by simp [hneedDm])
      refine eval_coerceE fc lw hwf hkeys hnd hdatas hco rfl htCore hdem ev
        (Q := fun v => evalRhs P ρ (.prim .natShl [a, b]) = .ok v)
        (fun w0 hm evBody => ?_) hTarget
      simp only [callE, qualifyExprF, qualifyExpr, qualifyName_shl_56, Option.map_some,
        Aiur.Generic.Expr.map, List.map] at evBody
      obtain ⟨_, va, vb, _, _, _, evA, evB, hcal⟩ := evalExprN_call2_inv evBody
      obtain ⟨n1, haEv, hn1, rfl, ext1⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h1 hvmCore hdemS1 henv evA
      obtain ⟨n2, hbEv, hn2, rfl, ext2⟩ :=
        eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h2 hvmCore hdemS2 (henv.extend ext1) evB
      obtain ⟨rfl, hlt, rfl⟩ :=
        eval_shl_56 fc (lw.byteCheck hneNone) (lw.hasSplit32_24 hneedMul)
          (lw.hasCheckU24 (Or.inl hneedU24)) (lw.hasCheckU56 (Or.inl hneedU56))
          (lw.hasSubBorrow56 hneedSub) (lw.hasMul56 hneedMul) (lw.hasDivMod56 hneedDm)
          (lw.hasPow56Loop hneedPow) (lw.hasPow56 hneedPow) (lw.hasShl56 hneedShl)
          hn1 hn2 hcal.toEvalFn
      exact ⟨.lit (.nat (Nat.shiftLeft n1 n2)),
        by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs, Nat.shiftLeft_eq],
        .nat (Nat.lt_min.mpr ⟨hlt, hlt⟩), ext1.trans ext2⟩
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
  | natShr =>
    unfold tPrimE at hprim
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at hprim
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · obtain ⟨xa, s1, h1, hprim⟩ := tBind_step_inv hprim
      obtain ⟨xb, s2, h2, hprim⟩ := tBind_step_inv hprim
      obtain ⟨s3, hle3, hdem3, hco⟩ := tMark_step_inv hprim (fun _ _ => rfl)
        (fun _ => by constructor <;> first | exact id | (intro _; rfl))
      have hdemS3 : DemandLe s3.demand lp.demand := (coerceE_spec hco).1.demand.trans hdem
      have hdemS2 : DemandLe s2.demand lp.demand := hle3.demand.trans hdemS3
      have hdemS1 : DemandLe s1.demand lp.demand := (tArgE_spec h2).1.demand.trans hdemS2
      have hneedShr : lp.demand.needShr56 = true := hdemS3.needShr56 (by rw [hdem3])
      have hneedPow : lp.demand.needPow56 = true := hdemS3.needPow56 (by rw [hdem3])
      have hneedDm : lp.demand.needDivMod56 = true := hdemS3.needDivMod56 (by rw [hdem3])
      have hneedMul : lp.demand.needMul56 = true := hdemS3.needMul56 (by rw [hdem3])
      have hneedU56 : lp.demand.needCheckU56 = true := hdemS3.needCheckU56 (by rw [hdem3])
      have hneedU24 : lp.demand.needCheckU24 = true := hdemS3.needCheckU24 (by rw [hdem3])
      have hneedSub : lp.demand.needSubBorrow56 = true := hdemS3.needSubBorrow56 (by rw [hdem3])
      have hneNone : lp.tier ≠ .none := tier_ne_none_of_usesRangeCheck lw.lowered (by simp [hneedDm])
      refine eval_coerceE fc lw hwf hkeys hnd hdatas hco rfl htCore hdem ev
        (Q := fun v => evalRhs P ρ (.prim .natShr [a, b]) = .ok v)
        (fun w0 hm evBody => ?_) hTarget
      simp only [callE, qualifyExprF, qualifyExpr, qualifyName_shr_56, Option.map_some,
        Aiur.Generic.Expr.map, List.map] at evBody
      obtain ⟨_, va, vb, _, _, _, evA, evB, hcal⟩ := evalExprN_call2_inv evBody
      obtain ⟨n1, haEv, hn1, rfl, ext1⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h1 hvmCore hdemS1 henv evA
      obtain ⟨n2, hbEv, hn2, rfl, ext2⟩ :=
        eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h2 hvmCore hdemS2 (henv.extend ext1) evB
      obtain ⟨rfl, hlt, rfl⟩ :=
        eval_shr_56 fc (lw.byteCheck hneNone) (lw.hasSplit32_24 hneedMul)
          (lw.hasCheckU24 (Or.inl hneedU24)) (lw.hasCheckU56 (Or.inl hneedU56))
          (lw.hasSubBorrow56 hneedSub) (lw.hasMul56 hneedMul) (lw.hasDivMod56 hneedDm)
          (lw.hasPow56Loop hneedPow) (lw.hasPow56 hneedPow) (lw.hasShr56 hneedShr)
          hn1 hn2 hcal.toEvalFn
      refine ⟨.lit (.nat (Nat.shiftRight n1 n2)), ?_,
        .nat (Nat.lt_min.mpr ⟨hlt, hlt⟩), ext1.trans ext2⟩
      simp only [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs, Option.map_some, Lam.Prim.sem,
        Lam.Prim.sem.srcOp, Src.PrimOp.eval2, Sem.Result.ok.injEq, Fir.Val.lit.injEq,
        Lit.nat.injEq]
      change (if n1.log2 < n2 then 0 else n1 / 2 ^ n2) = n1 >>> n2
      rw [Nat.shiftRight_eq_div_pow]
      split
      · rename_i hlog
        cases n1 with
        | zero => simp
        | succ m =>
          exact (Nat.div_eq_of_lt ((Nat.log2_lt (by omega)).mp hlog)).symm
      · rfl
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
  | natBeq =>
    unfold tPrimE at hprim
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at hprim
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · obtain ⟨xa, s1, h1, hprim⟩ := tBind_step_inv hprim
      obtain ⟨xb, s2, h2, hwrap⟩ := tBind_step_inv hprim
      have hleWrap : TStateLe s2 st' :=
        wrapBool_stateLe_poly hwrap (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      have hdemS2 : DemandLe s2.demand lp.demand := hleWrap.demand.trans hdem
      have hdemS1 : DemandLe s1.demand lp.demand := (tArgE_spec h2).1.demand.trans hdemS2
      have hcondExist : ∃ n1 n2, a.eval ρ = some (.lit (.nat n1)) ∧ b.eval ρ = some (.lit (.nat n2)) ∧
          ∀ v hm, EvalExprN world dDepth [] locals
            (qualifyExprF F (matchE (subE xa xb) [(.literal 0, litE 1), (.wildcard, litE 0)])) h v hm →
            v = .field (if (n1 == n2) then (1 : F) else 0) ∧ Heap.Extends h hm := by
        obtain ⟨v0, hm0, ev0⟩ :=
          wrapBool_scrutinee_eval_poly hwrap (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ev
        obtain ⟨vs0, hms0, evSub0, _⟩ := evalExprN_match_lit_wild_inv ev0
        simp only [subE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evSub0
        obtain ⟨_, _, _, evA0, evB0, _⟩ := evalExprN_binary_inv evSub0
        obtain ⟨n1, haEv, hn1, _, ext10⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h1 hvmCore hdemS1 henv evA0
        obtain ⟨n2, hbEv, hn2, _, _⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h2 hvmCore hdemS2 (henv.extend ext10) evB0
        refine ⟨n1, n2, haEv, hbEv, fun v hm evC => ?_⟩
        obtain ⟨vs, hms, evSub, hbr⟩ := evalExprN_match_lit_wild_inv evC
        simp only [subE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evSub
        obtain ⟨vl, vr, hm1, evA, evB, hsub⟩ := evalExprN_binary_inv evSub
        obtain ⟨n1', haEv', hn1', rfl, ext1⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h1 hvmCore hdemS1 henv evA
        obtain ⟨n2', hbEv', hn2', rfl, ext2⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h2 hvmCore hdemS2 (henv.extend ext1) evB
        rw [haEv, Option.some.injEq] at haEv'; cases haEv'
        rw [hbEv, Option.some.injEq] at hbEv'; cases hbEv'
        simp only [evalBinOp, Except.ok.injEq] at hsub
        rcases hbr with ⟨h0, ev1⟩ | ⟨hne, ev0'⟩
        · have heqF : (n1 : F) = (n2 : F) := sub_eq_zero.mp (by simpa using Value.field.inj (hsub.trans h0))
          have heqN : n1 = n2 := fc.natCast_inj56 hn1 hn2 heqF
          subst heqN
          simp only [litE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev1
          obtain ⟨rfl, rfl⟩ := evalExprN_literal_inv ev1
          exact ⟨by simp, ext1.trans ext2⟩
        · have hneN : n1 ≠ n2 := fun hEq => by
            subst hEq; exact hne (by simp [← hsub])
          simp only [litE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev0'
          obtain ⟨rfl, rfl⟩ := evalExprN_literal_inv ev0'
          have hbf : (n1 == n2) = false := beq_false_of_ne hneN
          exact ⟨by simp [hbf], ext1.trans ext2⟩
      obtain ⟨n1, n2, haEv, hbEv, hcond⟩ := hcondExist
      obtain ⟨v, hbv, htvr, ext⟩ :=
        eval_wrapBool_poly hkeys hwrap (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
          ev hcond (fun v hv => hTarget v (by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs, hv, Sem.Result.ofOption]))
      exact ⟨v, by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs, hbv, Sem.Result.ofOption], htvr, ext⟩
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
  | natBle =>
    unfold tPrimE at hprim
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at hprim
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · obtain ⟨xa, s1, h1, hprim⟩ := tBind_step_inv hprim
      obtain ⟨xb, s2, h2, hprim⟩ := tBind_step_inv hprim
      obtain ⟨s3, hle3, hdem3, hwrap⟩ := tMark_step_inv hprim (fun _ _ => rfl)
        (fun _ => by constructor <;> first | exact id | (intro _; rfl))
      have hleWrap : TStateLe s3 st' :=
        wrapBool_stateLe_poly hwrap (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      have hdemS3 : DemandLe s3.demand lp.demand := hleWrap.demand.trans hdem
      have hdemS2 : DemandLe s2.demand lp.demand := hle3.demand.trans hdemS3
      have hdemS1 : DemandLe s1.demand lp.demand := (tArgE_spec h2).1.demand.trans hdemS2
      have hneedSub : lp.demand.needSubBorrow56 = true := hdemS3.needSubBorrow56 (by rw [hdem3])
      have hneNone : lp.tier ≠ .none := tier_ne_none_of_usesRangeCheck lw.lowered (by simp [hneedSub])
      have hcondExist : ∃ n1 n2, a.eval ρ = some (.lit (.nat n1)) ∧ b.eval ρ = some (.lit (.nat n2)) ∧
          ∀ v hm, EvalExprN world dDepth [] locals
            (qualifyExprF F (.project (callE "sub_borrow_56" [xb, xa]) 1)) h v hm →
            v = .field (if decide (n1 ≤ n2) then (1 : F) else 0) ∧ Heap.Extends h hm := by
        obtain ⟨v0, hm0, ev0⟩ :=
          wrapBool_scrutinee_eval_poly hwrap (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ev
        simp only [callE, qualifyExprF, qualifyExpr, qualifyName_sub_borrow_56, Option.map_some,
          Aiur.Generic.Expr.map, List.map] at ev0
        obtain ⟨_, evCall0, _⟩ := evalExprN_project_inv ev0
        obtain ⟨_, _, _, _, _, _, evB0, evA0, _⟩ := evalExprN_call2_inv evCall0
        obtain ⟨n2, hbEv, hn2, _, extB0⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h2 hvmCore hdemS2 henv evB0
        obtain ⟨n1, haEv, hn1, _, _⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h1 hvmCore hdemS1 (henv.extend extB0) evA0
        refine ⟨n1, n2, haEv, hbEv, fun v hm evC => ?_⟩
        simp only [callE, qualifyExprF, qualifyExpr, qualifyName_sub_borrow_56, Option.map_some,
          Aiur.Generic.Expr.map, List.map] at evC
        obtain ⟨vt, evCall, hproj⟩ := evalExprN_project_inv evC
        obtain ⟨_, vb, va, _, _, _, evB, evA, hcal⟩ := evalExprN_call2_inv evCall
        obtain ⟨n2', hbEv', hn2', rfl, extB⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h2 hvmCore hdemS2 henv evB
        obtain ⟨n1', haEv', hn1', rfl, extA⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h1 hvmCore hdemS1 (henv.extend extB) evA
        rw [haEv, Option.some.injEq] at haEv'; cases haEv'
        rw [hbEv, Option.some.injEq] at hbEv'; cases hbEv'
        obtain ⟨rfl, hvtEq⟩ :=
          eval_sub_borrow_56 fc (lw.byteCheck hneNone) (lw.hasSubBorrow56 hneedSub) hn2 hn1 hcal.toEvalFn
        have hvt := Value.tuple.inj hvtEq; subst hvt
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hproj
        subst hproj
        exact ⟨by by_cases hle : n1 ≤ n2 <;> simp [hle], extB.trans extA⟩
      obtain ⟨n1, n2, haEv, hbEv, hcond⟩ := hcondExist
      obtain ⟨v, hbv, htvr, ext⟩ :=
        eval_wrapBool_poly hkeys hwrap (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
          ev hcond (fun v hv => hTarget v (by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs, hv, Sem.Result.ofOption]))
      exact ⟨v, by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs, hbv, Sem.Result.ofOption], htvr, ext⟩
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
  | natBlt =>
    unfold tPrimE at hprim
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at hprim
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · obtain ⟨xa, s1, h1, hprim⟩ := tBind_step_inv hprim
      obtain ⟨xb, s2, h2, hprim⟩ := tBind_step_inv hprim
      obtain ⟨s3, hle3, hdem3, hwrap⟩ := tMark_step_inv hprim (fun _ _ => rfl)
        (fun _ => by constructor <;> first | exact id | (intro _; rfl))
      have hleWrap : TStateLe s3 st' :=
        wrapBool_stateLe_poly hwrap (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      have hdemS3 : DemandLe s3.demand lp.demand := hleWrap.demand.trans hdem
      have hdemS2 : DemandLe s2.demand lp.demand := hle3.demand.trans hdemS3
      have hdemS1 : DemandLe s1.demand lp.demand := (tArgE_spec h2).1.demand.trans hdemS2
      have hneedSub : lp.demand.needSubBorrow56 = true := hdemS3.needSubBorrow56 (by rw [hdem3])
      have hneNone : lp.tier ≠ .none := tier_ne_none_of_usesRangeCheck lw.lowered (by simp [hneedSub])
      have hcondExist : ∃ n1 n2, a.eval ρ = some (.lit (.nat n1)) ∧ b.eval ρ = some (.lit (.nat n2)) ∧
          ∀ v hm, EvalExprN world dDepth [] locals
            (qualifyExprF F (subE (litE 1) (.project (callE "sub_borrow_56" [xa, xb]) 1))) h v hm →
            v = .field (if decide (n1 < n2) then (1 : F) else 0) ∧ Heap.Extends h hm := by
        obtain ⟨v0, hm0, ev0⟩ :=
          wrapBool_scrutinee_eval_poly hwrap (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ev
        simp only [subE, litE, callE, qualifyExprF, qualifyExpr, qualifyName_sub_borrow_56,
          Option.map_some, Aiur.Generic.Expr.map, List.map] at ev0
        obtain ⟨_, _, _, ev10, evPr0, _⟩ := evalExprN_binary_inv ev0
        obtain ⟨_, rfl⟩ := evalExprN_literal_inv ev10
        obtain ⟨_, evCall0, _⟩ := evalExprN_project_inv evPr0
        obtain ⟨_, _, _, _, _, _, evA0, evB0, _⟩ := evalExprN_call2_inv evCall0
        obtain ⟨n1, haEv, hn1, _, extA0⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h1 hvmCore hdemS1 henv evA0
        obtain ⟨n2, hbEv, hn2, _, _⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h2 hvmCore hdemS2 (henv.extend extA0) evB0
        refine ⟨n1, n2, haEv, hbEv, fun v hm evC => ?_⟩
        simp only [subE, litE, callE, qualifyExprF, qualifyExpr, qualifyName_sub_borrow_56,
          Option.map_some, Aiur.Generic.Expr.map, List.map] at evC
        obtain ⟨v1, vge, _, ev1, evPr, hsub⟩ := evalExprN_binary_inv evC
        obtain ⟨rfl, rfl⟩ := evalExprN_literal_inv ev1
        obtain ⟨vt, evCall, hproj⟩ := evalExprN_project_inv evPr
        obtain ⟨_, va, vb, _, _, _, evA, evB, hcal⟩ := evalExprN_call2_inv evCall
        obtain ⟨n1', haEv', hn1', rfl, extA⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h1 hvmCore hdemS1 henv evA
        obtain ⟨n2', hbEv', hn2', rfl, extB⟩ := eval_tArgE_to_nat fc lw hwf hkeys hnd hdatas h2 hvmCore hdemS2 (henv.extend extA) evB
        rw [haEv, Option.some.injEq] at haEv'; cases haEv'
        rw [hbEv, Option.some.injEq] at hbEv'; cases hbEv'
        obtain ⟨rfl, hvtEq⟩ :=
          eval_sub_borrow_56 fc (lw.byteCheck hneNone) (lw.hasSubBorrow56 hneedSub) hn1 hn2 hcal.toEvalFn
        have hvt := Value.tuple.inj hvtEq; subst hvt
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hproj
        subst hproj
        simp only [evalBinOp, Except.ok.injEq] at hsub
        rw [← hsub]
        refine ⟨?_, extA.trans extB⟩
        by_cases hlt : n1 < n2
        · have hnot : ¬ (n2 ≤ n1) := by omega
          simp [hlt, hnot]
        · have hge : n2 ≤ n1 := by omega
          simp [hlt, hge]
      obtain ⟨n1, n2, haEv, hbEv, hcond⟩ := hcondExist
      obtain ⟨v, hbv, htvr, ext⟩ :=
        eval_wrapBool_poly hkeys hwrap (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
          ev hcond (fun v hv => hTarget v (by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs, hv, Sem.Result.ofOption]))
      exact ⟨v, by simp [evalRhs, evalArgs, haEv, hbEv, primResult, natArgs, hbv, Sem.Result.ofOption], htvr, ext⟩
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
  | natLand =>
    unfold tPrimE at hprim
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at hprim
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact eval_tPrimE_bitwise fc lw hwf hkeys hnd hdatas (Or.inl rfl) hvmCore htCore
        hdem henv hprim (fun _ _ => rfl) ev hTarget
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
  | natLor =>
    unfold tPrimE at hprim
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at hprim
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact eval_tPrimE_bitwise fc lw hwf hkeys hnd hdatas (Or.inr (Or.inl rfl)) hvmCore htCore
        hdem henv hprim (fun _ _ => rfl) ev hTarget
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
  | natXor =>
    unfold tPrimE at hprim
    rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> dsimp only at hprim
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))
    · exact eval_tPrimE_bitwise fc lw hwf hkeys hnd hdatas (Or.inr (Or.inr rfl)) hvmCore htCore
        hdem henv hprim (fun _ _ => rfl) ev hTarget
    · exact False.elim (tLift_throw_elim hprim (fun _ _ => rfl))

/-- Backward simulation of `TypedLower.stepDownNat` (countdown predecessor fast path),
producing `n < natLimit`, `TVR` for `n - 1`, and the `OffsRel` witness for the returned `off?`. -/
private theorem eval_stepDownNat_poly {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld P cert sched lp world)
    (hwf : cert.WF) (hkeys : (P.ctors.map (·.key)).Nodup) (hnd : (objCtorNames P).Nodup)
    (hdatas : datasNatCoreReps P cert (scanFeatures P) = true)
    {fS : TCx → OffMap → Var → String → Rep → Rep → TLowerM (Lower.Expr × Option (String × Nat))}
    {dDepth : Nat} {fsh : FunShapes} {vm : TVarMap} {offs : OffMap}
    {x : Var} {nx : String} {rx target : Rep} {n : Nat}
    {st st' : TState} {res : Lower.Expr} {off? : Option (String × Nat)}
    {ρ : Env} {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F}
    (hsd : fS { P, cert, feat := scanFeatures P, sched } offs x nx rx target st = .ok ((res, off?), st'))
    (hdef : ∀ cx offs x nx rx target s, fS cx offs x nx rx target s =
      (match offs.lookup x with
       | some (baseNm, d) =>
         if d < 256 then do
           let e ← coerceE cx (.nat rx.fieldBound) target (subE (vE baseNm) (litE (d + 1)))
           let off? := match target with | .nat _ => some (baseNm, d + 1) | _ => none
           pure (e, off?)
         else do
           let e ← coerceE cx (.nat rx.fieldBound) target (subE (vE nx) (litE 1))
           let off? := match target with | .nat _ => some (nx, 1) | _ => none
           pure (e, off?)
       | none => do
         let e ← coerceE cx (.nat rx.fieldBound) target (subE (vE nx) (litE 1))
         let off? := match target with | .nat _ => some (nx, 1) | _ => none
         pure (e, off?)) s)
    (hlook : vm.lookup x = some (nx, rx))
    (hrxFn : rx.isFieldNat = true)
    (hEnvOk : Fir.Shape.EnvOk cert dummyEnc fsh ρ)
    (htCore : isNatCoreRep target = true)
    (hdem : DemandLe st'.demand lp.demand)
    (henv : TEnvRel P cert (scanFeatures P) h fsh vm ρ locals)
    (hoffs : OffsRel ρ locals offs)
    (hρx : ρ.get? x = some (.lit (.nat n))) (hpos : 0 < n)
    (ev : EvalExprN world dDepth [] locals (qualifyExprF F res) h r h')
    (hTarget : CoerceTargetOk P cert (scanFeatures P) target (.lit (.nat (n - 1)))) :
    n < natLimit ∧
    TVR P cert (scanFeatures P) h' target (.lit (.nat (n - 1))) r ∧
    Heap.Extends h h' ∧
    (∀ baseNm d, off? = some (baseNm, d) →
      (baseNm = nx ∨ baseNm ∈ offs.map (fun p => p.2.1)) ∧
      ∀ w, locals.find? (·.1 == baseNm) = some (baseNm, w) →
        (n - 1) + d < natLimit ∧ w = .field (((n - 1) + d : Nat) : F)) := by
  rw [hdef] at hsd
  have hrepX : repOf P cert (scanFeatures P) (fsh.var x) = rx := (henv.rep_eq x nx rx hlook).symm
  have hvokX : Fir.Shape.ValOk cert dummyEnc (fsh.var x) (.lit (.nat n)) := hEnvOk x (.lit (.nat n)) hρx
  have hfbOfLim : n < natLimit → n < rx.fieldBound := by
    intro hnLim
    cases rx with
    | nat b => exact valOk_nat_bound hrepX hvokX hnLim
    | w8 =>
      obtain ⟨m, hm, heq⟩ := valOk_w8_bound hrepX hvokX
      cases heq; exact hm
    | w16 =>
      obtain ⟨m, hm, heq⟩ := valOk_w16_bound hrepX hvokX
      cases heq; exact hm
    | irr | w32 | w64 | «enum» _ | data _ | obj => simp [Rep.isFieldNat] at hrxFn
  have hnx : ∀ {e1 : Lower.Expr},
      coerceE { P, cert, feat := scanFeatures P, sched } (.nat rx.fieldBound) target
        (subE (vE nx) (litE 1)) st = .ok (e1, st') →
      EvalExprN world dDepth [] locals (qualifyExprF F e1) h r h' →
      n < natLimit ∧
      TVR P cert (scanFeatures P) h' target (.lit (.nat (n - 1))) r ∧
      Heap.Extends h h' ∧
      (∀ w, locals.find? (·.1 == nx) = some (nx, w) →
        (n - 1) + 1 < natLimit ∧ w = .field (((n - 1) + 1 : Nat) : F)) := by
    intro e1 hco ev1
    obtain ⟨v', ⟨hv'Eq, hnLim⟩, htvr', ext'⟩ :=
      eval_coerceE fc lw hwf hkeys hnd hdatas hco rfl htCore hdem ev1
        (Q := fun v => v = .lit (.nat (n - 1)) ∧ n < natLimit)
        (fun w0 hm evSub => by
          simp only [subE, vE, litE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evSub
          obtain ⟨vl, vr, _, evL, evR, hsub⟩ := evalExprN_binary_inv evSub
          obtain ⟨hloc, rfl⟩ := evalExprN_var_inv evL
          obtain ⟨rfl, rfl⟩ := evalExprN_literal_inv evR
          obtain ⟨v0, hρ0, htvr0⟩ := henv.rel x nx rx vl hlook hloc
          rw [hρx, Option.some.injEq] at hρ0; subst hρ0
          have ⟨hnFb, hnLim, hvlEq⟩ : n < rx.fieldBound ∧ n < natLimit ∧ vl = .field (n : F) := by
            cases htvr0 with
            | nat hlt => exact ⟨hlt, (Nat.lt_min.mp hlt).2, rfl⟩
            | w8 hlt => exact ⟨hlt, lt_trans hlt (by decide), rfl⟩
            | w16 hlt => exact ⟨hlt, lt_trans hlt (by decide), rfl⟩
            | w32 _ | w64 _ | obj _ => simp [Rep.isFieldNat] at hrxFn
          subst hvlEq
          simp only [evalBinOp, Except.ok.injEq] at hsub
          rw [← hsub, ← Nat.cast_sub hpos]
          exact ⟨.lit (.nat (n - 1)), ⟨rfl, hnLim⟩,
            .nat (Nat.lt_min.mpr ⟨by omega, by omega⟩), Heap.Extends.refl _⟩)
        (fun _ ⟨heq, _⟩ => heq ▸ hTarget)
    subst hv'Eq
    refine ⟨hnLim, htvr', ext', fun w hloc => ?_⟩
    obtain ⟨v0, hρ0, htvr0⟩ := henv.rel x nx rx w hlook hloc
    rw [hρx, Option.some.injEq] at hρ0; subst hρ0
    have hwEq : w = .field (n : F) := by
      cases htvr0 with
      | nat _ | w8 _ | w16 _ => rfl
      | w32 _ | w64 _ | obj _ => simp [Rep.isFieldNat] at hrxFn
    exact ⟨by omega, by rw [hwEq, Nat.sub_add_cancel hpos]⟩
  cases hl : offs.lookup x with
  | none =>
    simp only [hl] at hsd
    obtain ⟨e1, s1, hco, hsd⟩ := tBind_step_inv hsd
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hsd
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hsd
    obtain ⟨hnLim, htvr', ext', hwNx⟩ := hnx hco ev
    refine ⟨hnLim, htvr', ext', fun baseNm d ho => ?_⟩
    cases target <;> simp at ho
    obtain ⟨rfl, rfl⟩ := ho
    exact ⟨Or.inl rfl, hwNx⟩
  | some bd =>
    rcases bd with ⟨base0, d0⟩
    simp only [hl] at hsd
    by_cases hlt : d0 < 256
    · simp only [hlt, ↓reduceIte] at hsd
      obtain ⟨e1, s1, hco, hsd⟩ := tBind_step_inv hsd
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hsd
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hsd
      obtain ⟨n', hρ', hnLim, hbase⟩ := hoffs x base0 d0 hl
      rw [hρx, Option.some.injEq] at hρ'; cases hρ'
      have hnFb : n < rx.fieldBound := hfbOfLim hnLim
      obtain ⟨v', hv'Eq, htvr', ext'⟩ :=
        eval_coerceE fc lw hwf hkeys hnd hdatas hco rfl htCore hdem ev
          (Q := fun v => v = .lit (.nat (n - 1)))
          (fun w0 hm evSub => by
            simp only [subE, vE, litE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evSub
            obtain ⟨vl, vr, _, evL, evR, hsub⟩ := evalExprN_binary_inv evSub
            obtain ⟨hloc, rfl⟩ := evalExprN_var_inv evL
            obtain ⟨rfl, rfl⟩ := evalExprN_literal_inv evR
            obtain ⟨hndLt, rfl⟩ := hbase vl hloc
            simp only [evalBinOp, Except.ok.injEq] at hsub
            rw [← hsub]
            have hle : d0 + 1 ≤ n + d0 := by omega
            rw [← Nat.cast_sub hle]
            have hsubEq : n + d0 - (d0 + 1) = n - 1 := by omega
            rw [hsubEq]
            exact ⟨.lit (.nat (n - 1)), rfl, .nat (Nat.lt_min.mpr ⟨by omega, by omega⟩), Heap.Extends.refl _⟩)
          (fun _ heq => heq ▸ hTarget)
      subst hv'Eq
      refine ⟨hnLim, htvr', ext', fun baseNm d ho => ?_⟩
      cases target <;> simp at ho
      obtain ⟨rfl, rfl⟩ := ho
      refine ⟨Or.inr (List.mem_map.mpr ⟨(x, (base0, d0)), mem_of_lookup_eq_some hl, rfl⟩), fun w hloc => ?_⟩
      obtain ⟨hndLt, hwEq⟩ := hbase w hloc
      have haddEq : n - 1 + (d0 + 1) = n + d0 := by omega
      exact ⟨by omega, by rw [haddEq]; exact hwEq⟩
    · simp only [hlt, ↓reduceIte] at hsd
      obtain ⟨e1, s1, hco, hsd⟩ := tBind_step_inv hsd
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hsd
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hsd
      obtain ⟨hnLim, htvr', ext', hwNx⟩ := hnx hco ev
      refine ⟨hnLim, htvr', ext', fun baseNm d ho => ?_⟩
      cases target <;> simp at ho
      obtain ⟨rfl, rfl⟩ := ho
      exact ⟨Or.inl rfl, hwNx⟩

/-- A Fir RHS contains no word primitive. -/
def noWordRhs : Rhs → Bool
  | .prim op _ => !op.isWord
  | _ => true

/-- Backward simulation of `TypedLower.tRhsE` for non-call right-hand sides (`.arg`, `.ctor`,
`.proj`, `.prim`), plus `OffsRel` witness for `xOff?`. -/
theorem eval_tRhsE_noncall {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld P cert sched lp world)
    (hwf : cert.WF) (hkeys : (P.ctors.map (·.key)).Nodup) (hnd : (objCtorNames P).Nodup)
    (hdatas : datasNatCoreReps P cert (scanFeatures P) = true)
    {dDepth : Nat} {fsh : FunShapes} {vm : TVarMap} {nz : List Var} {offs : OffMap}
    {rhs : Rhs} {σ : Shape}
    {st st' : TState} {res : Lower.Expr} {xOff? : Option (String × Nat)}
    {ρ : Env} {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F}
    (hnoW : noWordRhs rhs = true)
    (hRhsOk : Fir.Shape.RhsOk P cert fsh rhs σ)
    (hEnvOk : Fir.Shape.EnvOk cert dummyEnc fsh ρ)
    (hvmCore : ∀ p ∈ vm, isNatCoreRep p.2.2 = true)
    (hlocVm : AllLocalLt st.nextLocal (vm.map fun p => p.2.1))
    (htCore : isNatCoreRep (repOf P cert (scanFeatures P) σ) = true)
    (hrhs : tRhsE { P, cert, feat := scanFeatures P, sched } vm nz offs rhs
      (repOf P cert (scanFeatures P) σ) st = .ok ((res, xOff?), st'))
    (hdem : DemandLe st'.demand lp.demand)
    (henv : TEnvRel P cert (scanFeatures P) h fsh vm ρ locals)
    (hnz : NzRel ρ nz)
    (hoffs : OffsRel ρ locals offs)
    (hnotCall : ∀ f as, rhs ≠ .call f as)
    (ev : EvalExprN world dDepth [] locals (qualifyExprF F res) h r h') :
    ∃ v, evalRhs P ρ rhs = .ok v ∧
      Fir.Shape.ValOk cert dummyEnc σ v ∧
      TVR P cert (scanFeatures P) h' (repOf P cert (scanFeatures P) σ) v r ∧
      Heap.Extends h h' ∧
      (∀ baseNm d, xOff? = some (baseNm, d) →
        (baseNm ∈ vm.map (fun p => p.2.1) ∨ baseNm ∈ offs.map (fun p => p.2.1)) ∧
        ∃ n, v = .lit (.nat n) ∧ n < natLimit ∧
          ∀ w, locals.find? (·.1 == baseNm) = some (baseNm, w) →
            n + d < natLimit ∧ w = .field ((n + d : Nat) : F)) := by
  set cx : TCx := { P, cert, feat := scanFeatures P, sched }
  set target := repOf P cert (scanFeatures P) σ
  have hTargetOfRhs : ∀ v, evalRhs P ρ rhs = .ok v → CoerceTargetOk P cert (scanFeatures P) target v :=
    fun v hv => CoerceTargetOk.of_valOk (Fir.Proof.Shape.rhsSound hwf hEnvOk hRhsOk hv)
  cases rhs with
  | call f as => exact False.elim (hnotCall f as rfl)
  | arg a =>
    unfold tRhsE at hrhs
    obtain ⟨e1, s1, ha, hrhs⟩ := tBind_step_inv hrhs
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrhs
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrhs
    obtain ⟨v, haEv, htvr, ext⟩ :=
      eval_tArgE fc lw hwf hkeys hnd hdatas ha hvmCore htCore hdem henv ev
        (fun v hv => hTargetOfRhs v (by simp [evalRhs, hv, Sem.Result.ofOption]))
    have hEval : evalRhs P ρ (.arg a) = .ok v := by simp [evalRhs, haEv, Sem.Result.ofOption]
    refine ⟨v, hEval, Fir.Proof.Shape.rhsSound hwf hEnvOk hRhsOk hEval, htvr, ext, fun baseNm d ho => ?_⟩
    cases a with
    | lit _ | erased => simp at ho
    | var x =>
      cases htg : target with
      | nat b =>
        simp only [htg] at ho
        obtain ⟨n, hρx, hn, hbase⟩ := hoffs x baseNm d ho
        simp only [Arg.eval] at haEv
        rw [hρx, Option.some.injEq] at haEv; subst haEv
        exact ⟨Or.inr (List.mem_map.mpr ⟨(x, (baseNm, d)), mem_of_lookup_eq_some ho, rfl⟩),
          n, rfl, hn, hbase⟩
      | irr | w8 | w16 | w32 | w64 | «enum» _ | data _ | obj => simp [htg] at ho
  | ctor c as =>
    unfold tRhsE at hrhs
    cases hce : cx.ctorEntry? c.key with
    | none => simp only [hce] at hrhs; exact False.elim (tLift_throw_elim hrhs (fun _ _ => rfl))
    | some ie =>
      rcases ie with ⟨idx, entry⟩
      simp only [hce] at hrhs
      by_cases har : (as.length == entry.arity && c.arity == entry.arity) = true
      · simp only [har, ↓reduceIte] at hrhs
        simp only [Bool.and_eq_true, beq_iff_eq] at har
        obtain ⟨hasLen, hcAr⟩ := har
        obtain ⟨hget, hkey⟩ := ctorEntry?_sound hce
        cases htg : target with
        | «enum» ind =>
          simp only [htg, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at hrhs
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrhs
          have ⟨hσEq, _⟩ := repOf_eq_enum_inv htg
          subst hσEq
          obtain ⟨ks, rfl, hE, hcMem⟩ := rhsOk_ctor_enum_inv hRhsOk
          simp only [qualifyExprF, qualifyExpr, qualifyName_enumName, Option.map_some,
            Aiur.Generic.Expr.map, List.map_nil] at ev
          obtain ⟨ws, hargs, rfl⟩ := evalExprN_construct_inv ev
          cases hargs
          have har0 : entry.arity = 0 := by simpa using hasLen.symm
          have hEval : evalRhs P ρ (.ctor c []) = .ok (.ctor c []) := by
            simp [evalRhs, evalArgs, hcAr, har0]
          refine ⟨.ctor c [], hEval, Fir.Proof.Shape.rhsSound hwf hEnvOk hRhsOk hEval, ?_,
            Heap.Extends.refl _, fun _ _ ho => by cases ho⟩
          rw [hkey]
          exact .enumVal hE hcMem hget hkey har0
        | data d =>
          simp only [htg] at hrhs
          cases hD : cx.cert.data? d with
          | none =>
            simp only [hD] at hrhs
            obtain ⟨_, _, htr, _⟩ := tBind_step_inv hrhs
            exact False.elim (tLift_throw_elim htr (fun _ _ => rfl))
          | some D =>
            simp only [hD] at hrhs
            cases hfind : D.ctors.find? (·.1 == c.key) with
            | none =>
              simp only [hfind] at hrhs
              obtain ⟨_, _, htr, _⟩ := tBind_step_inv hrhs
              exact False.elim (tLift_throw_elim htr (fun _ _ => rfl))
            | some kfl =>
              rcases kfl with ⟨k', fl⟩
              simp only [hfind] at hrhs
              obtain ⟨fes, sF, hmap, hrhs⟩ := tBind_step_inv hrhs
              simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
                Except.ok.injEq, Prod.mk.injEq] at hrhs
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrhs
              have ⟨hσEq, _⟩ := repOf_eq_data_inv htg
              subst hσEq
              obtain ⟨D', fl', hD', hcMem', hargsOk⟩ := rhsOk_ctor_data_inv hRhsOk
              rw [hD, Option.some.injEq] at hD'; subst hD'
              have hk'Eq : k' = c.key := beq_iff_eq.mp (by simpa using List.find?_some hfind)
              have hflMem : (c.key, fl) ∈ D.ctors := hk'Eq ▸ List.mem_of_find?_eq_some hfind
              have hflEq : fl' = fl := hwf d D hD c.key fl' fl hcMem' hflMem
              rcases hflEq.symm with rfl
              simp only [qualifyExprF, qualifyExpr, qualifyName_dataName, Option.map_some,
                Aiur.Generic.Expr.map, List.map_map] at ev
              obtain ⟨ws, hargsEv, rfl⟩ := evalExprN_construct_inv ev
              have hfieldEv :
                  ∀ (as' : List Arg) (fl0 : List Shape) (sA sB : TState) (es' : List Lower.Expr)
                    (hA hB : Heap F) (ws' : List (SourceValue F)),
                    (∀ sh ∈ fl0, sh ∈ fl) →
                    Fir.Shape.ArgsOk fsh as' fl0 →
                    ((as'.zip fl0).mapM (m := TLowerM) fun (a0, sh) => do
                      let fr := cx.rep sh
                      let ae ← tArgE cx vm a0 fr
                      pure (if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.store ae else ae)) sA =
                      .ok (es', sB) →
                    DemandLe sB.demand lp.demand →
                    TEnvRel P cert (scanFeatures P) hA fsh vm ρ locals →
                    EvalArgsN world dDepth [] locals (es'.map (qualifyExprF F)) hA ws' hB →
                    ∃ vs', evalArgs ρ as' = some vs' ∧
                      TVRDataFields P cert (scanFeatures P) hB d fl0 vs' ws' ∧ Heap.Extends hA hB := by
                intro as'; induction as' with
                | nil =>
                  intro fl0 sA sB es' hA hB ws' _ haOk hm0 _ _ evA
                  cases haOk
                  simp only [List.zip_nil_left, List.mapM, List.mapM.loop, pure, StateT.pure,
                    Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm0
                  obtain ⟨rfl, rfl⟩ := hm0
                  cases evA
                  exact ⟨[], rfl, .nil, Heap.Extends.refl _⟩
                | cons a0 at_ iha =>
                  intro fl0 sA sB es' hA hB ws' hsub haOk hm0 hdemB henvA evA
                  cases haOk with | @cons _ sh _ sht ha1 haRest =>
                  simp only [List.zip_cons_cons, List.mapM_cons] at hm0
                  obtain ⟨fe1, sMid, hfe1, hm0⟩ := tBind_step_inv hm0
                  obtain ⟨fet, sEnd, hfet, hm0⟩ := tBind_step_inv hm0
                  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm0
                  obtain ⟨rfl, rfl⟩ := hm0
                  obtain ⟨ae, sMid', hae, hfe1⟩ := tBind_step_inv hfe1
                  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfe1
                  obtain ⟨rfl, rfl⟩ := hfe1
                  have hleRest : TStateLe sMid' sEnd := by
                    have aux : ∀ (prs : List (Arg × Shape)) (x0 x1 : TState) (es0 : List Lower.Expr),
                        (prs.mapM (m := TLowerM) fun (a1, sh1) => do
                          let fr := cx.rep sh1
                          let ae1 ← tArgE cx vm a1 fr
                          pure (if dataFieldNeedsPtr cx.P cx.cert cx.feat d fr then Aiur.Generic.Expr.store ae1 else ae1)) x0 =
                          .ok (es0, x1) → TStateLe x0 x1 := by
                      intro prs; induction prs with
                      | nil =>
                        intro x0 x1 es0 hm'; simp only [List.mapM, List.mapM.loop, pure, StateT.pure,
                          Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm'
                        obtain ⟨_, rfl⟩ := hm'; exact TStateLe.refl _
                      | cons p0 pt0 ihp0 =>
                        intro x0 x1 es0 hm'; rw [List.mapM_cons] at hm'
                        obtain ⟨_, xa, hxa, hm'⟩ := tBind_step_inv hm'
                        obtain ⟨_, xb, hxb, hm'⟩ := tBind_step_inv hm'
                        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm'
                        obtain ⟨_, rfl⟩ := hm'
                        obtain ⟨_, xa', hae', hxa⟩ := tBind_step_inv hxa
                        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hxa
                        obtain ⟨_, rfl⟩ := hxa
                        exact (tArgE_spec hae').1.trans (ihp0 xa' xb _ hxb)
                    exact aux _ sMid' sEnd fet hfet
                  simp only [List.map_cons] at evA
                  cases evA with | cons ev1 evRest =>
                  rename_i w1 hMid wsRest
                  have hcoreSh : isNatCoreRep (cx.rep sh) = true :=
                    datasNatCoreReps_field hdatas hD hflMem (hsub sh List.mem_cons_self)
                  cases hp : dataFieldNeedsPtr P cert (scanFeatures P) d (repOf P cert (scanFeatures P) sh) with
                  | false =>
                    dsimp only [cx, TCx.rep] at ev1
                    simp only [hp, Bool.false_eq_true, ↓reduceIte] at ev1
                    obtain ⟨v1, hv1Ev, htvr1, ext1⟩ :=
                      eval_tArgE fc lw hwf hkeys hnd hdatas hae hvmCore hcoreSh
                        (hleRest.demand.trans hdemB) henvA ev1
                        (fun v hv => CoerceTargetOk.of_valOk (Fir.Proof.Shape.argSound hEnvOk ha1 hv))
                    obtain ⟨vsRest, hvsRest, hdfRest, extRest⟩ :=
                      iha sht sMid' sEnd fet hMid hB wsRest
                        (fun s' hs' => hsub s' (List.mem_cons_of_mem _ hs'))
                        haRest hfet hdemB (henvA.extend ext1) evRest
                    refine ⟨v1 :: vsRest, ?_, .consInline hp (htvr1.extend extRest) hdfRest, ext1.trans extRest⟩
                    rw [Fir.evalArgs_cons, hv1Ev, hvsRest]; rfl
                  | true =>
                    dsimp only [cx, TCx.rep] at ev1
                    simp only [hp, ↓reduceIte, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev1
                    obtain ⟨wTyped, hPre, evTy, rfl, rfl⟩ := evalExprN_store_inv ev1
                    obtain ⟨v1, hv1Ev, htvr1, ext1⟩ :=
                      eval_tArgE fc lw hwf hkeys hnd hdatas hae hvmCore hcoreSh
                        (hleRest.demand.trans hdemB) henvA evTy
                        (fun v hv => CoerceTargetOk.of_valOk (Fir.Proof.Shape.argSound hEnvOk ha1 hv))
                    have extSt : Heap.Extends hA (hPre ++ [wTyped]) :=
                      ext1.trans (Heap.Extends.append_right hPre [wTyped])
                    obtain ⟨vsRest, hvsRest, hdfRest, extRest⟩ :=
                      iha sht sMid' sEnd fet (hPre ++ [wTyped]) hB wsRest
                        (fun s' hs' => hsub s' (List.mem_cons_of_mem _ hs'))
                        haRest hfet hdemB (henvA.extend extSt) evRest
                    have hatAddr : hB[hPre.length]? = some wTyped := extRest.getElem?_eq (by simp)
                    refine ⟨v1 :: vsRest, ?_,
                      .consPtr hp hatAddr (htvr1.extend ((Heap.Extends.append_right hPre [wTyped]).trans extRest)) hdfRest,
                      extSt.trans extRest⟩
                    rw [Fir.evalArgs_cons, hv1Ev, hvsRest]; rfl
              obtain ⟨vs, hvsEv, hdf, ext⟩ :=
                hfieldEv as fl st sF fes h h' ws (fun _ hx => hx) hargsOk hmap hdem henv hargsEv
              have ⟨hvsFl, _⟩ := hdf.length_eq
              have hvsLen : vs.length = as.length := by
                have auxLen : ∀ (as0 : List Arg) (vs0 : List Fir.Val), evalArgs ρ as0 = some vs0 → vs0.length = as0.length := by
                  intro as0; induction as0 with
                  | nil => intro vs0 h0; cases h0; rfl
                  | cons a0 at0 iha0 =>
                    intro vs0 h0; simp only [Fir.evalArgs] at h0
                    cases ha0 : a0.eval ρ <;> cases htl : evalArgs ρ at0 <;> simp [ha0, htl] at h0
                    subst h0; simp [iha0 _ htl]
                exact auxLen as vs hvsEv
              have hEval : evalRhs P ρ (.ctor c as) = .ok (.ctor c vs) := by
                simp [evalRhs, hvsEv, hvsLen, hasLen, hcAr]
              refine ⟨.ctor c vs, hEval, Fir.Proof.Shape.rhsSound hwf hEnvOk hRhsOk hEval, ?_, ext,
                fun _ _ ho => by cases ho⟩
              rw [hkey]
              exact .dataVal hD hflMem hget hkey (by omega) (by omega) hdf
        | irr | nat _ | w8 | w16 | w32 | w64 | obj =>
          simp only [htg] at hrhs
          obtain ⟨sM, hleM, _, hrhs⟩ := tMark_step_inv hrhs (fun _ _ => rfl)
            (fun _ => by constructor <;> first | exact id | (intro _; rfl))
          obtain ⟨argEs, sA, hmap, hrhs⟩ := tBind_step_inv hrhs
          obtain ⟨e1, sCo, hco, hrhs⟩ := tBind_step_inv hrhs
          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrhs
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrhs
          have hdemSA : DemandLe sA.demand lp.demand := (coerceE_spec hco).1.demand.trans hdem
          have hObjEv :
              ∀ (as' : List Arg) (s0 s1 : TState) (es' : List Lower.Expr)
                (hA hB : Heap F) (ps : List (SourceValue F)),
                (as'.mapM (m := TLowerM) fun a0 => do
                  pure (Aiur.Generic.Expr.store (← tArgE cx vm a0 .obj))) s0 = .ok (es', s1) →
                DemandLe s1.demand lp.demand →
                TEnvRel P cert (scanFeatures P) hA fsh vm ρ locals →
                EvalArgsN world dDepth [] locals (es'.map (qualifyExprF F)) hA ps hB →
                ∃ vs', evalArgs ρ as' = some vs' ∧
                  VRs P objQName bytesQName hB vs' ps ∧ Heap.Extends hA hB := by
            intro as'; induction as' with
            | nil =>
              intro s0 s1 es' hA hB ps hm0 _ _ evA
              simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
                Except.ok.injEq, Prod.mk.injEq] at hm0
              obtain ⟨rfl, rfl⟩ := hm0; cases evA; exact ⟨[], rfl, .nil, Heap.Extends.refl _⟩
            | cons a0 at_ iha =>
              intro s0 s1 es' hA hB ps hm0 hdem1 henvA evA
              rw [List.mapM_cons] at hm0
              obtain ⟨e1, sMid, h1, hm0⟩ := tBind_step_inv hm0
              obtain ⟨et, sEnd, h2, hm0⟩ := tBind_step_inv hm0
              simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm0
              obtain ⟨rfl, rfl⟩ := hm0
              obtain ⟨ae, sMid', hae, h1⟩ := tBind_step_inv h1
              simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1
              obtain ⟨rfl, rfl⟩ := h1
              have hleRest : TStateLe sMid' sEnd := by
                have aux : ∀ (l0 : List Arg) (x0 x1 : TState) (es0 : List Lower.Expr),
                    (l0.mapM (m := TLowerM) fun a1 => do
                      pure (Aiur.Generic.Expr.store (← tArgE cx vm a1 .obj))) x0 = .ok (es0, x1) →
                    TStateLe x0 x1 := by
                  intro l0; induction l0 with
                  | nil =>
                    intro x0 x1 es0 hm'; simp only [List.mapM, List.mapM.loop, pure, StateT.pure,
                      Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm'
                    obtain ⟨_, rfl⟩ := hm'; exact TStateLe.refl _
                  | cons a1 at1 ih1 =>
                    intro x0 x1 es0 hm'; rw [List.mapM_cons] at hm'
                    obtain ⟨_, xa, hxa, hm'⟩ := tBind_step_inv hm'
                    obtain ⟨_, xb, hxb, hm'⟩ := tBind_step_inv hm'
                    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm'
                    obtain ⟨_, rfl⟩ := hm'
                    obtain ⟨_, xa', hae', hxa⟩ := tBind_step_inv hxa
                    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hxa
                    obtain ⟨_, rfl⟩ := hxa
                    exact (tArgE_spec hae').1.trans (ih1 xa' xb _ hxb)
                exact aux at_ sMid' sEnd et h2
              simp only [List.map_cons] at evA
              cases evA with | cons evSt evRest =>
              rename_i p1 hMid psRest
              simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evSt
              obtain ⟨wObj, hPre, evObj, rfl, rfl⟩ := evalExprN_store_inv evSt
              obtain ⟨v1, hv1Ev, htvr1, ext1⟩ :=
                eval_tArgE fc lw hwf hkeys hnd hdatas hae hvmCore rfl
                  (hleRest.demand.trans hdem1) henvA evObj (fun _ _ => Or.inl rfl)
              have hvr1 := TVR_obj_inv htvr1
              have extSt : Heap.Extends hA (hPre ++ [wObj]) :=
                ext1.trans (Heap.Extends.append_right hPre [wObj])
              obtain ⟨vsRest, hvsRest, hvrsRest, extRest⟩ :=
                iha sMid' sEnd et (hPre ++ [wObj]) hB psRest h2 hdem1 (henvA.extend extSt) evRest
              have htype : wObj.type = .enum objQName := hvr1.type_eq
              have hatAddr : hB[hPre.length]? = some wObj := extRest.getElem?_eq (by simp)
              refine ⟨v1 :: vsRest, ?_, ?_, extSt.trans extRest⟩
              · rw [Fir.evalArgs_cons, hv1Ev, hvsRest]; rfl
              · rw [htype]
                exact .cons hatAddr (hvr1.extend ((Heap.Extends.append_right hPre [wObj]).trans extRest)) hvrsRest
          obtain ⟨v, hvEval, htvr, ext⟩ :=
            eval_coerceE fc lw hwf hkeys hnd hdatas hco rfl (htg ▸ htCore) hdem ev
              (Q := fun v => evalRhs P ρ (.ctor c as) = .ok v)
              (fun w0 hm evMk => by
                simp only [mk, qualifyExprF, qualifyExpr, qualifyName_obj, Option.map_some,
                  Aiur.Generic.Expr.map, List.map_map] at evMk
                obtain ⟨ps, hargsEv, rfl⟩ := evalExprN_construct_inv evMk
                obtain ⟨vs, hvsEv, hvrs, ext1⟩ := hObjEv as sM sA argEs h hm ps hmap hdemSA henv hargsEv
                have hvsLen : vs.length = as.length := by
                  have auxLen : ∀ (as0 : List Arg) (vs0 : List Fir.Val), evalArgs ρ as0 = some vs0 → vs0.length = as0.length := by
                    intro as0; induction as0 with
                    | nil => intro vs0 h0; cases h0; rfl
                    | cons a0 at0 iha0 =>
                      intro vs0 h0; simp only [Fir.evalArgs] at h0
                      cases ha0 : a0.eval ρ <;> cases htl : evalArgs ρ at0 <;> simp [ha0, htl] at h0
                      subst h0; simp [iha0 _ htl]
                  exact auxLen as vs hvsEv
                have hEval : evalRhs P ρ (.ctor c as) = .ok (.ctor c vs) := by
                  simp [evalRhs, hvsEv, hvsLen, hasLen, hcAr]
                rw [hkey]
                exact ⟨.ctor c vs, hEval, .obj (.ctor hget hkey (by rw [hvsLen, hasLen]) hvrs), ext1⟩)
              (fun v hv => htg ▸ hTargetOfRhs v hv)
          exact ⟨v, hvEval, Fir.Proof.Shape.rhsSound hwf hEnvOk hRhsOk hvEval, htvr, ext,
            fun _ _ ho => by cases ho⟩
      · simp only [har, Bool.false_eq_true, ↓reduceIte] at hrhs
        obtain ⟨_, _, h1, _⟩ := tBind_step_inv hrhs
        exact False.elim (tLift_throw_elim h1 (fun _ _ => rfl))
  | proj x c i =>
    unfold tRhsE at hrhs
    cases hlook : vm.lookup x with
    | none => simp only [hlook] at hrhs; exact False.elim (tLift_throw_elim hrhs (fun _ _ => rfl))
    | some nr =>
      rcases nr with ⟨nx, rx⟩
      simp only [hlook] at hrhs
      have hrxCore : isNatCoreRep rx = true := hvmCore (x, nx, rx) (mem_of_lookup_eq_some hlook)
      cases rx with
      | w32 | w64 => simp [isNatCoreRep] at hrxCore
      | irr | «enum» _ =>
        obtain ⟨tr, s1, htr, hrhs⟩ := tBind_step_inv hrhs
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrhs
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrhs
        have htrp := (tTrapE_ok_inv htr (fun _ _ _ => rfl) (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl)) (fun _ _ => rfl) (fun _ _ => rfl)).1
        exact False.elim (evalExprN_of_isTrapExpr htrp ev)
      | nat b | w8 | w16 =>
        by_cases hsc : (cx.P.known.natSucc == some c && i == 0) = true
        · simp only [hsc, ↓reduceIte] at hrhs
          simp only [Bool.and_eq_true, beq_iff_eq] at hsc
          obtain ⟨hns, rfl⟩ := hsc
          dsimp only [cx] at hns
          by_cases hnzx : nz.contains x = true
          · simp only [hnzx, ↓reduceIte] at hrhs
            obtain ⟨n, hρx, hpos⟩ := hnz x (List.contains_iff_mem.mp hnzx)
            have hEval : evalRhs P ρ (.proj x c 0) = .ok (.lit (.nat (n - 1))) := by
              cases n with
              | zero => omega
              | succ m =>
                simp [evalRhs, hρx, Fir.Val.asCtor, hns, Sem.Result.ofOption]
            obtain ⟨hnLim, htvr, ext, hoffW⟩ :=
              eval_stepDownNat_poly fc lw hwf hkeys hnd hdatas hrhs (fun _ _ _ _ _ _ _ => rfl)
                hlook rfl hEnvOk htCore hdem henv hoffs hρx hpos ev
                (hTargetOfRhs _ hEval)
            refine ⟨.lit (.nat (n - 1)), hEval, Fir.Proof.Shape.rhsSound hwf hEnvOk hRhsOk hEval,
              htvr, ext, fun baseNm d ho => ?_⟩
            obtain ⟨hmemBase, hbase⟩ := hoffW baseNm d ho
            refine ⟨?_, n - 1, rfl, by omega, hbase⟩
            rcases hmemBase with rfl | hmemO
            · exact Or.inl (List.mem_map.mpr ⟨(x, baseNm, _), mem_of_lookup_eq_some hlook, rfl⟩)
            · exact Or.inr hmemO
          · simp only [hnzx, Bool.false_eq_true, ↓reduceIte] at hrhs
            obtain ⟨tr, s1, htr, hrhs⟩ := tBind_step_inv hrhs
            obtain ⟨e1, s2, hco, hrhs⟩ := tBind_step_inv hrhs
            simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrhs
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrhs
            have htrp := (tTrapE_ok_inv htr (fun _ _ _ => rfl) (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl)) (fun _ _ => rfl) (fun _ _ => rfl)).1
            obtain ⟨v, hvEval, htvr, ext⟩ :=
              eval_coerceE fc lw hwf hkeys hnd hdatas hco rfl htCore hdem ev
                (Q := fun v => evalRhs P ρ (.proj x c 0) = .ok v)
                (fun w0 hm evMatch => by
                  obtain ⟨vx, hm1, evV, hbr⟩ := evalExprN_match_lit_wild_inv evMatch
                  simp only [vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evV
                  obtain ⟨hloc, rfl⟩ := evalExprN_var_inv evV
                  obtain ⟨vxFir, hρx, htvrX⟩ := henv.rel x nx _ vx hlook hloc
                  cases htvrX
                  rename_i n hlt
                  have hnLim : n < natLimit := by
                    first | exact (Nat.lt_min.mp hlt).2 | exact lt_trans hlt (by decide)
                  rcases hbr with ⟨_, evTr⟩ | ⟨hne0, evSub⟩
                  · exact False.elim (evalExprN_of_isTrapExpr htrp evTr)
                  · have hpos : 0 < n := by
                      by_contra hle; have hn0 : n = 0 := by omega
                      exact hne0 (by simp [hn0])
                    simp only [subE, vE, litE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evSub
                    obtain ⟨vl, vr, _, evL, evR, hsub⟩ := evalExprN_binary_inv evSub
                    obtain ⟨hll, rfl⟩ := evalExprN_var_inv evL
                    rw [hloc, Option.some.injEq, Prod.mk.injEq] at hll
                    obtain ⟨_, rfl⟩ := hll
                    obtain ⟨rfl, rfl⟩ := evalExprN_literal_inv evR
                    simp only [evalBinOp, Except.ok.injEq] at hsub
                    rw [← hsub, ← Nat.cast_sub hpos]
                    have hEval : evalRhs P ρ (.proj x c 0) = .ok (.lit (.nat (n - 1))) := by
                      cases n with
                      | zero => omega
                      | succ m => simp [evalRhs, hρx, Fir.Val.asCtor, hns, Sem.Result.ofOption]
                    exact ⟨.lit (.nat (n - 1)), hEval,
                      .nat (Nat.lt_min.mpr ⟨by dsimp only [Rep.fieldBound]; omega, by omega⟩), Heap.Extends.refl _⟩)
                hTargetOfRhs
            exact ⟨v, hvEval, Fir.Proof.Shape.rhsSound hwf hEnvOk hRhsOk hvEval, htvr, ext,
              fun _ _ ho => by cases ho⟩
        · simp only [hsc, Bool.false_eq_true, ↓reduceIte] at hrhs
          obtain ⟨tr, s1, htr, hrhs⟩ := tBind_step_inv hrhs
          simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrhs
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrhs
          have htrp := (tTrapE_ok_inv htr (fun _ _ _ => rfl) (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl)) (fun _ _ => rfl) (fun _ _ => rfl)).1
          exact False.elim (evalExprN_of_isTrapExpr htrp ev)
      | data d =>
        cases hD : cx.cert.data? d with
        | none => simp only [hD] at hrhs; exact False.elim (tLift_throw_elim hrhs (fun _ _ => rfl))
        | some D =>
          simp only [hD] at hrhs
          cases hfind : D.ctors.find? (·.1 == c) with
          | none =>
            simp only [hfind] at hrhs
            obtain ⟨tr, s1, htr, hrhs⟩ := tBind_step_inv hrhs
            simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrhs
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrhs
            have htrp := (tTrapE_ok_inv htr (fun _ _ _ => rfl) (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl)) (fun _ _ => rfl) (fun _ _ => rfl)).1
            exact False.elim (evalExprN_of_isTrapExpr htrp ev)
          | some kfl =>
            rcases kfl with ⟨k', fl⟩
            simp only [hfind] at hrhs
            cases hce : cx.ctorEntry? c with
            | none =>
              simp only [hce] at hrhs
              obtain ⟨tr, s1, htr, hrhs⟩ := tBind_step_inv hrhs
              simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrhs
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrhs
              have htrp := (tTrapE_ok_inv htr (fun _ _ _ => rfl) (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl)) (fun _ _ => rfl) (fun _ _ => rfl)).1
              exact False.elim (evalExprN_of_isTrapExpr htrp ev)
            | some ie =>
              rcases ie with ⟨idx, entry⟩
              cases hfli : fl[i]? with
              | none =>
                simp only [hce, hfli] at hrhs
                obtain ⟨tr, s1, htr, hrhs⟩ := tBind_step_inv hrhs
                simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrhs
                obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrhs
                have htrp := (tTrapE_ok_inv htr (fun _ _ _ => rfl) (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl)) (fun _ _ => rfl) (fun _ _ => rfl)).1
                exact False.elim (evalExprN_of_isTrapExpr htrp ev)
              | some sh =>
                simp only [hce, hfli] at hrhs
                obtain ⟨q, sQ, hq, hrhs⟩ := tBind_step_inv hrhs
                obtain ⟨body, sB, hco, hrhs⟩ := tBind_step_inv hrhs
                simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrhs
                obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrhs
                simp only [matchE, vE, qualifyExprF, qualifyExpr, qualifyPat, qualifyTy,
                  qualifyName_dataName, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at ev
                obtain ⟨wx, hm, bs, armB, evX, hsel, evB⟩ := evalExprN_match_inv ev
                obtain ⟨hloc, rfl⟩ := evalExprN_var_inv evX
                obtain ⟨vxFir, hρx, htvrX⟩ := henv.rel x nx (.data d) wx hlook hloc
                obtain ⟨D', c', fl', idx', entry', fs, ws, hD', hc'Mem, hget', hkey', hflen, hfllen, hfields, rfl, rfl⟩ :=
                  TVR_data_inv htvrX
                rw [hD, Option.some.injEq] at hD'; subst hD'
                have hpatMap :
                    List.map (Aiur.Generic.Pattern.map Nat.cast)
                      (List.map qualifyPat
                        (List.map (fun j => if j = i then (Aiur.Generic.Pattern.bind q : Lower.Pat) else .wildcard)
                          (List.range entry.arity))) =
                    (List.range entry.arity).map fun j =>
                      if 0 + j = i then (Aiur.Generic.Pattern.bind q : Aiur.Generic.Pattern F) else .wildcard := by
                  rw [List.map_map, List.map_map]
                  apply List.map_congr_left
                  intro j _; simp only [Function.comp_def, Nat.zero_add]
                  split <;> simp [qualifyPat, Aiur.Generic.Pattern.map]
                simp only [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
                  constructorName, Ty.subst, Ty.toCore, Instance.symbol, List.map_nil,
                  List.isEmpty_nil, ↓reduceIte, hpatMap, List.length_map, List.length_range,
                  bne_self_eq_false, Bool.false_or, bind, Except.bind, pure, Except.pure] at hsel
                by_cases hcond : (ctorNameOf idx' c'.key != ctorNameOf idx entry.key || entry.arity != ws.length) = true
                · simp [hcond] at hsel
                · have hcf0 : (ctorNameOf idx' c'.key != ctorNameOf idx entry.key || entry.arity != ws.length) = false :=
                    Bool.eq_false_iff.mpr hcond
                  rw [hcf0] at hsel
                  simp only [Bool.false_eq_true, ↓reduceIte] at hsel
                  simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hcf0
                  obtain ⟨hnmEq, harEq⟩ := hcf0
                  obtain ⟨hget, hkey⟩ := ctorEntry?_sound hce
                  rw [← hkey'] at hnmEq
                  obtain ⟨rfl, hentryEq⟩ := ctorNameOf_inj_of_nodup hnd hget' hget hnmEq
                  subst hentryEq
                  have hk'Eq : k' = c := beq_iff_eq.mp (by simpa using List.find?_some hfind)
                  have hc'c : c'.key = c := hkey'.symm.trans hkey
                  have hflMem : (c, fl) ∈ D.ctors := hk'Eq ▸ List.mem_of_find?_eq_some hfind
                  have hflEq : fl' = fl := hwf d D hD c fl' fl (hc'c ▸ hc'Mem) hflMem
                  subst hflEq
                  rw [matchListWith_attach_eq_t, matchListWith_projPats_gen q entry'.arity 0 i ws harEq.symm] at hsel
                  have hiLt : i < entry'.arity := by
                    have := (List.getElem?_eq_some_iff.mp hfli).1; omega
                  obtain ⟨fi, wRaw, hfsi, hwsi, hfieldRel⟩ := hfields.getElem?_some hfli
                  have hcondI : (0 ≤ i ∧ i < 0 + entry'.arity) := ⟨Nat.zero_le _, by omega⟩
                  rw [ite_eq_left hcondI, Nat.sub_zero, hwsi] at hsel
                  simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hsel
                  obtain ⟨rfl, rfl⟩ := hsel
                  have hEval : evalRhs P ρ (.proj x c i) = .ok fi := by
                    simp [evalRhs, hρx, Fir.Val.asCtor, hc'c, hfsi, Sem.Result.ofOption]
                  have hcoreSh : isNatCoreRep (cx.rep sh) = true :=
                    datasNatCoreReps_field hdatas hD hflMem (List.mem_of_getElem? hfli)
                  obtain ⟨vOut, hvOutEq, htvrOut, extOut⟩ :=
                    eval_coerceE fc lw hwf hkeys hnd hdatas hco hcoreSh htCore hdem evB
                      (Q := fun v => v = fi)
                      (fun w0 hm0 evRaw => by
                        dsimp only [cx, TCx.rep] at evRaw
                        rcases hfieldRel with ⟨hnp, htvrF⟩ | ⟨hp, addr, wDeref, rfl, hatA, htvrF⟩
                        · simp only [hnp, Bool.false_eq_true, ↓reduceIte, vE, qualifyExprF,
                            qualifyExpr, Aiur.Generic.Expr.map] at evRaw
                          obtain ⟨hlq, rfl⟩ := evalExprN_var_inv evRaw
                          simp only [List.cons_append, List.nil_append, List.find?_cons,
                            beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hlq
                          obtain ⟨_, rfl⟩ := hlq
                          exact ⟨fi, rfl, htvrF, Heap.Extends.refl _⟩
                        · simp only [hp, ↓reduceIte, vE, qualifyExprF, qualifyExpr,
                            Aiur.Generic.Expr.map] at evRaw
                          obtain ⟨vp, evV, hload⟩ := evalExprN_load_inv evRaw
                          obtain ⟨hlq, rfl⟩ := evalExprN_var_inv evV
                          simp only [List.cons_append, List.nil_append, List.find?_cons,
                            beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hlq
                          obtain ⟨_, rfl⟩ := hlq
                          simp [loadValue, hatA] at hload
                          subst hload
                          exact ⟨fi, rfl, htvrF, Heap.Extends.refl _⟩)
                      (fun _ heq => heq ▸ hTargetOfRhs fi hEval)
                  rcases hvOutEq with rfl
                  exact ⟨vOut, hEval, Fir.Proof.Shape.rhsSound hwf hEnvOk hRhsOk hEval, htvrOut, extOut,
                    fun _ _ ho => by cases ho⟩
      | obj =>
        obtain ⟨s1, _, _, hrhs⟩ := tMark_step_inv hrhs (fun _ _ => rfl)
          (fun _ => by constructor <;> first | exact id | (intro _; rfl))
        obtain ⟨e1, s2, hco, hrhs⟩ := tBind_step_inv hrhs
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrhs
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrhs
        obtain ⟨v, hvEval, htvr, ext⟩ :=
          eval_coerceE fc lw hwf hkeys hnd hdatas hco rfl htCore hdem ev
            (Q := fun v => evalRhs P ρ (.proj x c i) = .ok v)
            (fun w0 hm evRaw => by
              have hlocEx : ∃ w, locals.find? (·.1 == nx) = some (nx, w) := by
                have aux : ∀ (arms : List (Lower.Pat × Lower.Expr)),
                    EvalExprN world dDepth [] locals
                      (qualifyExprF F (if arms.isEmpty then trapE "projection of a missing field" else matchE (vE nx) arms))
                      h w0 hm →
                    ∃ w, locals.find? (·.1 == nx) = some (nx, w) := by
                  intro arms evA
                  cases hEmp : arms.isEmpty with
                  | true =>
                    simp only [hEmp, ↓reduceIte] at evA
                    exact False.elim (evalExprN_of_isTrapExpr (by simp [isTrapExpr, trapE, seqE]) evA)
                  | false =>
                    simp only [hEmp, Bool.false_eq_true, ↓reduceIte, matchE, vE, qualifyExprF,
                      qualifyExpr, Aiur.Generic.Expr.map] at evA
                    obtain ⟨w, _, _, _, evX, _, _⟩ := evalExprN_match_inv evA
                    obtain ⟨hloc, _⟩ := evalExprN_var_inv evX
                    exact ⟨w, hloc⟩
                exact aux _ evRaw
              obtain ⟨wx, hloc⟩ := hlocEx
              obtain ⟨vxFir, hρx, htvrX⟩ := henv.rel x nx .obj wx hlook hloc
              have hvrX := TVR_obj_inv htvrX
              obtain ⟨v', hprojOk, hvr', ext'⟩ :=
                eval_projE fc.toFieldCompatible hnd hloc hvrX evRaw
              have hEval : evalRhs P ρ (.proj x c i) = .ok v' := by
                simp only [evalRhs, hρx]; exact hprojOk
              exact ⟨v', hEval, .obj hvr', ext'⟩)
            hTargetOfRhs
        exact ⟨v, hvEval, Fir.Proof.Shape.rhsSound hwf hEnvOk hRhsOk hvEval, htvr, ext,
          fun _ _ ho => by cases ho⟩
  | prim op as =>
    have hopNoW : op.isWord = false := by simpa [noWordRhs] using hnoW
    have hfallback :
        tPrimE cx vm op as target st = .ok (res, st') → xOff? = none →
        ∃ v, evalRhs P ρ (.prim op as) = .ok v ∧
          Fir.Shape.ValOk cert dummyEnc σ v ∧
          TVR P cert (scanFeatures P) h' target v r ∧
          Heap.Extends h h' ∧
          (∀ baseNm d, xOff? = some (baseNm, d) →
            (baseNm ∈ vm.map (fun p => p.2.1) ∨ baseNm ∈ offs.map (fun p => p.2.1)) ∧
            ∃ n, v = .lit (.nat n) ∧ n < natLimit ∧
              ∀ w, locals.find? (·.1 == baseNm) = some (baseNm, w) →
                n + d < natLimit ∧ w = .field ((n + d : Nat) : F)) := by
      intro hp hnone
      obtain ⟨v, hvEval, htvr, ext⟩ :=
        eval_tPrimE fc lw hwf hkeys hnd hdatas hopNoW hvmCore hlocVm htCore hp hdem henv ev hTargetOfRhs
      exact ⟨v, hvEval, Fir.Proof.Shape.rhsSound hwf hEnvOk hRhsOk hvEval, htvr, ext,
        fun _ _ ho => by rw [hnone] at ho; cases ho⟩
    -- Unfold `tRhsE` on `.prim op as` and handle countdown fast paths vs `tPrimE` fallback.
    unfold tRhsE at hrhs
    have hfallbackStep : ∀ {t : Rep}, target = t →
        (do pure (← tPrimE cx vm op as t, (none : Option (String × Nat)))) st = .ok ((res, xOff?), st') →
        ∃ v, evalRhs P ρ (.prim op as) = .ok v ∧
          Fir.Shape.ValOk cert dummyEnc σ v ∧
          TVR P cert (scanFeatures P) h' t v r ∧
          Heap.Extends h h' ∧
          (∀ baseNm d, xOff? = some (baseNm, d) →
            (baseNm ∈ vm.map (fun p => p.2.1) ∨ baseNm ∈ offs.map (fun p => p.2.1)) ∧
            ∃ n, v = .lit (.nat n) ∧ n < natLimit ∧
              ∀ w, locals.find? (·.1 == baseNm) = some (baseNm, w) →
                n + d < natLimit ∧ w = .field ((n + d : Nat) : F)) := by
      intro t ht hf
      obtain ⟨e1, s1, hp, hf⟩ := tBind_step_inv hf
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hf
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hf
      have hres := hfallback (ht ▸ hp) rfl
      exact ht ▸ hres
    have haddFast : ∀ (x : Var) (k b : Nat),
        target = .nat b →
        (∀ v, evalRhs P ρ (.prim .natAdd [Arg.var x, Arg.lit (.nat k)]) = .ok v →
          evalRhs P ρ (.prim op as) = .ok v) →
        (match offs.lookup x with
         | some (baseNm, d) =>
           if k ≤ d then
             if k == d then pure (vE baseNm, some (baseNm, 0))
             else pure (subE (vE baseNm) (litE (d - k)), some (baseNm, d - k))
           else do pure (← tPrimE cx vm op as (.nat b), none)
         | none => do pure (← tPrimE cx vm op as (.nat b), none)) st = .ok ((res, xOff?), st') →
        ∃ v, evalRhs P ρ (.prim op as) = .ok v ∧
          Fir.Shape.ValOk cert dummyEnc σ v ∧
          TVR P cert (scanFeatures P) h' (.nat b) v r ∧
          Heap.Extends h h' ∧
          (∀ baseNm d, xOff? = some (baseNm, d) →
            (baseNm ∈ vm.map (fun p => p.2.1) ∨ baseNm ∈ offs.map (fun p => p.2.1)) ∧
            ∃ n, v = .lit (.nat n) ∧ n < natLimit ∧
              ∀ w, locals.find? (·.1 == baseNm) = some (baseNm, w) →
                n + d < natLimit ∧ w = .field ((n + d : Nat) : F)) := by
      intro x k b htg hEqEval hmatch
      cases ho : offs.lookup x with
      | none => rw [ho] at hmatch; exact hfallbackStep htg hmatch
      | some bd =>
        rcases bd with ⟨baseNm, d⟩
        rw [ho] at hmatch
        by_cases hkd : k ≤ d
        · simp only [hkd, ↓reduceIte] at hmatch
          obtain ⟨n, hρx, hn, hbase⟩ := hoffs x baseNm d ho
          have hEvalAdd : evalRhs P ρ (.prim .natAdd [Arg.var x, Arg.lit (.nat k)]) = .ok (.lit (.nat (n + k))) := by
            simp [evalRhs, evalArgs, Arg.eval, hρx, primResult, natArgs]
          have hEval := hEqEval _ hEvalAdd
          have hmemBase : baseNm ∈ offs.map (fun p => p.2.1) :=
            List.mem_map.mpr ⟨(x, (baseNm, d)), mem_of_lookup_eq_some ho, rfl⟩
          by_cases hkdEq : (k == d) = true
          · simp only [hkdEq, ↓reduceIte, pure, StateT.pure, Except.pure, Except.ok.injEq,
              Prod.mk.injEq] at hmatch
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hmatch
            have hkeq : k = d := beq_iff_eq.mp hkdEq
            subst hkeq
            simp only [vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
            obtain ⟨hloc, rfl⟩ := evalExprN_var_inv ev
            obtain ⟨hnkLt, rfl⟩ := hbase r hloc
            have hbound : n + k < min b natLimit := (htg ▸ hTargetOfRhs _ hEval).nat_bound hnkLt
            refine ⟨.lit (.nat (n + k)), hEval, Fir.Proof.Shape.rhsSound hwf hEnvOk hRhsOk hEval,
              .nat hbound, Heap.Extends.refl _, fun bm d' ho' => ?_⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at ho'
            obtain ⟨rfl, rfl⟩ := ho'
            exact ⟨Or.inr hmemBase, n + k, rfl, hnkLt, fun w hw => by
              obtain ⟨hlt, hwEq⟩ := hbase w hw; exact ⟨by omega, by simpa using hwEq⟩⟩
          · simp only [hkdEq, Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, Except.pure,
              Except.ok.injEq, Prod.mk.injEq] at hmatch
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hmatch
            simp only [subE, vE, litE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
            obtain ⟨vl, vr, _, evL, evR, hsub⟩ := evalExprN_binary_inv ev
            obtain ⟨hloc, rfl⟩ := evalExprN_var_inv evL
            obtain ⟨rfl, rfl⟩ := evalExprN_literal_inv evR
            obtain ⟨hndLt, rfl⟩ := hbase vl hloc
            simp only [evalBinOp, Except.ok.injEq] at hsub
            have hleSub : d - k ≤ n + d := by omega
            have hsubN : n + d - (d - k) = n + k := by omega
            have hrEq : r = .field ((n + k : Nat) : F) := by
              rw [← hsub, ← Nat.cast_sub hleSub, hsubN]
            subst hrEq
            have hnkLt : n + k < natLimit := by omega
            have hbound : n + k < min b natLimit := (htg ▸ hTargetOfRhs _ hEval).nat_bound hnkLt
            refine ⟨.lit (.nat (n + k)), hEval, Fir.Proof.Shape.rhsSound hwf hEnvOk hRhsOk hEval,
              .nat hbound, Heap.Extends.refl _, fun bm d' ho' => ?_⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at ho'
            obtain ⟨rfl, rfl⟩ := ho'
            exact ⟨Or.inr hmemBase, n + k, rfl, hnkLt, fun w hw => by
              obtain ⟨hlt, hwEq⟩ := hbase w hw
              have hsum : n + k + (d - k) = n + d := by omega
              exact ⟨by omega, by rw [hsum]; exact hwEq⟩⟩
        · simp only [hkd, ↓reduceIte] at hmatch
          exact hfallbackStep htg hmatch
    cases op with
    | natPred =>
      cases htg : target with
      | nat b =>
        rcases as with _ | ⟨a0, _ | _⟩
        · exact hfallbackStep htg (by simpa [htg] using hrhs)
        · cases a0 with
          | var x =>
            simp only [htg] at hrhs
            by_cases hnzx : nz.contains x = true
            · simp only [hnzx, ↓reduceIte] at hrhs
              cases hlook : vm.lookup x with
              | none => simp only [hlook] at hrhs; exact hfallbackStep htg hrhs
              | some nr =>
                rcases nr with ⟨nx, rx⟩
                simp only [hlook] at hrhs
                by_cases hfn : rx.isFieldNat = true
                · simp only [hfn, ↓reduceIte] at hrhs
                  obtain ⟨n, hρx, hpos⟩ := hnz x (List.contains_iff_mem.mp hnzx)
                  have hEval : evalRhs P ρ (.prim .natPred [.var x]) = .ok (.lit (.nat (n - 1))) := by
                    simp [evalRhs, evalArgs, Arg.eval, hρx, primResult, natArgs]
                  obtain ⟨hnLim, htvr, ext, hoffW⟩ :=
                    eval_stepDownNat_poly fc lw hwf hkeys hnd hdatas hrhs (fun _ _ _ _ _ _ _ => rfl)
                      hlook hfn hEnvOk (htg ▸ htCore) hdem henv hoffs hρx hpos ev
                      (htg ▸ hTargetOfRhs _ hEval)
                  refine ⟨.lit (.nat (n - 1)), hEval, Fir.Proof.Shape.rhsSound hwf hEnvOk hRhsOk hEval,
                    htvr, ext, fun baseNm d ho => ?_⟩
                  obtain ⟨hmemBase, hbase⟩ := hoffW baseNm d ho
                  refine ⟨?_, n - 1, rfl, by omega, hbase⟩
                  rcases hmemBase with rfl | hmemO
                  · exact Or.inl (List.mem_map.mpr ⟨(x, baseNm, rx), mem_of_lookup_eq_some hlook, rfl⟩)
                  · exact Or.inr hmemO
                · simp only [hfn, Bool.false_eq_true, ↓reduceIte] at hrhs
                  exact hfallbackStep htg hrhs
            · simp only [hnzx, Bool.false_eq_true, ↓reduceIte] at hrhs
              exact hfallbackStep htg hrhs
          | lit _ | erased => exact hfallbackStep htg (by simpa [htg] using hrhs)
        · exact hfallbackStep htg (by simpa [htg] using hrhs)
      | irr | w8 | w16 | w32 | w64 | «enum» _ | data _ | obj =>
        exact hfallbackStep htg (by simpa [htg] using hrhs)
    | natSub =>
      cases htg : target with
      | nat b =>
        rcases as with _ | ⟨a0, _ | ⟨b0, _ | _⟩⟩
        · exact hfallbackStep htg (by simpa [htg] using hrhs)
        · exact hfallbackStep htg (by simpa [htg] using hrhs)
        · cases a0 with
          | var x =>
            cases b0 with
            | lit l =>
              cases l with
              | nat k =>
                cases k with
                | succ k' =>
                  cases k' with
                  | zero =>
                    simp only [htg] at hrhs
                    by_cases hnzx : nz.contains x = true
                    · simp only [hnzx, ↓reduceIte] at hrhs
                      cases hlook : vm.lookup x with
                      | none => simp only [hlook] at hrhs; exact hfallbackStep htg hrhs
                      | some nr =>
                        rcases nr with ⟨nx, rx⟩
                        simp only [hlook] at hrhs
                        by_cases hfn : rx.isFieldNat = true
                        · simp only [hfn, ↓reduceIte] at hrhs
                          obtain ⟨n, hρx, hpos⟩ := hnz x (List.contains_iff_mem.mp hnzx)
                          have hEval : evalRhs P ρ (.prim .natSub [.var x, .lit (.nat 1)]) = .ok (.lit (.nat (n - 1))) := by
                            simp [evalRhs, evalArgs, Arg.eval, hρx, primResult, natArgs]
                          obtain ⟨hnLim, htvr, ext, hoffW⟩ :=
                            eval_stepDownNat_poly fc lw hwf hkeys hnd hdatas hrhs (fun _ _ _ _ _ _ _ => rfl)
                              hlook hfn hEnvOk (htg ▸ htCore) hdem henv hoffs hρx hpos ev
                              (htg ▸ hTargetOfRhs _ hEval)
                          refine ⟨.lit (.nat (n - 1)), hEval, Fir.Proof.Shape.rhsSound hwf hEnvOk hRhsOk hEval,
                            htvr, ext, fun baseNm d ho => ?_⟩
                          obtain ⟨hmemBase, hbase⟩ := hoffW baseNm d ho
                          refine ⟨?_, n - 1, rfl, by omega, hbase⟩
                          rcases hmemBase with rfl | hmemO
                          · exact Or.inl (List.mem_map.mpr ⟨(x, baseNm, rx), mem_of_lookup_eq_some hlook, rfl⟩)
                          · exact Or.inr hmemO
                        · simp only [hfn, Bool.false_eq_true, ↓reduceIte] at hrhs
                          exact hfallbackStep htg hrhs
                    · simp only [hnzx, Bool.false_eq_true, ↓reduceIte] at hrhs
                      exact hfallbackStep htg hrhs
                  | succ _ => exact hfallbackStep htg (by simpa [htg] using hrhs)
                | zero => exact hfallbackStep htg (by simpa [htg] using hrhs)
              | str _ => exact hfallbackStep htg (by simpa [htg] using hrhs)
            | var _ | erased => exact hfallbackStep htg (by simpa [htg] using hrhs)
          | lit _ | erased => exact hfallbackStep htg (by simpa [htg] using hrhs)
        · exact hfallbackStep htg (by simpa [htg] using hrhs)
      | irr | w8 | w16 | w32 | w64 | «enum» _ | data _ | obj =>
        exact hfallbackStep htg (by simpa [htg] using hrhs)
    | natAdd =>
      cases htg : target with
      | nat b =>
        rcases as with _ | ⟨a0, _ | ⟨b0, _ | _⟩⟩
        · exact hfallbackStep htg (by simpa [htg] using hrhs)
        · exact hfallbackStep htg (by simpa [htg] using hrhs)
        · cases a0 with
          | var x =>
            cases b0 with
            | lit l =>
              cases l with
              | nat k =>
                simp only [htg] at hrhs
                exact haddFast x k b htg (fun _ hv => hv) hrhs
              | str _ => exact hfallbackStep htg (by simpa [htg] using hrhs)
            | var _ | erased => exact hfallbackStep htg (by simpa [htg] using hrhs)
          | lit l =>
            cases l with
            | nat k =>
              cases b0 with
              | var x =>
                simp only [htg] at hrhs
                refine haddFast x k b htg (fun v hv => ?_) hrhs
                cases hx : ρ.get? x with
                | none => simp [evalRhs, evalArgs, Arg.eval, hx] at hv
                | some vx =>
                  cases vx with
                  | lit lv =>
                    cases lv with
                    | nat nx =>
                      simp only [evalRhs, evalArgs, Arg.eval, hx, primResult, natArgs, Option.map_some,
                        Lam.Prim.sem, Lam.Prim.sem.srcOp, Src.PrimOp.eval2] at hv ⊢
                      rw [Nat.add_comm]; exact hv
                    | str _ => simp [evalRhs, evalArgs, Arg.eval, hx, primResult, natArgs] at hv
                  | ctor _ _ | erased => simp [evalRhs, evalArgs, Arg.eval, hx, primResult, natArgs] at hv
              | lit _ | erased => exact hfallbackStep htg (by simpa [htg] using hrhs)
            | str _ => exact hfallbackStep htg (by simpa [htg] using hrhs)
          | erased => exact hfallbackStep htg (by simpa [htg] using hrhs)
        · exact hfallbackStep htg (by simpa [htg] using hrhs)
      | irr | w8 | w16 | w32 | w64 | «enum» _ | data _ | obj =>
        exact hfallbackStep htg (by simpa [htg] using hrhs)
    | natMul | natDiv | natMod | natPow | natGcd | natShl | natShr
    | natBeq | natBle | natBlt | natLand | natLor | natXor =>
      exact hfallbackStep rfl hrhs
    | word _ _ => simp [Lam.Prim.isWord] at hopNoW

/-! ### Arm Selection and Backward Simulation of `tCaseE` -/

private theorem ctorEntry?_eq_of_nodup {P : Program} (hkeys : (P.ctors.map (·.key)).Nodup)
    {idx0 : Nat} {entry0 : Lam.CtorInfo} {k0 : CtorKey}
    (hget0 : P.ctors[idx0]? = some entry0) (hkey0 : entry0.key = k0) :
    Lower.ctorEntry? P k0 = some (idx0, entry0) :=
  hkey0 ▸ ctorEntry?_complete hkeys hget0

private theorem selectArm_enumCase_t {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {world : World F} {h : Heap F}
    (hkeys : (P.ctors.map (·.key)).Nodup) (hnd : (objCtorNames P).Nodup)
    {ind : Src.CId} {ks : List CtorKey} {k0 : CtorKey} {idx0 : Nat} {entry0 : Lam.CtorInfo}
    (hk0Mem : k0 ∈ ks) (hget0 : P.ctors[idx0]? = some entry0) (hkey0 : entry0.key = k0) :
    let cx : TCx := { P, cert, feat := scanFeatures P, sched }
    ∀ (xs : List (CtorKey × Lower.Expr)) (sA sB : TState)
      (arms : List (Lower.Pat × Lower.Expr)),
      (xs.filterMapM (m := TLowerM) fun (k, body) => do
        if ks.contains k then
          match cx.ctorEntry? k with
          | some (idx, entry) =>
            pure (some (Aiur.Generic.Pattern.construct (.named (enumName ind) []) (ctorNameOf idx entry.key) [], body))
          | none => pure none
        else pure none) sA = .ok (arms, sB) →
      (∀ bs body,
        SourceSemantics.selectArm world [] h (.construct (enumQName ind) (ctorNameOf idx0 k0) [])
          (arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) = .ok (some (bs, body)) →
        ∃ be, xs.find? (·.1 == k0) = some (k0, be) ∧ bs = [] ∧ body = qualifyExprF F be) ∧
      (SourceSemantics.selectArm world [] h (.construct (enumQName ind) (ctorNameOf idx0 k0) [])
          (arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) = .ok none →
        xs.find? (·.1 == k0) = none) := by
  intro cx xs sA sB arms hm
  let armFn : CtorKey × Lower.Expr → Option (Lower.Pat × Lower.Expr) := fun (k, body) =>
    if ks.contains k then
      match cx.ctorEntry? k with
      | some (idx, entry) =>
        some (Aiur.Generic.Pattern.construct (.named (enumName ind) []) (ctorNameOf idx entry.key) [], body)
      | none => none
    else none
  have hfm : (xs.filterMapM (m := TLowerM) fun (k, body) =>
      if ks.contains k then
        match cx.ctorEntry? k with
        | some (idx, entry) =>
          pure (some (Aiur.Generic.Pattern.construct (.named (enumName ind) []) (ctorNameOf idx entry.key) [], body))
        | none => pure none
      else pure none) sA = .ok (xs.filterMap armFn, sA) := by
    have heqFn : (fun ((k, body) : CtorKey × Lower.Expr) =>
        if ks.contains k then
          match cx.ctorEntry? k with
          | some (idx, entry) =>
            (pure (some (Aiur.Generic.Pattern.construct (.named (enumName ind) []) (ctorNameOf idx entry.key) [], body)) : TLowerM _)
          | none => pure none
        else pure none) = (fun p => pure (armFn p)) := by
      funext ⟨k, body⟩; dsimp only [armFn]
      split
      · cases cx.ctorEntry? k <;> rfl
      · rfl
    rw [heqFn]; exact filterMapM_pure_stateT armFn xs sA
  rw [hfm, Except.ok.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  clear hfm
  induction xs with
  | nil => exact ⟨(fun _ _ hs => by cases hs), (fun _ => rfl)⟩
  | cons hd tl ih =>
    rcases hd with ⟨k, be⟩
    by_cases hEqK : k = k0
    · subst hEqK
      have hce : cx.ctorEntry? k = some (idx0, entry0) := ctorEntry?_eq_of_nodup hkeys hget0 hkey0
      have hfa : armFn (k, be) = some (Aiur.Generic.Pattern.construct (.named (enumName ind) []) (ctorNameOf idx0 entry0.key) [], be) := by
        simp [armFn, hk0Mem, hce]
      simp only [List.filterMap_cons, hfa]
      constructor
      · intro bs body hs
        simp only [List.map_cons, SourceSemantics.selectArm, qualifyPatF, qualifyPat,
          qualifyTy, qualifyName_enumName, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol,
          List.map_nil, List.isEmpty_nil, ↓reduceIte, List.length_nil, hkey0, bne_self_eq_false,
          Bool.or_self, Bool.false_eq_true, bind, Except.bind, pure, Except.pure] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ⟨be, by simp, rfl, rfl⟩
      · intro hs
        simp only [List.map_cons, SourceSemantics.selectArm, qualifyPatF, qualifyPat,
          qualifyTy, qualifyName_enumName, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol,
          List.map_nil, List.isEmpty_nil, ↓reduceIte, List.length_nil, hkey0, bne_self_eq_false,
          Bool.or_self, Bool.false_eq_true, bind, Except.bind, pure, Except.pure] at hs
        cases hs
    · have hneB : (k == k0) = false := beq_false_of_ne hEqK
      cases hfa : armFn (k, be) with
      | none =>
        simp only [List.filterMap_cons, hfa]
        exact ⟨fun bs body hs => by
          obtain ⟨be', hf, rfl, rfl⟩ := ih.1 bs body hs
          exact ⟨be', by simp [hneB, hf], rfl, rfl⟩,
          fun hs => by simp [hneB, ih.2 hs]⟩
      | some pa =>
        have hfa0 := hfa
        simp only [armFn] at hfa
        split at hfa
        · cases hce : cx.ctorEntry? k with
          | none => simp [hce] at hfa
          | some ie =>
            rcases ie with ⟨idx', entry'⟩
            simp only [hce, Option.some.injEq] at hfa
            subst hfa
            obtain ⟨hget', hkey'⟩ := ctorEntry?_sound hce
            have hnmNe : ctorNameOf idx0 k0 ≠ ctorNameOf idx' entry'.key := fun heq => by
              rw [← hkey0] at heq
              obtain ⟨rfl, hentryEq⟩ := ctorNameOf_inj_of_nodup hnd hget0 hget' heq
              subst hentryEq
              exact hEqK (hkey'.symm.trans hkey0)
            have hnmNeB : (ctorNameOf idx0 k0 != ctorNameOf idx' entry'.key) = true := bne_iff_ne.mpr hnmNe
            simp only [List.filterMap_cons, hfa0]
            constructor
            · intro bs body hs
              simp only [List.map_cons, SourceSemantics.selectArm, qualifyPatF, qualifyPat,
                qualifyTy, qualifyName_enumName, Aiur.Generic.Pattern.map, World.matchPattern,
                matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol,
                List.map_nil, List.isEmpty_nil, ↓reduceIte, List.length_nil, bne_self_eq_false,
                Bool.false_or, Bool.or_false, hnmNeB, bind, Except.bind, pure, Except.pure] at hs
              obtain ⟨be', hf, rfl, rfl⟩ := ih.1 bs body hs
              exact ⟨be', by simp [hneB, hf], rfl, rfl⟩
            · intro hs
              simp only [List.map_cons, SourceSemantics.selectArm, qualifyPatF, qualifyPat,
                qualifyTy, qualifyName_enumName, Aiur.Generic.Pattern.map, World.matchPattern,
                matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol,
                List.map_nil, List.isEmpty_nil, ↓reduceIte, List.length_nil, bne_self_eq_false,
                Bool.false_or, Bool.or_false, hnmNeB, bind, Except.bind, pure, Except.pure] at hs
              simp [hneB, ih.2 hs]
        · cases hfa

private theorem selectArm_dataCase_t {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {world : World F} {h : Heap F}
    (hkeys : (P.ctors.map (·.key)).Nodup) (hnd : (objCtorNames P).Nodup)
    {did : Nat} {D : IxCC.Shape.DataDecl CtorKey} {k0 : CtorKey} {fl0 : List Shape}
    {idx0 : Nat} {entry0 : Lam.CtorInfo} {ws : List (SourceValue F)}
    (hk0Mem : (k0, fl0) ∈ D.ctors) (hget0 : P.ctors[idx0]? = some entry0)
    (hkey0 : entry0.key = k0) (hwsLen : ws.length = entry0.arity) :
    let cx : TCx := { P, cert, feat := scanFeatures P, sched }
    ∀ (xs : List (CtorKey × Lower.Expr)) (sA sB : TState)
      (arms : List (Lower.Pat × Lower.Expr)),
      (xs.filterMapM (m := TLowerM) fun (k, body) => do
        if D.ctors.any (·.1 == k) then
          match cx.ctorEntry? k with
          | some (idx, entry) =>
            pure (some (Aiur.Generic.Pattern.construct (.named (dataName did) []) (ctorNameOf idx entry.key)
              (List.replicate entry.arity .wildcard), body))
          | none => pure none
        else pure none) sA = .ok (arms, sB) →
      (∀ bs body,
        SourceSemantics.selectArm world [] h (.construct (dataQName did) (ctorNameOf idx0 k0) ws)
          (arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) = .ok (some (bs, body)) →
        ∃ be, xs.find? (·.1 == k0) = some (k0, be) ∧ bs = [] ∧ body = qualifyExprF F be) ∧
      (SourceSemantics.selectArm world [] h (.construct (dataQName did) (ctorNameOf idx0 k0) ws)
          (arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) = .ok none →
        xs.find? (·.1 == k0) = none) := by
  intro cx xs sA sB arms hm
  have hrepWild : ∀ n : Nat,
      List.map (Aiur.Generic.Pattern.map Nat.cast)
        (List.map qualifyPat (List.replicate n (Aiur.Generic.Pattern.wildcard : Lower.Pat))) =
      List.replicate n (Aiur.Generic.Pattern.wildcard : Aiur.Generic.Pattern F) := by
    intro n; induction n with
    | zero => rfl
    | succ _ _ => simp [List.replicate_succ, qualifyPat, Aiur.Generic.Pattern.map]
  let armFn : CtorKey × Lower.Expr → Option (Lower.Pat × Lower.Expr) := fun (k, body) =>
    if D.ctors.any (·.1 == k) then
      match cx.ctorEntry? k with
      | some (idx, entry) =>
        some (Aiur.Generic.Pattern.construct (.named (dataName did) []) (ctorNameOf idx entry.key)
          (List.replicate entry.arity .wildcard), body)
      | none => none
    else none
  have hfm : (xs.filterMapM (m := TLowerM) fun (k, body) =>
      if D.ctors.any (·.1 == k) then
        match cx.ctorEntry? k with
        | some (idx, entry) =>
          pure (some (Aiur.Generic.Pattern.construct (.named (dataName did) []) (ctorNameOf idx entry.key)
            (List.replicate entry.arity .wildcard), body))
        | none => pure none
      else pure none) sA = .ok (xs.filterMap armFn, sA) := by
    have heqFn : (fun ((k, body) : CtorKey × Lower.Expr) =>
        if D.ctors.any (·.1 == k) then
          match cx.ctorEntry? k with
          | some (idx, entry) =>
            (pure (some (Aiur.Generic.Pattern.construct (.named (dataName did) []) (ctorNameOf idx entry.key)
              (List.replicate entry.arity .wildcard), body)) : TLowerM _)
          | none => pure none
        else pure none) = (fun p => pure (armFn p)) := by
      funext ⟨k, body⟩; dsimp only [armFn]
      split
      · cases cx.ctorEntry? k <;> rfl
      · rfl
    rw [heqFn]; exact filterMapM_pure_stateT armFn xs sA
  rw [hfm, Except.ok.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  clear hfm
  induction xs with
  | nil => exact ⟨(fun _ _ hs => by cases hs), (fun _ => rfl)⟩
  | cons hd tl ih =>
    rcases hd with ⟨k, be⟩
    by_cases hEqK : k = k0
    · subst hEqK
      have hany : D.ctors.any (·.1 == k) = true := List.any_eq_true.mpr ⟨(k, fl0), hk0Mem, beq_self_eq_true k⟩
      have hce : cx.ctorEntry? k = some (idx0, entry0) := ctorEntry?_eq_of_nodup hkeys hget0 hkey0
      have hfa : armFn (k, be) = some (Aiur.Generic.Pattern.construct (.named (dataName did) []) (ctorNameOf idx0 entry0.key)
          (List.replicate entry0.arity .wildcard), be) := by
        simp only [armFn, hany, ↓reduceIte, hce]
      simp only [List.filterMap_cons, hfa]
      constructor
      · intro bs body hs
        simp only [List.map_cons, SourceSemantics.selectArm, qualifyPatF, qualifyPat,
          qualifyTy, qualifyName_dataName, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol,
          List.map_nil, List.isEmpty_nil, ↓reduceIte, hrepWild, List.length_replicate,
          hkey0, hwsLen, bne_self_eq_false, Bool.or_self, Bool.false_eq_true,
          bind, Except.bind, pure, Except.pure] at hs
        rw [matchListWith_attach_eq_t, matchListWith_replicate_wildcard_t entry0.arity ws hwsLen] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ⟨be, by simp, rfl, rfl⟩
      · intro hs
        simp only [List.map_cons, SourceSemantics.selectArm, qualifyPatF, qualifyPat,
          qualifyTy, qualifyName_dataName, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol,
          List.map_nil, List.isEmpty_nil, ↓reduceIte, hrepWild, List.length_replicate,
          hkey0, hwsLen, bne_self_eq_false, Bool.or_self, Bool.false_eq_true,
          bind, Except.bind, pure, Except.pure] at hs
        rw [matchListWith_attach_eq_t, matchListWith_replicate_wildcard_t entry0.arity ws hwsLen] at hs
        cases hs
    · have hneB : (k == k0) = false := beq_false_of_ne hEqK
      cases hfa : armFn (k, be) with
      | none =>
        simp only [List.filterMap_cons, hfa]
        exact ⟨fun bs body hs => by
          obtain ⟨be', hf, rfl, rfl⟩ := ih.1 bs body hs
          exact ⟨be', by simp [hneB, hf], rfl, rfl⟩,
          fun hs => by simp [hneB, ih.2 hs]⟩
      | some pa =>
        have hfa0 := hfa
        simp only [armFn] at hfa
        split at hfa
        · cases hce : cx.ctorEntry? k with
          | none => simp [hce] at hfa
          | some ie =>
            rcases ie with ⟨idx', entry'⟩
            simp only [hce, Option.some.injEq] at hfa
            subst hfa
            obtain ⟨hget', hkey'⟩ := ctorEntry?_sound hce
            have hnmNe : ctorNameOf idx0 k0 ≠ ctorNameOf idx' entry'.key := fun heq => by
              rw [← hkey0] at heq
              obtain ⟨rfl, hentryEq⟩ := ctorNameOf_inj_of_nodup hnd hget0 hget' heq
              subst hentryEq
              exact hEqK (hkey'.symm.trans hkey0)
            have hnmNeB : (ctorNameOf idx0 k0 != ctorNameOf idx' entry'.key) = true := bne_iff_ne.mpr hnmNe
            simp only [List.filterMap_cons, hfa0]
            constructor
            · intro bs body hs
              simp only [List.map_cons, SourceSemantics.selectArm, qualifyPatF, qualifyPat,
                qualifyTy, qualifyName_dataName, Aiur.Generic.Pattern.map, World.matchPattern,
                matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol,
                List.map_nil, List.isEmpty_nil, ↓reduceIte, hrepWild, List.length_replicate,
                bne_self_eq_false, Bool.false_or, hnmNeB, Bool.true_or, bind, Except.bind,
                pure, Except.pure] at hs
              obtain ⟨be', hf, rfl, rfl⟩ := ih.1 bs body hs
              exact ⟨be', by simp [hneB, hf], rfl, rfl⟩
            · intro hs
              simp only [List.map_cons, SourceSemantics.selectArm, qualifyPatF, qualifyPat,
                qualifyTy, qualifyName_dataName, Aiur.Generic.Pattern.map, World.matchPattern,
                matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol,
                List.map_nil, List.isEmpty_nil, ↓reduceIte, hrepWild, List.length_replicate,
                bne_self_eq_false, Bool.false_or, hnmNeB, Bool.true_or, bind, Except.bind,
                pure, Except.pure] at hs
              simp [hneB, ih.2 hs]
        · cases hfa

/-- Backward simulation of `TypedLower.tCaseE`: connects an `EvalExprN` derivation of a
specialized typed `case` (on `.nat`/`.w8`/`.w16`, `.enum`, `.data`, `.obj`, `.irr`)
directly to `v.asCtor P.known` and the matched arm (or default) expression. -/
theorem eval_tCaseE {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {world : World F}
    (fc : FieldCompatible64 F) (hkeys : (P.ctors.map (·.key)).Nodup) (hnd : (objCtorNames P).Nodup)
    {dDepth : Nat} {nx : String} {rx retR : Rep}
    {altEs : List (CtorKey × Lower.Expr)} {dE : Option Lower.Expr}
    {st st' : TState} {res : Lower.Expr}
    {v : Fir.Val} {w : SourceValue F} {locals : Environment F Nat}
    {h h' : Heap F} {r : SourceValue F}
    (hrxCore : isNatCoreRep rx = true)
    (hcase : tCaseE { P, cert, feat := scanFeatures P, sched } nx rx retR altEs dE st = .ok (res, st'))
    (hloc : locals.find? (·.1 == nx) = some (nx, w))
    (htvr : TVR P cert (scanFeatures P) h rx v w)
    (ev : EvalExprN world dDepth [] locals (qualifyExprF F res) h r h') :
    ∃ k fs be loc',
      v.asCtor P.known = some (k, fs) ∧
      ((altEs.find? (·.1 == k) = some (k, be)) ∨
       (altEs.find? (·.1 == k) = none ∧ dE = some be)) ∧
      EvalExprN world dDepth [] loc' (qualifyExprF F be) h r h' ∧
      (loc' = locals ∨
        (rx = .obj ∧ ∃ kq n, st.nextLocal ≤ kq ∧ loc' = (localName kq, .field (n : F)) :: locals)) := by
  set cx : TCx := { P, cert, feat := scanFeatures P, sched }
  set firsts := Lower.firstPerKey [] altEs
  unfold tCaseE at hcase
  have hExtract : ∀ {α : Type} {g : TLowerM Lower.Expr} {f : Lower.Expr → TLowerM α}
      {r0 : α} {s' : TState},
      (match dE with
       | some e => (pure e : TLowerM Lower.Expr) >>= f
       | none => g >>= f) st = .ok (r0, s') →
      ∃ fb sFb,
        ((∃ e, dE = some e ∧ fb = e ∧ sFb = st) ∨ (dE = none ∧ g st = .ok (fb, sFb))) ∧
        f fb sFb = .ok (r0, s') := by
    intro α g f r0 s' h0
    cases dE with
    | some e =>
      obtain ⟨fb, sFb, h1, h2⟩ := tBind_step_inv h0
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1
      obtain ⟨hfbEq, hsEq⟩ := h1; subst hfbEq; subst hsEq
      exact ⟨e, st, Or.inl ⟨e, rfl, rfl, rfl⟩, h2⟩
    | none =>
      obtain ⟨fb, sFb, h1, h2⟩ := tBind_step_inv h0
      exact ⟨fb, sFb, Or.inr ⟨rfl, h1⟩, h2⟩
  obtain ⟨fb, sFb, hfbRaw, hcase⟩ := hExtract hcase
  have hfbSpec : TStateLe st sFb ∧
      ((∃ e, dE = some e ∧ fb = e) ∨ (dE = none ∧ isTrapExpr fb)) := by
    rcases hfbRaw with ⟨e, hdEq, hfe, hse⟩ | ⟨hdEq, hfb⟩
    · subst hfe; subst hse; exact ⟨TStateLe.refl _, Or.inl ⟨fb, hdEq, rfl⟩⟩
    · have ⟨htrp, hle, _⟩ := tTrapE_ok_inv hfb (fun _ _ _ => rfl)
        (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
        (fun _ _ => rfl) (fun _ _ => rfl)
      exact ⟨hle, Or.inr ⟨hdEq, htrp⟩⟩
  have hpickSome : ∀ (k : CtorKey) {loc' : Environment F Nat},
      EvalExprN world dDepth [] loc' (qualifyExprF F (((firsts.find? (·.1 == k)).map (·.2)).getD fb)) h r h' →
      (altEs.find? (·.1 == k) = some (k, ((firsts.find? (·.1 == k)).map (·.2)).getD fb)) ∨
      (altEs.find? (·.1 == k) = none ∧ dE = some (((firsts.find? (·.1 == k)).map (·.2)).getD fb)) := by
    intro k loc' evB
    cases hf : altEs.find? (·.1 == k) with
    | some kb =>
      rcases kb with ⟨k', b'⟩
      have hk'Eq : k' = k := beq_iff_eq.mp (by simpa using List.find?_some hf)
      rcases hk'Eq with rfl
      have hff : firsts.find? (·.1 == k') = some (k', b') := by
        dsimp only [firsts]; rw [firstPerKey_nil_find?]; exact hf
      rw [hff]; simp
    | none =>
      have hff : firsts.find? (·.1 == k) = none := by
        dsimp only [firsts]; rw [firstPerKey_nil_find?]; exact hf
      simp only [hff, Option.map_none, Option.getD_none] at evB ⊢
      rcases hfbSpec.2 with ⟨e, rfl, rfl⟩ | ⟨rfl, htrp⟩
      · exact Or.inr ⟨trivial, rfl⟩
      · exact False.elim (evalExprN_of_isTrapExpr htrp evB)
  cases rx with
  | w32 | w64 => simp [isNatCoreRep] at hrxCore
  | irr =>
    have htrp := (tTrapE_ok_inv hcase (fun _ _ _ => rfl) (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl)) (fun _ _ => rfl) (fun _ _ => rfl)).1
    exact False.elim (evalExprN_of_isTrapExpr htrp ev)
  | nat b | w8 | w16 =>
    obtain ⟨zBody, sZ, hz, hcase⟩ := tBind_step_inv hcase
    obtain ⟨sBody, sS, hs, hcase⟩ := tBind_step_inv hcase
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hcase
    obtain ⟨rfl, rfl⟩ := hcase
    have ⟨n, hnLim, hvEq, hwEq⟩ : ∃ n, n < natLimit ∧ v = .lit (.nat n) ∧ w = .field (n : F) := by
      cases htvr
      rename_i hlt
      first
      | exact ⟨_, (Nat.lt_min.mp hlt).2, rfl, rfl⟩
      | exact ⟨_, lt_trans hlt (by decide), rfl, rfl⟩
    subst hvEq; subst hwEq
    obtain ⟨vx, hm, evX, hbr⟩ := evalExprN_match_lit_wild_inv ev
    simp only [vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evX
    obtain ⟨hlx, rfl⟩ := evalExprN_var_inv evX
    rw [hloc, Option.some.injEq, Prod.mk.injEq] at hlx
    obtain ⟨_, rfl⟩ := hlx
    rcases hbr with ⟨hn0F, evZ⟩ | ⟨hnNeF, evS⟩
    · have hn0 : n = 0 := fc.natCast_inj56 hnLim (by unfold natLimit; omega) (by simpa using Value.field.inj hn0F)
      subst hn0
      cases hkz : P.known.natZero with
      | none =>
        dsimp only [cx] at hz; simp only [hkz] at hz
        exact False.elim (evalExprN_of_isTrapExpr
          (tTrapE_ok_inv hz (fun _ _ _ => rfl) (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
            (fun _ _ => rfl) (fun _ _ => rfl)).1 evZ)
      | some kz =>
        dsimp only [cx] at hz
        simp only [hkz, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hz
        obtain ⟨rfl, rfl⟩ := hz
        exact ⟨kz, [], _, locals, by simp [Fir.Val.asCtor, hkz], hpickSome kz evZ, evZ, Or.inl rfl⟩
    · cases n with
      | zero => exact False.elim (hnNeF (by simp))
      | succ m =>
        cases hks : P.known.natSucc with
        | none =>
          dsimp only [cx] at hs; simp only [hks] at hs
          exact False.elim (evalExprN_of_isTrapExpr
            (tTrapE_ok_inv hs (fun _ _ _ => rfl) (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
              (fun _ _ => rfl) (fun _ _ => rfl)).1 evS)
        | some ks =>
          dsimp only [cx] at hs
          simp only [hks, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          exact ⟨ks, [.lit (.nat m)], _, locals, by simp [Fir.Val.asCtor, hks], hpickSome ks evS, evS, Or.inl rfl⟩
  | «enum» ind =>
    cases hE : cx.cert.enum? ind with
    | none => simp only [hE] at hcase; exact False.elim (tLift_throw_elim hcase (fun _ _ => rfl))
    | some ks =>
      simp only [hE] at hcase
      obtain ⟨arms, sA, hmap, hcase⟩ := tBind_step_inv hcase
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hcase
      obtain ⟨rfl, rfl⟩ := hcase
      obtain ⟨ks', c, idx, entry, hE', hcMem, hget, hkey, har, rfl, rfl⟩ := TVR_enum_inv htvr
      rw [hE, Option.some.injEq] at hE'; subst hE'
      simp only [matchE, vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
      obtain ⟨wx, hm, bs, body, evX, hsel, evB⟩ := evalExprN_match_inv ev
      obtain ⟨hlx, rfl⟩ := evalExprN_var_inv evX
      rw [hloc, Option.some.injEq, Prod.mk.injEq] at hlx
      obtain ⟨_, rfl⟩ := hlx
      have hmapApp :
          List.map (fun arm => (Aiur.Generic.Pattern.map Nat.cast arm.1, Aiur.Generic.Expr.map Nat.cast arm.2))
            (List.map (fun arm => (qualifyPat arm.1, qualifyExpr arm.2))
              (arms ++ match dE with | some e => [(.wildcard, e)] | none => [])) =
          (arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) ++
            (match dE with | some e => [(.wildcard, qualifyExprF F e)] | none => []) := by
        rw [List.map_append, List.map_append]
        congr 1
        · rw [List.map_map]; rfl
        · cases dE <;> simp [qualifyPat, Aiur.Generic.Pattern.map, qualifyExprF]
      have hsel := hmapApp ▸ hsel
      obtain ⟨hHit, hMiss⟩ :=
        selectArm_enumCase_t (world := world) (h := hm) hkeys hnd hcMem hget hkey firsts sFb sA arms hmap
      rcases selectArm_append_inv_t hsel with h1 | ⟨h1, h2⟩
      · obtain ⟨be, hff, rfl, rfl⟩ := hHit bs body h1
        rw [firstPerKey_nil_find?] at hff
        exact ⟨c.key, [], be, locals, rfl, Or.inl hff, evB, Or.inl rfl⟩
      · have hffNone := hMiss h1
        rw [firstPerKey_nil_find?] at hffNone
        cases hd : dE with
        | none => rw [hd] at h2; cases h2
        | some de =>
          rw [hd] at h2
          simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith] at h2
          obtain ⟨rfl, rfl⟩ := h2
          exact ⟨c.key, [], de, locals, rfl, Or.inr ⟨hffNone, rfl⟩, evB, Or.inl rfl⟩
  | data did =>
    cases hD : cx.cert.data? did with
    | none => simp only [hD] at hcase; exact False.elim (tLift_throw_elim hcase (fun _ _ => rfl))
    | some D =>
      simp only [hD] at hcase
      obtain ⟨arms, sA, hmap, hcase⟩ := tBind_step_inv hcase
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hcase
      obtain ⟨rfl, rfl⟩ := hcase
      obtain ⟨D', c, fl, idx, entry, fs, ws, hD', hcMem, hget, hkey, hflen, hfllen, hfields, rfl, rfl⟩ :=
        TVR_data_inv htvr
      rw [hD, Option.some.injEq] at hD'; subst hD'
      have hwsLen : ws.length = entry.arity := by have ⟨h1, h2⟩ := hfields.length_eq; omega
      simp only [matchE, vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
      obtain ⟨wx, hm, bs, body, evX, hsel, evB⟩ := evalExprN_match_inv ev
      obtain ⟨hlx, rfl⟩ := evalExprN_var_inv evX
      rw [hloc, Option.some.injEq, Prod.mk.injEq] at hlx
      obtain ⟨_, rfl⟩ := hlx
      have hmapApp :
          List.map (fun arm => (Aiur.Generic.Pattern.map Nat.cast arm.1, Aiur.Generic.Expr.map Nat.cast arm.2))
            (List.map (fun arm => (qualifyPat arm.1, qualifyExpr arm.2))
              (arms ++ match dE with | some e => [(.wildcard, e)] | none => [])) =
          (arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) ++
            (match dE with | some e => [(.wildcard, qualifyExprF F e)] | none => []) := by
        rw [List.map_append, List.map_append]
        congr 1
        · rw [List.map_map]; rfl
        · cases dE <;> simp [qualifyPat, Aiur.Generic.Pattern.map, qualifyExprF]
      have hsel := hmapApp ▸ hsel
      obtain ⟨hHit, hMiss⟩ :=
        selectArm_dataCase_t (world := world) (h := hm) hkeys hnd hcMem hget hkey hwsLen firsts sFb sA arms hmap
      rcases selectArm_append_inv_t hsel with h1 | ⟨h1, h2⟩
      · obtain ⟨be, hff, rfl, rfl⟩ := hHit bs body h1
        rw [firstPerKey_nil_find?] at hff
        exact ⟨c.key, fs, be, locals, rfl, Or.inl hff, evB, Or.inl rfl⟩
      · have hffNone := hMiss h1
        rw [firstPerKey_nil_find?] at hffNone
        cases hd : dE with
        | none => rw [hd] at h2; cases h2
        | some de =>
          rw [hd] at h2
          simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith] at h2
          obtain ⟨rfl, rfl⟩ := h2
          exact ⟨c.key, fs, de, locals, rfl, Or.inr ⟨hffNone, rfl⟩, evB, Or.inl rfl⟩
  | obj =>
    obtain ⟨sM, hleM, _, hcase⟩ := tMark_step_inv hcase (fun _ _ => rfl)
      (fun _ => by constructor <;> first | exact id | (intro _; rfl))
    obtain ⟨q, sQ, hq, hcase⟩ := tBind_step_inv hcase
    have hqEq : q = localName sM.nextLocal ∧ sQ = { sM with nextLocal := sM.nextLocal + 1 } := by
      have hstep : ∀ (fF : TLowerM String), fF sM = .ok (q, sQ) →
          (∀ s, fF s = .ok (localName s.nextLocal, { s with nextLocal := s.nextLocal + 1 })) →
          q = localName sM.nextLocal ∧ sQ = { sM with nextLocal := sM.nextLocal + 1 } := by
        intro fF hf hdef; rw [hdef] at hf; simp only [Except.ok.injEq, Prod.mk.injEq] at hf
        exact ⟨hf.1.symm, hf.2.symm⟩
      exact hstep _ hq (fun _ => rfl)
    obtain ⟨rfl, rfl⟩ := hqEq
    obtain ⟨zBody, sZ, hz, hcase⟩ := tBind_step_inv hcase
    obtain ⟨sBody, sS, hs, hcase⟩ := tBind_step_inv hcase
    obtain ⟨erTr, sE, herTr, hcase⟩ := tBind_step_inv hcase
    obtain ⟨stTr, sSt, hstTr, hcase⟩ := tBind_step_inv hcase
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hcase
    obtain ⟨rfl, rfl⟩ := hcase
    have herTrap := (tTrapE_ok_inv herTr (fun _ _ _ => rfl) (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl)) (fun _ _ => rfl) (fun _ _ => rfl)).1
    have hstTrap := (tTrapE_ok_inv hstTr (fun _ _ _ => rfl) (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl)) (fun _ _ => rfl) (fun _ _ => rfl)).1
    have hvr := TVR_obj_inv htvr
    simp only [matchE, vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    obtain ⟨wx, hm, bs, body, evX, hsel, evB⟩ := evalExprN_match_inv ev
    obtain ⟨hlx, rfl⟩ := evalExprN_var_inv evX
    rw [hloc, Option.some.injEq, Prod.mk.injEq] at hlx
    obtain ⟨_, rfl⟩ := hlx
    set arms := Lower.ctorArms ⟨P⟩ firsts
    set natArm : Lower.Pat × Lower.Expr :=
      (pN (.bind (localName sM.nextLocal)), matchE (vE (localName sM.nextLocal)) [(.literal 0, zBody), (.wildcard, sBody)])
    set erasedArm : Lower.Pat × Lower.Expr := (pC "E" [], erTr)
    set strArm : Lower.Pat × Lower.Expr := (pC "S" [.wildcard], stTr)
    have hmapApp :
        List.map (fun arm => (Aiur.Generic.Pattern.map Nat.cast arm.1, Aiur.Generic.Expr.map Nat.cast arm.2))
          (List.map (fun arm => (qualifyPat arm.1, qualifyExpr arm.2))
            (arms ++ [natArm, erasedArm, strArm] ++ match dE with | some e => [(.wildcard, e)] | none => [])) =
        (arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) ++
          ([natArm, erasedArm, strArm].map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) ++
          (match dE with | some e => [(.wildcard, qualifyExprF F e)] | none => []) := by
      rw [List.map_append, List.map_append, List.map_append, List.map_append]
      congr 1
      · congr 1; rw [List.map_map]; rfl
      · cases dE <;> simp [qualifyPat, Aiur.Generic.Pattern.map, qualifyExprF]
    have hsel := hmapApp ▸ hsel
    have hleStM : st.nextLocal ≤ sM.nextLocal := (hfbSpec.1.trans hleM).nextLocal
    cases hvr with
    | @nat n hn =>
      have hmissArms : SourceSemantics.selectArm world [] hm (.construct objQName "N" [.field (n : F)])
          (arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) = .ok none :=
        selectArm_ctorArms_miss_t Lower.ctorNameOf_ne_N firsts
      rcases selectArm_append_inv_t hsel with h12 | ⟨h12, _⟩
      · rcases selectArm_append_inv_t h12 with h1 | ⟨_, h2⟩
        · rw [hmissArms] at h1; cases h1
        · simp only [natArm, List.map_cons, SourceSemantics.selectArm, pN, qualifyPatF, qualifyPat,
            qualifyTy, objTy, qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern,
            matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol,
            List.map_nil, List.isEmpty_nil, ↓reduceIte, List.length_cons, List.length_nil,
            bne_self_eq_false, Bool.or_self, Bool.false_eq_true, bind, Except.bind,
            pure, Except.pure] at h2
          simp [matchListWith, matchPatternWith] at h2
          obtain ⟨rfl, rfl⟩ := h2
          obtain ⟨vq, hm1, evQ, hbr⟩ := evalExprN_match_lit_wild_inv evB
          simp only [vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evQ
          obtain ⟨hlq, rfl⟩ := evalExprN_var_inv evQ
          simp only [List.cons_append, List.nil_append, List.find?_cons, beq_self_eq_true,
            Option.some.injEq, Prod.mk.injEq] at hlq
          obtain ⟨_, rfl⟩ := hlq
          rcases hbr with ⟨hn0F, evZ⟩ | ⟨hnNeF, evS⟩
          · have hn0 : n = 0 := fc.natCast_inj56 hn (by unfold natLimit; omega) (by simpa using Value.field.inj hn0F)
            subst hn0
            cases hkz : P.known.natZero with
            | none =>
              dsimp only [cx] at hz; simp only [hkz] at hz
              exact False.elim (evalExprN_of_isTrapExpr
                (tTrapE_ok_inv hz (fun _ _ _ => rfl) (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
                  (fun _ _ => rfl) (fun _ _ => rfl)).1 evZ)
            | some kz =>
              dsimp only [cx] at hz
              simp only [hkz, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hz
              obtain ⟨rfl, rfl⟩ := hz
              simp only [List.cons_append, List.nil_append, Nat.cast_zero] at evZ
              exact ⟨kz, [], _, (localName sM.nextLocal, .field (0 : F)) :: locals,
                by simp [Fir.Val.asCtor, hkz], hpickSome kz evZ, evZ, Or.inr ⟨rfl, sM.nextLocal, 0, hleStM, by simp⟩⟩
          · cases n with
            | zero => exact False.elim (hnNeF (by simp))
            | succ m =>
              cases hks : P.known.natSucc with
              | none =>
                dsimp only [cx] at hs; simp only [hks] at hs
                exact False.elim (evalExprN_of_isTrapExpr
                  (tTrapE_ok_inv hs (fun _ _ _ => rfl) (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
                    (fun _ _ => rfl) (fun _ _ => rfl)).1 evS)
              | some ks =>
                dsimp only [cx] at hs
                simp only [hks, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hs
                obtain ⟨rfl, rfl⟩ := hs
                simp only [List.cons_append, List.nil_append] at evS
                exact ⟨ks, [.lit (.nat m)], _, (localName sM.nextLocal, .field ((m + 1 : Nat) : F)) :: locals,
                  by simp [Fir.Val.asCtor, hks], hpickSome ks evS, evS, Or.inr ⟨rfl, sM.nextLocal, m + 1, hleStM, by simp⟩⟩
      · exfalso
        have hstep : SourceSemantics.selectArm world [] hm (.construct objQName "N" [.field (n : F)])
            ([natArm, erasedArm, strArm].map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) = .ok none := by
          have aux : ∀ l1 l2,
              SourceSemantics.selectArm world [] hm (.construct objQName "N" [.field (n : F)]) (l1 ++ l2) = .ok none →
              SourceSemantics.selectArm world [] hm (.construct objQName "N" [.field (n : F)]) l1 = .ok none →
              SourceSemantics.selectArm world [] hm (.construct objQName "N" [.field (n : F)]) l2 = .ok none := by
            intro l1; induction l1 with
            | nil => intro _ h0 _; exact h0
            | cons a1 tl1 ih1 =>
              intro l2 h0 h1
              simp only [List.cons_append, SourceSemantics.selectArm, bind, Except.bind] at h0 h1
              cases hm0 : world.matchPattern [] hm a1.1 (.construct objQName "N" [.field (n : F)]) with
              | error _ => simp [hm0] at h1
              | ok o => cases o with
                | some _ => simp [hm0, pure, Except.pure] at h1
                | none => simp only [hm0] at h0 h1; exact ih1 l2 h0 h1
          exact aux _ _ h12 hmissArms
        simp only [natArm, List.map_cons, SourceSemantics.selectArm, pN, qualifyPatF, qualifyPat,
          qualifyTy, objTy, qualifyName_obj, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, constructorName, Ty.subst, Ty.toCore, Instance.symbol,
          List.map_nil, List.isEmpty_nil, ↓reduceIte, List.length_cons, List.length_nil,
          bne_self_eq_false, Bool.or_self, Bool.false_eq_true, bind, Except.bind,
          pure, Except.pure] at hstep
        simp [matchListWith, matchPatternWith, bind, Except.bind, pure, Except.pure] at hstep
    | erased =>
      have hmissArms : SourceSemantics.selectArm world [] hm (.construct objQName "E" [])
          (arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) = .ok none :=
        selectArm_ctorArms_miss_t Lower.ctorNameOf_ne_E firsts
      have hselMid : SourceSemantics.selectArm world [] hm (.construct objQName "E" [])
          ([natArm, erasedArm, strArm].map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) =
          .ok (some ([], qualifyExprF F erTr)) := by
        simp only [natArm, erasedArm, List.map_cons, SourceSemantics.selectArm, pN, pC,
          qualifyPatF, qualifyPat, qualifyTy, objTy, qualifyName_obj, Aiur.Generic.Pattern.map,
          World.matchPattern, matchPatternWith, constructorName, Ty.subst, Ty.toCore,
          Instance.symbol, List.map_nil, List.isEmpty_nil, ↓reduceIte, List.length_cons,
          List.length_nil, bne_self_eq_false, Bool.false_or, Bool.or_self, Bool.false_eq_true,
          bind, Except.bind, pure, Except.pure]
        have hEN : ("E" != "N") = true := by decide
        simp [hEN, matchListWith, pure, Except.pure]
      have hsel12 : SourceSemantics.selectArm world [] hm (.construct objQName "E" [])
          ((arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) ++
           ([natArm, erasedArm, strArm].map fun a => (qualifyPatF F a.1, qualifyExprF F a.2))) =
          .ok (some ([], qualifyExprF F erTr)) := by
        have aux : ∀ l1 l2 res,
            SourceSemantics.selectArm world [] hm (.construct objQName "E" []) l1 = .ok none →
            SourceSemantics.selectArm world [] hm (.construct objQName "E" []) l2 = res →
            SourceSemantics.selectArm world [] hm (.construct objQName "E" []) (l1 ++ l2) = res := by
          intro l1; induction l1 with
          | nil => intro _ _ _ h2; exact h2
          | cons a1 tl1 ih1 =>
            intro l2 res h1 h2
            simp only [List.cons_append, SourceSemantics.selectArm, bind, Except.bind] at h1 ⊢
            cases hm0 : world.matchPattern [] hm a1.1 (.construct objQName "E" []) with
            | error _ => simp [hm0] at h1
            | ok o => cases o with
              | some _ => simp [hm0, pure, Except.pure] at h1
              | none => simp only [hm0] at h1 ⊢; exact ih1 l2 res h1 h2
        exact aux _ _ _ hmissArms hselMid
      rcases selectArm_append_inv_t hsel with h12 | ⟨h12, _⟩
      · rw [hsel12, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h12
        obtain ⟨rfl, rfl⟩ := h12
        exact False.elim (evalExprN_of_isTrapExpr herTrap evB)
      · rw [hsel12] at h12; cases h12
    | @str s bw _ =>
      have hmissArms : SourceSemantics.selectArm world [] hm (.construct objQName "S" [bw])
          (arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) = .ok none :=
        selectArm_ctorArms_miss_t Lower.ctorNameOf_ne_S firsts
      have hselMid : SourceSemantics.selectArm world [] hm (.construct objQName "S" [bw])
          ([natArm, erasedArm, strArm].map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) =
          .ok (some ([], qualifyExprF F stTr)) := by
        simp only [natArm, erasedArm, strArm, List.map_cons, SourceSemantics.selectArm, pN, pC,
          qualifyPatF, qualifyPat, qualifyTy, objTy, qualifyName_obj, Aiur.Generic.Pattern.map,
          World.matchPattern, matchPatternWith, constructorName, Ty.subst, Ty.toCore,
          Instance.symbol, List.map_nil, List.isEmpty_nil, ↓reduceIte, List.length_cons,
          List.length_nil, bne_self_eq_false, Bool.false_or, Bool.or_self, Bool.false_eq_true,
          bind, Except.bind, pure, Except.pure]
        have hSN : ("S" != "N") = true := by decide
        have hSE : ("S" != "E") = true := by decide
        simp [hSN, hSE, matchListWith, matchPatternWith, bind, Except.bind, pure, Except.pure]
      have hsel12 : SourceSemantics.selectArm world [] hm (.construct objQName "S" [bw])
          ((arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) ++
           ([natArm, erasedArm, strArm].map fun a => (qualifyPatF F a.1, qualifyExprF F a.2))) =
          .ok (some ([], qualifyExprF F stTr)) := by
        have aux : ∀ l1 l2 res,
            SourceSemantics.selectArm world [] hm (.construct objQName "S" [bw]) l1 = .ok none →
            SourceSemantics.selectArm world [] hm (.construct objQName "S" [bw]) l2 = res →
            SourceSemantics.selectArm world [] hm (.construct objQName "S" [bw]) (l1 ++ l2) = res := by
          intro l1; induction l1 with
          | nil => intro _ _ _ h2; exact h2
          | cons a1 tl1 ih1 =>
            intro l2 res h1 h2
            simp only [List.cons_append, SourceSemantics.selectArm, bind, Except.bind] at h1 ⊢
            cases hm0 : world.matchPattern [] hm a1.1 (.construct objQName "S" [bw]) with
            | error _ => simp [hm0] at h1
            | ok o => cases o with
              | some _ => simp [hm0, pure, Except.pure] at h1
              | none => simp only [hm0] at h1 ⊢; exact ih1 l2 res h1 h2
        exact aux _ _ _ hmissArms hselMid
      rcases selectArm_append_inv_t hsel with h12 | ⟨h12, _⟩
      · rw [hsel12, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h12
        obtain ⟨rfl, rfl⟩ := h12
        exact False.elim (evalExprN_of_isTrapExpr hstTrap evB)
      · rw [hsel12] at h12; cases h12
    | @ctor ci idx entry fs ps hget hkey hflen hvrs =>
      have hpsLen : ps.length = entry.arity := by have := hvrs.length_eq; omega
      have hctorSel := selectArm_ctorArms_ctor_t (world := world) (h := hm) hnd hkeys hget hpsLen firsts
      rw [firstPerKey_nil_find?, hkey] at hctorSel
      have hmissMid : SourceSemantics.selectArm world [] hm (.construct objQName (ctorNameOf idx ci.key) ps)
          ([natArm, erasedArm, strArm].map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) = .ok none := by
        have hN : (ctorNameOf idx ci.key != "N") = true := bne_iff_ne.mpr (Lower.ctorNameOf_ne_N idx ci.key)
        have hE : (ctorNameOf idx ci.key != "E") = true := bne_iff_ne.mpr (Lower.ctorNameOf_ne_E idx ci.key)
        have hS : (ctorNameOf idx ci.key != "S") = true := bne_iff_ne.mpr (Lower.ctorNameOf_ne_S idx ci.key)
        simp only [natArm, erasedArm, strArm, List.map_cons, List.map_nil, SourceSemantics.selectArm,
          pN, pC, qualifyPatF, qualifyPat, qualifyTy, objTy, qualifyName_obj,
          Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith, constructorName,
          Ty.subst, Ty.toCore, Instance.symbol, List.isEmpty_nil, ↓reduceIte, List.length_cons,
          List.length_nil, bne_self_eq_false, Bool.false_or, hN, hE, hS, Bool.true_or,
          bind, Except.bind, pure, Except.pure]
      cases hf : altEs.find? (·.1 == ci.key) with
      | some kb =>
        rcases kb with ⟨k', be⟩
        have hk'Eq : k' = ci.key := beq_iff_eq.mp (by simpa using List.find?_some hf)
        subst hk'Eq
        rw [hf] at hctorSel
        simp only [Option.map_some] at hctorSel
        rcases selectArm_append_inv_t hsel with h12 | ⟨h12, _⟩
        · rcases selectArm_append_inv_t h12 with h1 | ⟨h1, _⟩
          · rw [hctorSel, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1
            exact ⟨ci.key, fs, be, locals, rfl, Or.inl hf, evB, Or.inl rfl⟩
          · rw [hctorSel] at h1; cases h1
        · exfalso
          have aux : ∀ l1 l2,
              SourceSemantics.selectArm world [] hm (.construct objQName (ctorNameOf idx ci.key) ps) (l1 ++ l2) = .ok none →
              SourceSemantics.selectArm world [] hm (.construct objQName (ctorNameOf idx ci.key) ps) l1 = .ok none := by
            intro l1; induction l1 with
            | nil => intro _ _; rfl
            | cons a1 tl1 ih1 =>
              intro l2 h0
              simp only [List.cons_append, SourceSemantics.selectArm, bind, Except.bind] at h0 ⊢
              cases hm0 : world.matchPattern [] hm a1.1 (.construct objQName (ctorNameOf idx ci.key) ps) with
              | error _ => simp [hm0] at h0
              | ok o => cases o with
                | some _ => simp [hm0, pure, Except.pure] at h0
                | none => simp only [hm0] at h0 ⊢; exact ih1 l2 h0
          have := aux _ _ h12; rw [hctorSel] at this; cases this
      | none =>
        rw [hf] at hctorSel
        simp only [Option.map_none] at hctorSel
        rcases selectArm_append_inv_t hsel with h12 | ⟨_, h3⟩
        · rcases selectArm_append_inv_t h12 with h1 | ⟨_, h2⟩
          · rw [hctorSel] at h1; cases h1
          · rw [hmissMid] at h2; cases h2
        · cases hd : dE with
          | none => rw [hd] at h3; cases h3
          | some de =>
            rw [hd] at h3
            simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith] at h3
            obtain ⟨rfl, rfl⟩ := h3
            exact ⟨ci.key, fs, de, locals, rfl, Or.inr ⟨hf, rfl⟩, evB, Or.inl rfl⟩

end TypedEnvsDec

/-! ## Section 7: Master Backward Simulation (`eval_tCodeE_sound_N`) -/

section MainTypedProof

variable {F : Type} [Field F] [DecidableEq F]

/-- Discharge `TypedLoweredWorld` purely from `checkTypedWorld` for any `natCoreProgram`
(since `natCoreProgram` rules out `usesW32`, hence `lp.tier ≠ .u32`). -/
theorem typedLoweredWorld_of_natCore (fc : FieldCompatible64 F)
    {P : Program} {cert : ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    (hnc : natCoreProgram P cert = true)
    (hlow : TypedLower.lowerProgram P cert sched = .ok lp)
    (s : Generic.Source F) (hchk : checkTypedWorld s lp = true) :
    TypedLoweredWorld P cert sched lp s.world :=
  typedLoweredWorld_of_check_noU32 fc hlow
    (tier_ne_u32_of_not_usesW32 hlow (natCoreProgram_not_usesW32 hnc)) s hchk

omit [Field F] [DecidableEq F] in
theorem isCleanNoU32_rewriteExpr {e : Lower.Expr} (hc : isCleanNoU32 e = true) :
    isCleanNoU32 (Peephole.rewriteExpr e) = true := by
  unfold Peephole.rewriteExpr
  rw [lowerByteShifts_eq_self_of_clean [] (isCleanNoU32_fuseExpr [] hc)]
  exact isCleanNoU32_fuseExpr [] hc

theorem evalFnN_rewritten_clean_inv {world : World F} {d : Nat} {name : String}
    {paramNames : List String} {body : Lower.Expr} {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F}
    (hwf : WorldHasFn world name paramNames (qualifyExprF F (Peephole.rewriteExpr body)))
    (hc : isCleanNoU32 body = true)
    (ev : EvalFnN world d name args h r h') :
    args.length = paramNames.length ∧
    EvalExprN world d [] (paramNames.zip args) (qualifyExprF F body) h r h' := by
  have hplain : isPlainExpr (qualifyExprF F (Peephole.rewriteExpr body)) = true := by
    rw [isPlainExpr_qualifyExprF]
    exact isPlainExpr_of_isCleanNoU32 (isCleanNoU32_rewriteExpr hc)
  obtain ⟨hlen, evRew⟩ := evalFnN_plain_inv hwf hplain ev
  exact ⟨hlen, evalExprN_of_rewriteExpr_clean hc evRew⟩

omit [Field F] [DecidableEq F] in
private theorem evalCall_valOk {P : Program} {cert : ShapeCert} (hchk : Checked P cert)
    {f : FunId} {k : Nat} {vs : List Fir.Val} {v : Fir.Val}
    (hsz : f < P.size) (hvs : ValsOk cert dummyEnc (cert.fn f).params vs)
    (hcall : Fir.evalCall P k f vs = .ok v) :
    ValOk cert dummyEnc (cert.fn f).ret v :=
  Fir.Proof.Shape.checkSound dummyEnc P cert hchk f k vs v hsz hvs (by rw [Fir.run_eq]; exact hcall)

omit [Field F] [DecidableEq F] in
private theorem AllLocalLt_bindTVm {n m : Nat} {vm : TVarMap} {ps : List Var}
    {nrs : List (String × Rep)}
    (hvm : AllLocalLt n (vm.map fun p => p.2.1))
    (hpns : AllLocalLt m (nrs.map Prod.fst))
    (hle : n ≤ m) :
    AllLocalLt m ((bindTVm vm ps nrs).map fun p => p.2.1) := by
  intro s hs
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
  rcases bindTVm_mem hp with h1 | ⟨_, _, nr, hnr, rfl⟩
  · exact hvm.mono hle _ (List.mem_map.mpr ⟨p, h1, rfl⟩)
  · exact hpns _ (List.mem_map.mpr ⟨nr, hnr, rfl⟩)

omit [Field F] [DecidableEq F] in
private theorem AllLocalLt_initOffs {m : Nat} {ps : List Var} {pns : List String} {rs : List Rep}
    (hpns : AllLocalLt m pns) :
    AllLocalLt m
      (((ps.zip (pns.zip rs)).filterMap fun (p, nm, r) =>
          match r with | .nat _ => some (p, (nm, 0)) | _ => none).map fun p => p.2.1) := by
  intro s hs
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
  simp only [List.mem_filterMap] at hq
  obtain ⟨⟨p, nm, r⟩, hmem, hcase⟩ := hq
  cases r <;> simp at hcase
  obtain ⟨rfl, rfl⟩ := hcase
  exact hpns _ (List.of_mem_zip (List.of_mem_zip hmem).2).1

omit [Field F] [DecidableEq F] in
private theorem AllLocalLt_offs_update {n m : Nat} {vm : TVarMap} {offs : OffMap}
    {x : Var} {xOff? : Option (String × Nat)}
    (hvm : AllLocalLt n (vm.map fun p => p.2.1))
    (hoffs : AllLocalLt n (offs.map fun p => p.2.1))
    (hxOff : ∀ baseNm d, xOff? = some (baseNm, d) →
      baseNm ∈ vm.map (fun p => p.2.1) ∨ baseNm ∈ offs.map (fun p => p.2.1))
    (hle : n ≤ m) :
    AllLocalLt m
      ((match xOff? with
        | some off => (x, off) :: offs.filter (·.1 != x)
        | none => offs.filter (·.1 != x)).map fun (p : Var × String × Nat) => p.2.1) := by
  have hfilt : AllLocalLt m ((offs.filter (·.1 != x)).map fun p => p.2.1) := by
    intro s hs
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
    exact hoffs.mono hle _ (List.mem_map.mpr ⟨q, List.mem_of_mem_filter hq, rfl⟩)
  cases xOff? with
  | none => exact hfilt
  | some off =>
    rcases off with ⟨b0, d0⟩
    intro s hs
    simp only [List.map_cons, List.mem_cons] at hs
    rcases hs with rfl | htl
    · rcases hxOff s d0 rfl with hm1 | hm2
      · exact hvm.mono hle _ hm1
      · exact hoffs.mono hle _ hm2
    · exact hfilt s htl

private theorem eval_capNames_any {world : World F} {d : Nat} {locals : Environment F Nat} :
    ∀ {nms : List String} {capWs : List (SourceValue F)} {h h' : Heap F},
      EvalArgsN world d [] locals (nms.map fun nm => qualifyExprF F (vE nm)) h capWs h' →
      EvalCapArgs locals nms capWs ∧ h' = h
  | [], _, _, _, .nil => ⟨trivial, rfl⟩
  | _ :: _, _, _, _, .cons h1 htl => by
    simp only [vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at h1
    obtain ⟨hlook, rfl⟩ := evalExprN_var_inv h1
    obtain ⟨htlCap, rfl⟩ := eval_capNames_any htl
    exact ⟨⟨hlook, htlCap⟩, rfl⟩

private theorem eval_tCaseE_scrut_loc {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {world : World F} {dDepth : Nat} {nx : String} {rx retR : Rep}
    {altEs : List (CtorKey × Lower.Expr)} {dE : Option Lower.Expr}
    {st st' : TState} {res : Lower.Expr}
    {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F}
    (hrxCore : isNatCoreRep rx = true)
    (hcase : tCaseE { P, cert, feat := scanFeatures P, sched } nx rx retR altEs dE st = .ok (res, st'))
    (ev : EvalExprN world dDepth [] locals (qualifyExprF F res) h r h') :
    ∃ w, locals.find? (·.1 == nx) = some (nx, w) := by
  unfold tCaseE at hcase
  have hExtract : ∀ {α : Type} {g : TLowerM Lower.Expr} {f : Lower.Expr → TLowerM α}
      {r0 : α} {s' : TState},
      (match dE with
       | some e => (pure e : TLowerM Lower.Expr) >>= f
       | none => g >>= f) st = .ok (r0, s') →
      ∃ fb sFb, f fb sFb = .ok (r0, s') := by
    intro α g f r0 s' h0
    cases dE with
    | some e =>
      obtain ⟨fb, sFb, _, h2⟩ := tBind_step_inv h0
      exact ⟨fb, sFb, h2⟩
    | none =>
      obtain ⟨fb, sFb, _, h2⟩ := tBind_step_inv h0
      exact ⟨fb, sFb, h2⟩
  obtain ⟨fb, sFb, hcase⟩ := hExtract hcase
  cases rx with
  | w32 | w64 => simp [isNatCoreRep] at hrxCore
  | irr =>
    have htrp := (tTrapE_ok_inv hcase (fun _ _ _ => rfl)
      (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
      (fun _ _ => rfl) (fun _ _ => rfl)).1
    exact False.elim (evalExprN_of_isTrapExpr htrp ev)
  | nat _ | w8 | w16 =>
    obtain ⟨_, _, _, hcase⟩ := tBind_step_inv hcase
    obtain ⟨_, _, _, hcase⟩ := tBind_step_inv hcase
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hcase
    obtain ⟨rfl, rfl⟩ := hcase
    simp only [matchE, vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    obtain ⟨w, _, _, _, evX, _, _⟩ := evalExprN_match_inv ev
    obtain ⟨hlx, _⟩ := evalExprN_var_inv evX
    exact ⟨w, hlx⟩
  | «enum» ind =>
    cases he : cert.enum? ind with
    | none => simp only [he] at hcase; exact False.elim (tLift_throw_elim hcase (fun _ _ => rfl))
    | some ks =>
      simp only [he] at hcase
      obtain ⟨_, _, _, hcase⟩ := tBind_step_inv hcase
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hcase
      obtain ⟨rfl, rfl⟩ := hcase
      simp only [matchE, vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
      obtain ⟨w, _, _, _, evX, _, _⟩ := evalExprN_match_inv ev
      obtain ⟨hlx, _⟩ := evalExprN_var_inv evX
      exact ⟨w, hlx⟩
  | data did =>
    cases hd : cert.data? did with
    | none => simp only [hd] at hcase; exact False.elim (tLift_throw_elim hcase (fun _ _ => rfl))
    | some D =>
      simp only [hd] at hcase
      obtain ⟨_, _, _, hcase⟩ := tBind_step_inv hcase
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hcase
      obtain ⟨rfl, rfl⟩ := hcase
      simp only [matchE, vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
      obtain ⟨w, _, _, _, evX, _, _⟩ := evalExprN_match_inv ev
      obtain ⟨hlx, _⟩ := evalExprN_var_inv evX
      exact ⟨w, hlx⟩
  | obj =>
    obtain ⟨_, _, _, hcase⟩ := tBind_step_inv hcase
    obtain ⟨_, _, _, hcase⟩ := tBind_step_inv hcase
    obtain ⟨_, _, _, hcase⟩ := tBind_step_inv hcase
    obtain ⟨_, _, _, hcase⟩ := tBind_step_inv hcase
    obtain ⟨_, _, _, hcase⟩ := tBind_step_inv hcase
    obtain ⟨_, _, _, hcase⟩ := tBind_step_inv hcase
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hcase
    obtain ⟨rfl, rfl⟩ := hcase
    simp only [matchE, vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    obtain ⟨w, _, _, _, evX, _, _⟩ := evalExprN_match_inv ev
    obtain ⟨hlx, _⟩ := evalExprN_var_inv evX
    exact ⟨w, hlx⟩

omit [Field F] [DecidableEq F] in
private theorem tAltsE_find_sound {cx : TCx} {fid : FunId} {fsh : FunShapes} {retR : Rep}
    {vm : TVarMap} {jenv : List TJEntry} {nz : List Var} {offs : OffMap}
    {scrut : Var} {scrutR : Rep} :
    ∀ {alts : List Alt} {st st1 : TState} {altEs : List (CtorKey × Lower.Expr)} {k : CtorKey},
      tAltsE cx fid fsh retR vm jenv nz offs scrut scrutR alts st = .ok (altEs, st1) →
      (∀ p, altEs.find? (·.1 == k) = some p →
        ∃ b stA stB,
          b.size ≤ Code.altsSize alts ∧
          tCodeE cx fid fsh retR vm jenv
            (if scrutR.isFieldNat && cx.P.known.natSucc == some k then
              if nz.contains scrut then nz else scrut :: nz
             else nz)
            offs b stA = .ok (p.2, stB) ∧
          st.nextLocal ≤ stA.nextLocal ∧
          (∀ g ∈ stB.lifted, g ∈ st1.lifted) ∧
          DemandLe stB.demand st1.demand ∧
          (AltsOk cx.P cx.cert fsh alts → CodeOk cx.P cx.cert fsh b) ∧
          (altsParamsNodup alts = true → codeParamsNodup b = true) ∧
          (altsNoWordPrims alts = true → codeNoWordPrims b = true) ∧
          (altsNatCoreReps cx.P cx.cert cx.feat fsh alts = true →
            codeNatCoreReps cx.P cx.cert cx.feat fsh b = true) ∧
          ∀ kc ρ J d, Fir.evalAlts cx.P kc ρ J k alts d = Fir.eval cx.P kc ρ J b) ∧
      (altEs.find? (·.1 == k) = none →
        ∀ kc ρ J d, Fir.evalAlts cx.P kc ρ J k alts d =
          match d with | some dc => Fir.eval cx.P kc ρ J dc | none => .stuck)
  | [], st, st1, altEs, k, h => by
    simp only [tAltsE, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ hp => by simp at hp, fun _ kc ρ J d => Fir.evalAlts_nil cx.P kc ρ J k d⟩
  | .mk k' b :: rest, st, st1, altEs, k, h => by
    unfold tAltsE at h
    obtain ⟨be, sMid, hb, h⟩ := tBind_step_inv h
    obtain ⟨re, sEnd, hr, h⟩ := tBind_step_inv h
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hle1 := (tCodeE_spec hb).1
    have hle2 := (tAltsE_spec hr).1
    obtain ⟨ihSome, ihNone⟩ := tAltsE_find_sound (k := k) hr
    constructor
    · intro p hp
      simp only [List.find?_cons] at hp
      by_cases hk : k' = k
      · have hbeq : (k' == k) = true := beq_iff_eq.mpr hk
        simp only [hbeq, Option.some.injEq] at hp
        subst hp
        subst hk
        refine ⟨b, st, sMid, by simp [Code.altsSize], hb, Nat.le_refl _,
          fun g hg => hle2.lifted g hg, hle2.demand,
          fun hok => by cases hok with | cons hbOk _ => exact hbOk,
          fun hpn => by simp only [altsParamsNodup, Bool.and_eq_true] at hpn; exact hpn.1,
          fun hnw => by simp only [altsNoWordPrims, Bool.and_eq_true] at hnw; exact hnw.1,
          fun hcr => by simp only [altsNatCoreReps, Bool.and_eq_true] at hcr; exact hcr.1,
          fun kc ρ J d => by rw [Fir.evalAlts_cons]; simp⟩
      · have hbeq : (k' == k) = false := beq_false_of_ne hk
        simp only [hbeq] at hp
        obtain ⟨b', stA, stB, hsz, hcode, hleA, hlifB, hdemB, hokB, hpnB, hnwB, hcrB, hev⟩ :=
          ihSome p hp
        refine ⟨b', stA, stB, by simp only [Code.altsSize]; omega, hcode,
          Nat.le_trans hle1.nextLocal hleA, hlifB, hdemB,
          fun hok => hokB (by cases hok with | cons _ hrOk => exact hrOk),
          fun hpn => hpnB (by simp only [altsParamsNodup, Bool.and_eq_true] at hpn; exact hpn.2),
          fun hnw => hnwB (by simp only [altsNoWordPrims, Bool.and_eq_true] at hnw; exact hnw.2),
          fun hcr => hcrB (by simp only [altsNatCoreReps, Bool.and_eq_true] at hcr; exact hcr.2),
          fun kc ρ J d => by rw [Fir.evalAlts_cons]; simp only [hk, ↓reduceIte]; exact hev kc ρ J d⟩
    · intro hnone kc ρ J d
      simp only [List.find?_cons] at hnone
      by_cases hk : k' = k
      · have hbeq : (k' == k) = true := beq_iff_eq.mpr hk
        simp [hbeq] at hnone
      · have hbeq : (k' == k) = false := beq_false_of_ne hk
        simp only [hbeq] at hnone
        rw [Fir.evalAlts_cons]
        simp only [hk, ↓reduceIte]
        exact ihNone hnone kc ρ J d

omit [Field F] [DecidableEq F] in
private theorem tOptE_none_inv {cx : TCx} {fid : FunId} {fsh : FunShapes} {retR : Rep}
    {vm : TVarMap} {jenv : List TJEntry} {nz : List Var} {offs : OffMap}
    {st st' : TState} {res : Option Lower.Expr}
    (h : tOptE cx fid fsh retR vm jenv nz offs none st = .ok (res, st')) :
    res = none ∧ st' = st := by
  simp only [tOptE, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

omit [Field F] [DecidableEq F] in
private theorem tOptE_some_inv {cx : TCx} {fid : FunId} {fsh : FunShapes} {retR : Rep}
    {vm : TVarMap} {jenv : List TJEntry} {nz : List Var} {offs : OffMap}
    {c : Code} {st st' : TState} {res : Option Lower.Expr}
    (h : tOptE cx fid fsh retR vm jenv nz offs (some c) st = .ok (res, st')) :
    ∃ ce, tCodeE cx fid fsh retR vm jenv nz offs c st = .ok (ce, st') ∧ res = some ce := by
  unfold tOptE at h
  obtain ⟨ce, s1, hc, h⟩ := tBind_step_inv h
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨ce, hc, rfl⟩

/-- Depth-indexed inductive invariant for typed `Fir.Code` backward simulation. -/
def TCodeSoundAt (P : Program) (cert : ShapeCert) (sched : CircuitSchedule)
    (lp : LoweredProgram) (world : World F) (d : Nat) : Prop :=
  ∀ (fid : FunId) (fsh : FunShapes) (retR : Rep)
    (vm : TVarMap) (jenv : List TJEntry) (nz : List Var) (offs : OffMap)
    (c : Code) (st st' : TState) (e : Lower.Expr)
    (ρ : Env) (J : List Fir.JEntry) (locals : Environment F Nat)
    (h : Heap F) (r : SourceValue F) (h' : Heap F),
    let feat := scanFeatures P
    retR = repOf P cert feat fsh.ret →
    isNatCoreRep retR = true →
    CodeOk P cert fsh c →
    codeParamsNodup c = true →
    codeNoWordPrims c = true →
    codeNatCoreReps P cert feat fsh c = true →
    (∀ p ∈ vm, isNatCoreRep p.2.2 = true) →
    (∀ ji ∈ jenv, ∀ pr ∈ ji.paramReps, isNatCoreRep pr = true) →
    tCodeE { P, cert, feat, sched } fid fsh retR vm jenv nz offs c st = .ok (e, st') →
    DemandLe st'.demand lp.demand →
    AllLocalLt st.nextLocal (vm.map fun p => p.2.1) →
    AllLocalLt st.nextLocal (jenv.flatMap fun je => je.capVars.map Prod.fst) →
    AllLocalLt st.nextLocal (offs.map fun p => p.2.1) →
    (∀ g ∈ st'.lifted,
      isCleanNoU32 g.body = true ∧
      WorldHasFn world (qualified g.name) (g.params.map Prod.fst)
        (qualifyExprF F (Peephole.rewriteExpr g.body))) →
    EnvOk cert dummyEnc fsh ρ →
    TEnvRel P cert feat h fsh vm ρ locals →
    TJEnvRel P cert feat world d h fsh jenv J locals →
    NzRel ρ nz →
    OffsRel ρ locals offs →
    EvalExprN world d [] locals (qualifyExprF F e) h r h' →
    ∃ k v, Fir.eval P k ρ J c = .ok v ∧
      TVR P cert feat h' retR v r

/-- Derive `TFunSoundN P cert (scanFeatures P) world d` from `∀ d' < d, TCodeSoundAt ... d'`. -/
theorem tFunSoundN_of_tCodeSound {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (lw : TypedLoweredWorld P cert sched lp world)
    (hnc : natCoreProgram P cert = true) {d : Nat}
    (hCode : ∀ d' < d, TCodeSoundAt P cert sched lp world d') :
    TFunSoundN P cert (scanFeatures P) world d := by
  intro d' hd' f fd hfun hsz vs ws h r h' htvrs hvsOk evFn
  have hchk := natCoreProgram_checked hnc
  obtain ⟨hpsOk, hbodyOk⟩ := hchk.funs f fd hfun
  obtain ⟨hpsNodup, hcodeNd, hcodeNoW, hretCore, hparamCore, hcodeCore⟩ :=
    natCoreProgram_funInfo hnc hfun hsz
  obtain ⟨baseIdx, stIn, stOut, body, hnl, _, hcode, hdemLp, hbodyClean, hwfMain, hwfLifted⟩ :=
    lw.hasFun hnc hfun hsz
  set feat := scanFeatures P
  set fsh := cert.fn f
  set ps := fd.params.map Prod.fst
  set paramReps := ps.map fun p => repOf P cert feat (fsh.var p)
  set pns := (List.range fd.params.length).map (fun k => localName (baseIdx + k))
  set initOffs : OffMap :=
    (ps.zip (pns.zip paramReps)).filterMap fun (p, nm, r) =>
      match r with | .nat _ => some (p, (nm, 0)) | _ => none
  obtain ⟨hwslen, evBody⟩ := evalFnN_rewritten_clean_inv hwfMain hbodyClean evFn
  have hpnsLen : ps.length = pns.length := by simp [ps, pns]
  have hpnsNodup : pns.Nodup :=
    List.Nodup.map (fun _ _ heq => by have := localName_inj heq; omega) List.nodup_range
  have hvslen : vs.length = fd.params.length := by
    have := htvrs.length_eq
    simp only [paramReps, ps, List.length_map] at this
    omega
  have henv0 : TEnvRel P cert feat h fsh [] .leaf [] :=
    { rep_eq := fun _ _ _ h => (by cases h), rel := fun _ _ _ _ h _ => (by cases h) }
  have henv : TEnvRel P cert feat h fsh (bindTVm [] ps (pns.zip paramReps))
      (Fir.bindAll .leaf ps vs) (pns.zip ws) := by
    simpa using TEnvRel.bindTVm_append hpnsLen hpnsNodup (by simp) (by simp) henv0 htvrs
  have hvmCore : ∀ p ∈ bindTVm [] ps (pns.zip paramReps), isNatCoreRep p.2.2 = true := by
    intro p hp
    rcases bindTVm_mem hp with h1 | ⟨_, _, nr, hnr, rfl⟩
    · cases h1
    · obtain ⟨q, hq, hqEq⟩ := List.mem_map.mp (List.of_mem_zip hnr).2
      rw [← hqEq]; exact hparamCore q hq
  have hpnsLt : AllLocalLt stIn.nextLocal pns := by
    intro s hs
    simp only [pns, List.mem_map, List.mem_range] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    exact ⟨baseIdx + k, by omega, rfl⟩
  have hlocVm : AllLocalLt stIn.nextLocal ((bindTVm [] ps (pns.zip paramReps)).map fun p => p.2.1) := by
    apply AllLocalLt_bindTVm (n := 0) (by intro s hs; cases hs) _ (Nat.zero_le _)
    intro s hs
    obtain ⟨nr, hnr, rfl⟩ := List.mem_map.mp hs
    exact hpnsLt _ (List.of_mem_zip hnr).1
  have hlocJ : AllLocalLt stIn.nextLocal (([] : List TJEntry).flatMap fun je => je.capVars.map Prod.fst) := by
    intro s hs; simp at hs
  have hlocOffs : AllLocalLt stIn.nextLocal (initOffs.map fun p => p.2.1) :=
    AllLocalLt_initOffs hpnsLt
  have hEnvOk : EnvOk cert dummyEnc fsh (Fir.bindAll .leaf ps vs) :=
    Fir.Proof.Shape.envOk_bindAll ps fsh.params vs .leaf (Fir.Proof.Shape.envOk_leaf cert dummyEnc fsh)
      hpsOk hvsOk
  have hoffs : OffsRel (Fir.bindAll .leaf ps vs) (pns.zip ws) initOffs := by
    simpa using OffsRel.of_initOffs (base := ([] : Environment F Nat))
      hpsNodup hpnsLen hpnsNodup (by simp) htvrs
  have hnz : NzRel (Fir.bindAll .leaf ps vs) [] := fun _ hx => by cases hx
  obtain ⟨k, v, heval, htvr⟩ := hCode d' hd' f fsh (repOf P cert feat fsh.ret)
    (bindTVm [] ps (pns.zip paramReps)) [] [] initOffs fd.body stIn stOut body
    (Fir.bindAll .leaf ps vs) [] (pns.zip ws) h r h'
    rfl hretCore hbodyOk hcodeNd hcodeNoW hcodeCore hvmCore (fun _ hm => by cases hm)
    hcode hdemLp hlocVm hlocJ hlocOffs hwfLifted hEnvOk henv .nil hnz hoffs evBody
  refine ⟨k + 1, v, ?_, htvr⟩
  rw [Fir.evalCall_of P (k + 1) hfun]
  simp only [Fir.callFun, hvslen, ↓reduceIte, Sem.later]
  exact heval

/-- **Master Backward Simulation Theorem for `TypedLower.tCodeE`** across all call depths `d`. -/
theorem eval_tCodeE_sound_N {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld P cert sched lp world)
    (hnc : natCoreProgram P cert = true) :
    ∀ d : Nat, TCodeSoundAt P cert sched lp world d := by
  have hchk := natCoreProgram_checked hnc
  have hwf := hchk.wf
  have hkeys := lw.ctors_keys_nodup
  have hnd := lw.ctors_names_nodup
  have hdatas := natCoreProgram_datasNatCoreReps hnc
  set feat := scanFeatures P
  set cx : TCx := { P, cert, feat, sched }
  intro d
  induction d using Nat.strongRecOn with
  | _ d ihD =>
    have hFunSound : TFunSoundN P cert feat world d := tFunSoundN_of_tCodeSound lw hnc ihD
    have bySize : ∀ (n : Nat) (c : Code), c.size = n →
        ∀ fid fsh retR vm jenv nz offs st st' e ρ J locals h r h',
          retR = repOf P cert feat fsh.ret →
          isNatCoreRep retR = true →
          CodeOk P cert fsh c →
          codeParamsNodup c = true →
          codeNoWordPrims c = true →
          codeNatCoreReps P cert feat fsh c = true →
          (∀ p ∈ vm, isNatCoreRep p.2.2 = true) →
          (∀ ji ∈ jenv, ∀ pr ∈ ji.paramReps, isNatCoreRep pr = true) →
          tCodeE cx fid fsh retR vm jenv nz offs c st = .ok (e, st') →
          DemandLe st'.demand lp.demand →
          AllLocalLt st.nextLocal (vm.map fun p => p.2.1) →
          AllLocalLt st.nextLocal (jenv.flatMap fun je => je.capVars.map Prod.fst) →
          AllLocalLt st.nextLocal (offs.map fun p => p.2.1) →
          (∀ g ∈ st'.lifted,
            isCleanNoU32 g.body = true ∧
            WorldHasFn world (qualified g.name) (g.params.map Prod.fst)
              (qualifyExprF F (Peephole.rewriteExpr g.body))) →
          EnvOk cert dummyEnc fsh ρ →
          TEnvRel P cert feat h fsh vm ρ locals →
          TJEnvRel P cert feat world d h fsh jenv J locals →
          NzRel ρ nz →
          OffsRel ρ locals offs →
          EvalExprN world d [] locals (qualifyExprF F e) h r h' →
          ∃ k v, Fir.eval P k ρ J c = .ok v ∧ TVR P cert feat h' retR v r := by
      intro n
      induction n using Nat.strongRecOn with
      | _ n ihS =>
        intro c hcsz fid fsh retR vm jenv nz offs st st' e ρ J locals h r h'
          hretEq hretCore hCodeOk hcpNd hnoW hcore hvmCore hjCore hcode hdemLp
          hlocVm hlocJ hlocOffs hLifted hEnvOk henv hjenv hnz hoffs ev
        cases c with
        | bind x rhs k =>
          cases hCodeOk with
          | bind hrhsOk hkOk =>
            unfold tCodeE at hcode
            obtain ⟨s1, hle1, _, _, hcode⟩ := markRep_step_inv hcode
              (fun _ => rfl) (fun _ => rfl)
              (fun r _ h1 h2 => by cases r <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2)
            obtain ⟨⟨re, xOff?⟩, s2, hrhs, hcode⟩ := tBind_step_inv hcode
            obtain ⟨hle3, hcode⟩ := tFreshLocal_step_inv hcode (fun _ => rfl)
            obtain ⟨ke, s4, hk, hcode⟩ := tBind_step_inv hcode
            simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hcode
            obtain ⟨rfl, rfl⟩ := hcode
            simp only [letE, qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
              Aiur.Generic.Pattern.map] at ev
            obtain ⟨w1, hm, evRhs, evK⟩ := evalExprN_let_bind_inv ev
            have hle2 := (tRhsE_spec hrhs).1
            have hle4 := (tCodeE_spec hk).1
            have hdemS2 : DemandLe s2.demand lp.demand :=
              ((hle3.demand.trans hle4.demand).trans hdemLp)
            have hstLeS2 : st.nextLocal ≤ s2.nextLocal := (hle1.trans hle2).nextLocal
            have hfreshVm : localName s2.nextLocal ∉ vm.map (fun p => p.2.1) :=
              (hlocVm.mono hstLeS2).not_mem (Nat.le_refl _)
            have hfreshJ : localName s2.nextLocal ∉ jenv.flatMap (fun je => je.capVars.map Prod.fst) :=
              (hlocJ.mono hstLeS2).not_mem (Nat.le_refl _)
            have hfreshOffs : localName s2.nextLocal ∉ offs.map (fun p => p.2.1) :=
              (hlocOffs.mono hstLeS2).not_mem (Nat.le_refl _)
            simp only [codeParamsNodup, codeNoWordPrims, codeNatCoreReps, Bool.and_eq_true] at hcpNd hnoW hcore
            have hrxCore : isNatCoreRep (repOf P cert feat (fsh.var x)) = true := hcore.1
            have hvmCore' : ∀ p ∈ ((x, localName s2.nextLocal, repOf P cert feat (fsh.var x)) :: vm),
                isNatCoreRep p.2.2 = true := by
              intro p hp
              rcases List.mem_cons.mp hp with rfl | htl
              · exact hrxCore
              · exact hvmCore p htl
            have hlocVm' : AllLocalLt (s2.nextLocal + 1)
                (((x, localName s2.nextLocal, repOf P cert feat (fsh.var x)) :: vm).map fun p => p.2.1) := by
              intro s hs
              simp only [List.map_cons, List.mem_cons] at hs
              rcases hs with rfl | htl
              · exact ⟨s2.nextLocal, by omega, rfl⟩
              · exact hlocVm.mono (by omega) s htl
            have hlocJ' : AllLocalLt (s2.nextLocal + 1)
                (jenv.flatMap fun je => je.capVars.map Prod.fst) :=
              hlocJ.mono (by omega)
            have hkSize : k.size < n := by rw [← hcsz]; simp [Code.size]
            by_cases hcall : ∃ g as, rhs = .call g as
            · obtain ⟨g, as, rfl⟩ := hcall
              unfold tRhsE at hrhs
              dsimp only [cx] at hrhs
              cases hfun : P.fun? g with
              | none => simp only [hfun] at hrhs; exact False.elim (tLift_throw_elim hrhs (fun _ _ => rfl))
              | some gd =>
                simp only [hfun] at hrhs
                by_cases hsz : g < P.size
                · simp only [hsz, ↓reduceIte] at hrhs
                  by_cases har : (as.length == gd.params.length) = true
                  · simp only [har, ↓reduceIte] at hrhs
                    obtain ⟨argEs, s2a, hmap, hrhs⟩ := tBind_step_inv hrhs
                    obtain ⟨eCo, s2b, hco, hrhs⟩ := tBind_step_inv hrhs
                    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrhs
                    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrhs
                    obtain ⟨hArgsOk, hRetImp⟩ := Fir.Proof.Shape.rhsOk_call_inv dummyEnc hrhsOk
                    obtain ⟨hgParamsOk, _⟩ := hchk.funs g gd hfun
                    have hgParamsEq : (cert.fn g).params = (gd.params.map Prod.fst).map (cert.fn g).var :=
                      paramsOk_eq_map hgParamsOk
                    obtain ⟨_, _, _, hgRetCore, hgParamCore, _⟩ := natCoreProgram_funInfo hnc hfun hsz
                    have hσsCore : ∀ σ ∈ (cert.fn g).params, isNatCoreRep (repOf P cert feat σ) = true := by
                      intro σ hσ
                      rw [hgParamsEq] at hσ
                      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hσ
                      exact hgParamCore p hp
                    have hmap' : ((as.zip ((cert.fn g).params.map fun σ => repOf P cert feat σ)).mapM
                        (m := TLowerM) fun (a, pr) => tArgE cx vm a pr) s1 = .ok (argEs, s2a) := by
                      have hrepsEq : ((cert.fn g).params.map fun σ => repOf P cert feat σ) =
                          (gd.params.map Prod.fst).map (fun p => cx.rep ((cx.funShapes g).var p)) := by
                        rw [hgParamsEq, List.map_map]; rfl
                      rwa [hrepsEq]
                    have hdemS2a : DemandLe s2a.demand lp.demand :=
                      (coerceE_spec hco).1.demand.trans hdemS2
                    obtain ⟨v1, ⟨vs, hvs, k1, hcall1, hv1Ok⟩, htvr1, ext12⟩ :=
                      eval_coerceE fc lw hwf hkeys hnd hdatas hco hgRetCore hrxCore hdemS2 evRhs
                        (Q := fun v => ∃ vs, evalArgs ρ as = some vs ∧
                          ∃ k1, Fir.evalCall P k1 g vs = .ok v ∧ ValOk cert dummyEnc (fsh.var x) v)
                        (fun w0 hm0 evCall => by
                          simp only [callE, qualifyExprF, qualifyExpr, qualifyName_funName,
                            Option.map_some, Aiur.Generic.Expr.map, List.map_map] at evCall
                          obtain ⟨d', ws, hm1, hd', hargsEv, hcal⟩ := evalExprN_call_inv evCall
                          have hargsEv' : EvalArgsN world d [] locals (argEs.map (qualifyExprF F)) h ws hm1 :=
                            hargsEv
                          obtain ⟨vs, hvs, hvsOk, htvrs, ext1⟩ :=
                            eval_tArgEs fc lw hwf hkeys hnd hdatas hvmCore hEnvOk
                              hArgsOk hσsCore hmap' hdemS2a henv hargsEv'
                          have htvrs' : TVRs P cert feat hm1
                              ((gd.params.map Prod.fst).map fun p => repOf P cert feat ((cert.fn g).var p))
                              vs ws := by
                            simpa [feat, hgParamsEq, List.map_map, Function.comp_def] using htvrs
                          obtain ⟨k1, v1, hcall1, htvr1⟩ :=
                            hFunSound d' hd' g gd hfun hsz vs ws hm1 w0 hm0 htvrs' hvsOk hcal
                          have hv1Ok := hRetImp v1 (evalCall_valOk hchk hsz hvsOk hcall1)
                          exact ⟨v1, ⟨vs, hvs, k1, hcall1, hv1Ok⟩, htvr1, ext1.trans hcal.heap_extends⟩)
                        (fun _ ⟨_, _, _, _, hvOk⟩ => CoerceTargetOk.of_valOk hvOk)
                    have henv' := (henv.extend ext12).cons_fresh hfreshVm rfl htvr1
                    have hjenv' := (hjenv.extend ext12).cons_unused (wx := w1) hfreshJ
                    have hnz' := hnz.filter_ne x v1
                    have hoffs' := hoffs.update (x := x) (nx := localName s2b.nextLocal) (v := v1)
                      (w1 := w1) (xOff? := none) hfreshOffs (fun _ _ h0 => by cases h0)
                    have hlocOffs' := AllLocalLt_offs_update (m := s2b.nextLocal + 1) hlocVm hlocOffs
                      (x := x) (xOff? := none) (fun _ _ h0 => by cases h0) (by omega)
                    have hEnvOk' := Fir.Proof.Shape.envOk_insert hEnvOk hv1Ok
                    obtain ⟨k2, v2, heval2, htvr2⟩ :=
                      ihS k.size hkSize k rfl fid fsh retR _ jenv _ _ _ s4 ke
                        (ρ.insert x v1) J ((localName s2b.nextLocal, w1) :: locals) hm r h'
                        hretEq hretCore hkOk hcpNd hnoW.2 hcore.2 hvmCore' hjCore hk hdemLp
                        hlocVm' hlocJ' hlocOffs' hLifted hEnvOk' henv' hjenv' hnz' hoffs' evK
                    refine ⟨max k1 k2, v2, ?_, htvr2⟩
                    rw [Fir.eval_bindCall, hvs]
                    simp only [Sem.Result.ofOption, Sem.Result.bind_ok]
                    rw [FirFacts.evalCall_mono P hcall1 (Nat.le_max_left k1 k2)]
                    simp only [Sem.Result.bind_ok]
                    exact FirFacts.eval_mono P heval2 (Nat.le_max_right k1 k2)
                  · have harf : (as.length == gd.params.length) = false := Bool.eq_false_iff.mpr har
                    simp only [harf, Bool.false_eq_true, ↓reduceIte] at hrhs
                    obtain ⟨_, _, h1, _⟩ := tBind_step_inv hrhs
                    exact False.elim (tLift_throw_elim h1 (fun _ _ => rfl))
                · simp only [hsz, ↓reduceIte] at hrhs
                  obtain ⟨_, _, h1, _⟩ := tBind_step_inv hrhs
                  exact False.elim (tLift_throw_elim h1 (fun _ _ => rfl))
            · have hnotCall : ∀ g as, rhs ≠ .call g as := fun g as heq => hcall ⟨g, as, heq⟩
              have hnoWR : noWordRhs rhs = true := by cases rhs <;> exact hnoW.1
              obtain ⟨v1, hEvalRhs, hv1Ok, htvr1, ext1, hxOff⟩ :=
                eval_tRhsE_noncall fc lw hwf hkeys hnd hdatas hnoWR hrhsOk hEnvOk hvmCore
                  (hlocVm.mono hle1.nextLocal) hrxCore hrhs hdemS2 henv hnz hoffs hnotCall evRhs
              have henv' := (henv.extend ext1).cons_fresh hfreshVm rfl htvr1
              have hjenv' := (hjenv.extend ext1).cons_unused (wx := w1) hfreshJ
              have hnz' := hnz.filter_ne x v1
              have hoffs' := hoffs.update (x := x) (nx := localName s2.nextLocal) (v := v1)
                (w1 := w1) (xOff? := xOff?) hfreshOffs (fun baseNm d0 ho => by
                  obtain ⟨hmem, n0, hvEq, hn0, hbase⟩ := hxOff baseNm d0 ho
                  have hneNx : localName s2.nextLocal ≠ baseNm := by
                    intro heq; subst heq
                    rcases hmem with hm1 | hm2
                    · exact hfreshVm hm1
                    · exact hfreshOffs hm2
                  exact ⟨hneNx, n0, hvEq, hn0, hbase⟩)
              have hlocOffs' := AllLocalLt_offs_update (m := s2.nextLocal + 1) hlocVm hlocOffs
                (x := x) (xOff? := xOff?) (fun baseNm d0 ho => (hxOff baseNm d0 ho).1) (by omega)
              have hEnvOk' := Fir.Proof.Shape.envOk_insert hEnvOk hv1Ok
              cases xOff? <;>
                (obtain ⟨k2, v2, heval2, htvr2⟩ :=
                  ihS k.size hkSize k rfl fid fsh retR _ jenv _ _ _ s4 ke
                    (ρ.insert x v1) J ((localName s2.nextLocal, w1) :: locals) hm r h'
                    hretEq hretCore hkOk hcpNd hnoW.2 hcore.2 hvmCore' hjCore hk hdemLp
                    hlocVm' hlocJ' hlocOffs' hLifted hEnvOk' henv' hjenv' hnz' hoffs' evK;
                 refine ⟨k2, v2, ?_, htvr2⟩;
                 rw [Fir.eval_bindRhs P k2 ρ J x rhs k hnotCall, hEvalRhs];
                 exact heval2)
        | jp j ps isRec body k =>
          cases hCodeOk with
          | jp hpsOk hbodyOk hkOk =>
            simp only [codeParamsNodup, codeNoWordPrims, codeNatCoreReps, Bool.and_eq_true] at hcpNd hnoW hcore
            have hpsNodup : ps.Nodup := (Lower.allDistinct_iff_nodup ps).mp hcpNd.1.1
            have hpsCore : ∀ p ∈ ps, isNatCoreRep (repOf P cert feat (fsh.var p)) = true :=
              List.all_eq_true.mp hcore.1.1
            unfold tCodeE at hcode
            obtain ⟨hle1, hcode⟩ := tFreshJp_step_inv hcode (fun _ => rfl)
            obtain ⟨s2, hle2, _, _, hcode⟩ := forIn_markRep_step_inv (g := Prod.snd) hcode
              (fun _ => rfl) (fun _ => rfl)
              (fun r _ h1 h2 => by cases r <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2)
            obtain ⟨s3, hle3, _, _, hcode⟩ := forIn_markRep_step_inv (g := id) hcode
              (fun _ => rfl) (fun _ => rfl)
              (fun r _ h1 h2 => by cases r <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2)
            obtain ⟨s4, hle4, _, _, hcode⟩ := markRep_step_inv hcode
              (fun _ => rfl) (fun _ => rfl)
              (fun r _ h1 h2 => by cases r <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2)
            obtain ⟨hle5, hcode⟩ := tFreshLocals_step_inv hcode (fun _ => rfl) (fun _ _ => rfl)
            obtain ⟨bodyExpr, s6, hbody, hcode⟩ := tBind_step_inv hcode
            obtain ⟨hle7, hk⟩ := tEmitLifted_step_inv hcode (fun _ _ => rfl)
            -- Abstract private `collectJpCaptures` and `tBindVm` via polymorphic helpers.
            have hCapSpec : ∀ (fCap : TVarMap → List TJEntry → List Var → JoinId → Bool → Code → Bool → List (String × Rep)),
                (∀ vm jenv ps j isRec body fc,
                  ((fCap vm jenv ps j isRec body fc).map Prod.fst).Nodup ∧
                  ∀ p ∈ fCap vm jenv ps j isRec body fc,
                    p ∈ (vm.map fun (q : Var × String × Rep) => q.2) ++ jenv.flatMap TJEntry.capVars) →
                ∀ (fBV : TVarMap → List Var → List (String × Rep) → TVarMap),
                (∀ vm ps nrs, fBV vm ps nrs = bindTVm vm ps nrs) →
                let capVars := fCap vm jenv ps j isRec body cx.sched.filterJpCaptures
                let jpName := jpFunName fid st.nextJp
                let paramReps := ps.map fun p => cx.rep (fsh.var p)
                let pns := (List.range ps.length).map fun i => localName (s4.nextLocal + i)
                let ji : TJEntry := ⟨j, jpName, capVars, paramReps, retR⟩
                let bodyVm := fBV vm ps (pns.zip paramReps)
                let bodyJenv := if isRec then ji :: jenv else jenv
                let bodyNz := nz.filter fun v => !ps.contains v
                let bodyOffs : OffMap :=
                  (ps.zip (pns.zip paramReps)).filterMap fun (p, nm, r) =>
                    match r with | .nat _ => some (p, (nm, 0)) | _ => none
                let liftedFn : Lower.Fn := {
                  name := jpName
                  params := capVars.map (fun (nm, r) => (nm, r.aiurTy)) ++
                    (pns.zip paramReps).map (fun (nm, r) => (nm, r.aiurTy))
                  result := retR.aiurTy
                  body := bodyExpr
                  isInline := shouldInlineJp cx.sched j isRec body k
                }
                tCodeE cx fid fsh retR bodyVm bodyJenv bodyNz bodyOffs body
                  { s4 with nextLocal := s4.nextLocal + ps.length } = .ok (bodyExpr, s6) →
                tCodeE cx fid fsh retR vm (ji :: jenv) nz offs k
                  { s6 with lifted := s6.lifted ++ [liftedFn] } = .ok (e, st') →
                ∃ kOut vOut, Fir.eval P kOut ρ J (.jp j ps isRec body k) = .ok vOut ∧
                  TVR P cert feat h' retR vOut r := by
              intro fCap hCap fBV hBV capVars jpName paramReps pns ji bodyVm bodyJenv bodyNz bodyOffs
                liftedFn hbody' hk'
              have hbodyVmEq : bodyVm = bindTVm vm ps (pns.zip paramReps) := hBV _ _ _
              obtain ⟨hcapNodup, hcapMem⟩ := hCap vm jenv ps j isRec body cx.sched.filterJpCaptures
              have hlePre : TStateLe st s4 := ((hle1.trans hle2).trans hle3).trans hle4
              have hle6 := (tCodeE_spec hbody').1
              have hle8 := (tCodeE_spec hk').1
              have hdem6 : DemandLe s6.demand lp.demand := (hle7.demand.trans hle8.demand).trans hdemLp
              have hlocCap : AllLocalLt st.nextLocal (capVars.map Prod.fst) := by
                intro s hs
                obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
                rcases List.mem_append.mp (hcapMem p hp) with h1 | h2
                · obtain ⟨q, hq, hqEq⟩ := List.mem_map.mp h1
                  exact hlocVm _ (List.mem_map.mpr ⟨q, hq, congrArg Prod.fst hqEq⟩)
                · obtain ⟨je, hje, hpe⟩ := List.mem_flatMap.mp h2
                  exact hlocJ _ (List.mem_flatMap.mpr ⟨je, hje, List.mem_map.mpr ⟨p, hpe, rfl⟩⟩)
              have hpnsLen : ps.length = pns.length := by simp [pns]
              have hpnsNodup : pns.Nodup :=
                List.Nodup.map (fun _ _ heq => by have := localName_inj heq; omega) List.nodup_range
              have hpnsLt : AllLocalLt (s4.nextLocal + ps.length) pns := by
                intro s hs
                simp only [pns, List.mem_map, List.mem_range] at hs
                obtain ⟨idx, hidx, rfl⟩ := hs
                exact ⟨s4.nextLocal + idx, by omega, rfl⟩
              have hpnsNotInCap : ∀ p ∈ pns, p ∉ capVars.map Prod.fst := by
                intro p hp hmem
                simp only [pns, List.mem_map, List.mem_range] at hp
                obtain ⟨idx, _, rfl⟩ := hp
                exact (hlocCap.mono hlePre.nextLocal).not_mem (by omega) hmem
              have hpnsNotInVm : ∀ p ∈ pns, p ∉ vm.map (fun q => q.2.1) := by
                intro p hp hmem
                simp only [pns, List.mem_map, List.mem_range] at hp
                obtain ⟨idx, _, rfl⟩ := hp
                exact (hlocVm.mono hlePre.nextLocal).not_mem (by omega) hmem
              have hpnsNotInJ : ∀ p ∈ pns, p ∉ jenv.flatMap (fun je => je.capVars.map Prod.fst) := by
                intro p hp hmem
                simp only [pns, List.mem_map, List.mem_range] at hp
                obtain ⟨idx, _, rfl⟩ := hp
                exact (hlocJ.mono hlePre.nextLocal).not_mem (by omega) hmem
              have hwfLiftedBody : ∀ g ∈ s6.lifted,
                  isCleanNoU32 g.body = true ∧
                  WorldHasFn world (qualified g.name) (g.params.map Prod.fst)
                    (qualifyExprF F (Peephole.rewriteExpr g.body)) := by
                intro g hg
                exact hLifted g (hle8.lifted g (List.mem_append_left _ hg))
              have hwfJpRaw : isCleanNoU32 liftedFn.body = true ∧
                  WorldHasFn world (qualified liftedFn.name) (liftedFn.params.map Prod.fst)
                    (qualifyExprF F (Peephole.rewriteExpr liftedFn.body)) :=
                hLifted liftedFn (hle8.lifted liftedFn (List.mem_append_right _ List.mem_cons_self))
              have hliftedParams : liftedFn.params.map Prod.fst = capVars.map Prod.fst ++ pns := by
                simp only [liftedFn, List.map_append, List.map_map]
                congr 1
                have hlenZip : pns.length = paramReps.length := by simp [pns, paramReps]
                change (pns.zip paramReps).map Prod.fst = pns
                exact List.map_fst_zip (Nat.le_of_eq hlenZip)
              have hbodyClean : isCleanNoU32 bodyExpr = true := hwfJpRaw.1
              have hwfJp : WorldHasFn world (qualified jpName) (capVars.map Prod.fst ++ pns)
                  (qualifyExprF F (Peephole.rewriteExpr bodyExpr)) := by
                simpa [liftedFn, hliftedParams] using hwfJpRaw.2
              have hparamRepsCore : ∀ pr ∈ paramReps, isNatCoreRep pr = true := by
                intro pr hpr
                obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hpr
                exact hpsCore p hp
              have hbodyVmCore : ∀ p ∈ bodyVm, isNatCoreRep p.2.2 = true := by
                rw [hbodyVmEq]
                intro p hp
                rcases bindTVm_mem hp with h1 | ⟨_, _, nr, hnr, rfl⟩
                · exact hvmCore p h1
                · exact hparamRepsCore nr.2 (List.of_mem_zip hnr).2
              have hjCoreCons : ∀ ji' ∈ (ji :: jenv), ∀ pr ∈ ji'.paramReps, isNatCoreRep pr = true := by
                intro ji' hji'
                rcases List.mem_cons.mp hji' with rfl | htl
                · exact hparamRepsCore
                · exact hjCore ji' htl
              have hjCoreBody : ∀ ji' ∈ bodyJenv, ∀ pr ∈ ji'.paramReps, isNatCoreRep pr = true := by
                dsimp only [bodyJenv]
                cases isRec
                · exact hjCore
                · exact hjCoreCons
              have hlePreNl : st.nextLocal ≤ s4.nextLocal := hlePre.nextLocal
              have hlocVmBody : AllLocalLt (s4.nextLocal + ps.length) (bodyVm.map fun p => p.2.1) := by
                rw [hbodyVmEq]
                apply AllLocalLt_bindTVm hlocVm _ (by omega)
                intro s hs
                obtain ⟨nr, hnr, rfl⟩ := List.mem_map.mp hs
                exact hpnsLt _ (List.of_mem_zip hnr).1
              have hlocJBody : AllLocalLt (s4.nextLocal + ps.length)
                  (bodyJenv.flatMap fun je => je.capVars.map Prod.fst) := by
                dsimp only [bodyJenv]
                cases isRec
                · exact hlocJ.mono (by omega)
                · intro s hs
                  rcases List.mem_append.mp hs with h1 | h2
                  · exact hlocCap.mono (by omega) s h1
                  · exact hlocJ.mono (by omega) s h2
              have hlocOffsBody : AllLocalLt (s4.nextLocal + ps.length) (bodyOffs.map fun p => p.2.1) :=
                AllLocalLt_initOffs hpnsLt
              set je : Fir.JEntry := { id := j, charged := false, env := ρ, params := ps, body := body, isRec := isRec }
              -- Inner strong induction on call depth `m < d` for `jiSound` (handles recursive join points).
              have jiSound : ∀ m < d, ∀ h1, Heap.Extends h h1 →
                  ∀ capWs vs ws r1 h2,
                    EvalCapArgs locals (ji.capVars.map Prod.fst) capWs →
                    TVRs P cert feat h1 ji.paramReps vs ws →
                    ValsOk cert dummyEnc (fsh.join j) vs →
                    EvalFnN world m (qualified ji.fnName) (capWs ++ ws) h1 r1 h2 →
                    ∃ k' v', Fir.eval P k' (Fir.bindAll ρ ps vs) (je.after J) body = .ok v' ∧
                      TVR P cert feat h2 (repOf P cert feat fsh.ret) v' r1 := by
                intro m
                induction m using Nat.strongRecOn with
                | _ m ihM =>
                  intro hmLt h1 ext1 capWs vs ws r1 h2 hcapDef htvrs hvsOk evJp
                  obtain ⟨_, evBody⟩ := evalFnN_rewritten_clean_inv hwfJp hbodyClean evJp
                  have hcapLen : capWs.length = (capVars.map Prod.fst).length := hcapDef.length_eq
                  have hzipEq : (capVars.map Prod.fst ++ pns).zip (capWs ++ ws) =
                      (capVars.map Prod.fst).zip capWs ++ pns.zip ws :=
                    List.zip_append (by omega)
                  rw [hzipEq] at evBody
                  have henvCap : TEnvRel P cert feat h1 fsh vm ρ ((capVars.map Prod.fst).zip capWs) :=
                    (henv.extend ext1).of_capZip hcapNodup hcapDef
                  have hpnsDisjBase : ∀ p ∈ pns, p ∉ ((capVars.map Prod.fst).zip capWs).map Prod.fst := by
                    intro p hp hmem
                    rw [List.map_fst_zip (by omega)] at hmem
                    exact hpnsNotInCap p hp hmem
                  have henvBody : TEnvRel P cert feat h1 fsh bodyVm (Fir.bindAll ρ ps vs)
                      ((capVars.map Prod.fst).zip capWs ++ pns.zip ws) := by
                    rw [hbodyVmEq]
                    exact TEnvRel.bindTVm_append hpnsLen hpnsNodup hpnsDisjBase hpnsNotInVm henvCap htvrs
                  have hdisjJExtra : ∀ p ∈ pns.zip ws,
                      p.1 ∉ jenv.flatMap (fun je => je.capVars.map Prod.fst) :=
                    fun p hp => hpnsNotInJ p.1 (List.of_mem_zip hp).1
                  have hjenvBase : TJEnvRel P cert feat world m h1 fsh jenv J
                      ((capVars.map Prod.fst).zip capWs ++ pns.zip ws) :=
                    (((hjenv.extend ext1).mono_depth (Nat.le_of_lt hmLt)).of_capZip hcapNodup hcapDef).append_right
                      hdisjJExtra
                  have hjenvBody : TJEnvRel P cert feat world m h1 fsh bodyJenv (je.after J)
                      ((capVars.map Prod.fst).zip capWs ++ pns.zip ws) := by
                    dsimp only [bodyJenv]
                    cases hrec : isRec with
                    | false =>
                      simpa [je, Fir.JEntry.after, hrec] using hjenvBase
                    | true =>
                      simp only [je, Fir.JEntry.after, hrec, ↓reduceIte]
                      have hcaRec : CapAgree (ji.capVars.map Prod.fst) locals
                          ((capVars.map Prod.fst).zip capWs ++ pns.zip ws) :=
                        ((CapAgree.refl (capVars.map Prod.fst) locals).of_capZip hcapNodup hcapDef).append_right
                          (fun p hp => hpnsNotInCap p.1 (List.of_mem_zip hp).1)
                      refine .cons rfl (qualifyName_jpFunName fid st.nextJp) hpsOk rfl hretEq hcaRec ?_ hjenvBase
                      intro m' hm' h1' ext1' capWs' vs' ws' r1' h2' hcapDef' htvrs' hvsOk' evRec
                      have hres := ihM m' hm' (Nat.lt_trans hm' hmLt) h1' (ext1.trans ext1')
                        capWs' vs' ws' r1' h2' hcapDef' htvrs' hvsOk' evRec
                      simpa [je, Fir.JEntry.after, hrec] using hres
                  have hEnvOkBody : EnvOk cert dummyEnc fsh (Fir.bindAll ρ ps vs) :=
                    Fir.Proof.Shape.envOk_bindAll ps (fsh.join j) vs ρ hEnvOk hpsOk hvsOk
                  have hnzBody : NzRel (Fir.bindAll ρ ps vs) bodyNz := hnz.filter_bindAll ps vs
                  have hoffsBody : OffsRel (Fir.bindAll ρ ps vs)
                      ((capVars.map Prod.fst).zip capWs ++ pns.zip ws) bodyOffs :=
                    OffsRel.of_initOffs hpsNodup hpnsLen hpnsNodup hpnsDisjBase htvrs
                  obtain ⟨k', v', hevB, htvrB⟩ := ihD m hmLt fid fsh retR bodyVm bodyJenv bodyNz bodyOffs
                    body _ s6 bodyExpr (Fir.bindAll ρ ps vs) (je.after J)
                    ((capVars.map Prod.fst).zip capWs ++ pns.zip ws) h1 r1 h2
                    hretEq hretCore hbodyOk hcpNd.1.2 hnoW.1 hcore.1.2 hbodyVmCore hjCoreBody
                    hbody' hdem6 hlocVmBody hlocJBody hlocOffsBody hwfLiftedBody
                    hEnvOkBody henvBody hjenvBody hnzBody hoffsBody evBody
                  exact ⟨k', v', hevB, hretEq ▸ htvrB⟩
              -- Step into continuation `k` with `ji :: jenv` and `je :: J`.
              have hst6Ge : st.nextLocal ≤ s6.nextLocal :=
                Nat.le_trans (Nat.le_trans hlePre.nextLocal (Nat.le_add_right _ _)) hle6.nextLocal
              have hlocVmK : AllLocalLt s6.nextLocal (vm.map fun p => p.2.1) := hlocVm.mono hst6Ge
              have hlocJK : AllLocalLt s6.nextLocal ((ji :: jenv).flatMap fun je => je.capVars.map Prod.fst) := by
                intro s hs
                simp only [List.flatMap_cons, List.mem_append] at hs
                rcases hs with h1 | h2
                · exact hlocCap.mono hst6Ge s h1
                · exact hlocJ.mono hst6Ge s h2
              have hlocOffsK : AllLocalLt s6.nextLocal (offs.map fun p => p.2.1) := hlocOffs.mono hst6Ge
              have hjenvK : TJEnvRel P cert feat world d h fsh (ji :: jenv) (je :: J) locals :=
                .cons rfl (qualifyName_jpFunName fid st.nextJp) hpsOk rfl hretEq
                  (CapAgree.refl _ locals) jiSound hjenv
              have hkSize : k.size < n := by rw [← hcsz]; simp [Code.size]
              obtain ⟨kOut, vOut, hevalK, htvrOut⟩ := ihS k.size hkSize k rfl fid fsh retR vm
                (ji :: jenv) nz offs _ st' e ρ (je :: J) locals h r h'
                hretEq hretCore hkOk hcpNd.2 hnoW.2 hcore.2 hvmCore hjCoreCons
                hk' hdemLp hlocVmK hlocJK hlocOffsK hLifted hEnvOk henv hjenvK hnz hoffs ev
              exact ⟨kOut, vOut, by rw [Fir.eval_jp]; exact hevalK, htvrOut⟩
            exact hCapSpec _ (collectJpCaptures_poly _ _ fun _ _ _ _ _ _ _ => rfl)
              _ (bindTVm_poly _ (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl))
              hbody hk
        | jmp j as =>
          cases hCodeOk with
          | jmp hArgsOk =>
            unfold tCodeE at hcode
            cases hf : jenv.find? (·.id == j) with
            | none => simp only [hf] at hcode; exact False.elim (tLift_throw_elim hcode (fun _ _ => rfl))
            | some ji =>
              simp only [hf] at hcode
              by_cases har : (as.length == ji.paramReps.length) = true
              · simp only [har, ↓reduceIte] at hcode
                obtain ⟨argEs, s1, hmap, hcode⟩ := tBind_step_inv hcode
                simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hcode
                obtain ⟨rfl, rfl⟩ := hcode
                obtain ⟨je, Jrest, localsDef, hlookJ, hqual, hParamsOk, hRepsEq, hCapAgree, hJSound⟩ :=
                  hjenv.find_lookup hf
                have hJoinEq : fsh.join j = je.params.map fsh.var := paramsOk_eq_map hParamsOk
                have hRepsMap : ji.paramReps = (fsh.join j).map fun σ => repOf P cert feat σ := by
                  rw [hRepsEq, hJoinEq, List.map_map]; rfl
                have hσsCore : ∀ σ ∈ fsh.join j, isNatCoreRep (repOf P cert feat σ) = true := by
                  intro σ hσ
                  have hjiMem : ji ∈ jenv := List.mem_of_find?_eq_some hf
                  apply hjCore ji hjiMem
                  rw [hRepsMap]
                  exact List.mem_map.mpr ⟨σ, hσ, rfl⟩
                simp only [callE, qualifyExprF, qualifyExpr, hqual, Option.map_some,
                  Aiur.Generic.Expr.map, List.map_append, List.map_map] at ev
                obtain ⟨d', allWs, hm, hd', hargsEv, hcal⟩ := evalExprN_call_inv ev
                obtain ⟨capWs, argWs, hm1, rfl, hcapEv, hargEv⟩ := evalArgsN_append_inv hargsEv
                have hcapEv' : EvalArgsN world d [] locals
                    ((ji.capVars.map Prod.fst).map fun nm => qualifyExprF F (vE nm)) h capWs hm1 := by
                  simpa [qualifyExprF, List.map_map, Function.comp_def] using hcapEv
                obtain ⟨hcapLoc, hm1Eq⟩ := eval_capNames_any hcapEv'
                rw [hm1Eq] at hargEv
                have hcapDef := evalCapArgs_of_capAgree hCapAgree hcapLoc
                have hmap' : ((as.zip ((fsh.join j).map fun σ => repOf P cert feat σ)).mapM
                    (m := TLowerM) fun (a, pr) => tArgE cx vm a pr) st = .ok (argEs, s1) := by
                  rwa [← hRepsMap]
                have hargEv' : EvalArgsN world d [] locals (argEs.map (qualifyExprF F)) h argWs hm := hargEv
                obtain ⟨vs, hvs, hvsOk, htvrs, ext1⟩ :=
                  eval_tArgEs fc lw hwf hkeys hnd hdatas hvmCore hEnvOk
                    hArgsOk hσsCore hmap' hdemLp henv hargEv'
                have htvrs' : TVRs P cert feat hm ji.paramReps vs argWs := by rwa [hRepsMap]
                have hvslen : vs.length = je.params.length := by
                  have h1 := htvrs.length_eq
                  rw [hJoinEq] at h1
                  simp only [List.length_map] at h1
                  omega
                obtain ⟨k1, v1, heval1, htvr1⟩ :=
                  hJSound d' hd' hm ext1 capWs vs argWs r h' hcapDef htvrs' hvsOk hcal
                refine ⟨k1 + 1, v1, ?_, hretEq ▸ htvr1⟩
                rw [Fir.eval_jmp, hlookJ, hvs]
                simp only [Sem.Result.ofOption, Sem.Result.bind_ok, Fir.jumpTo, hvslen, ↓reduceIte]
                cases je.charged
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  exact FirFacts.eval_mono P heval1 (Nat.le_succ k1)
                · simp [Sem.later, heval1]
              · have harf : (as.length == ji.paramReps.length) = false := Bool.eq_false_iff.mpr har
                simp only [harf, Bool.false_eq_true, ↓reduceIte] at hcode
                obtain ⟨_, _, h1, _⟩ := tBind_step_inv hcode
                exact False.elim (tLift_throw_elim h1 (fun _ _ => rfl))
        | case x alts dOpt =>
          cases hCodeOk with
          | case hAltsOk hOptOk =>
            simp only [codeParamsNodup, codeNoWordPrims, codeNatCoreReps, Bool.and_eq_true] at hcpNd hnoW hcore
            unfold tCodeE at hcode
            cases hlook : vm.lookup x with
            | none => simp only [hlook] at hcode; exact False.elim (tLift_throw_elim hcode (fun _ _ => rfl))
            | some nr =>
              rcases nr with ⟨nx, rx⟩
              simp only [hlook] at hcode
              obtain ⟨altEs, s1, halts, hcode⟩ := tBind_step_inv hcode
              obtain ⟨dE, s2, hdOpt, hcase⟩ := tBind_step_inv hcode
              have hleAlts := (tAltsE_spec halts).1
              have hleOpt := (tOptE_spec hdOpt).1
              have hleCase := (tCaseE_spec hcase).1
              have hrxCore : isNatCoreRep rx = true := hvmCore (x, (nx, rx)) (mem_of_lookup_eq_some hlook)
              obtain ⟨wx, hlocx⟩ := eval_tCaseE_scrut_loc hrxCore hcase ev
              obtain ⟨vx, hρx, htvrX⟩ := henv.rel x nx rx wx hlook hlocx
              obtain ⟨ck, fs, be, loc', hasCtor, hbranch, evBe, hlocRel⟩ :=
                eval_tCaseE fc hkeys hnd hrxCore hcase hlocx htvrX ev
              have hdemS2 : DemandLe s2.demand lp.demand := hleCase.demand.trans hdemLp
              have hdemS1 : DemandLe s1.demand lp.demand := hleOpt.demand.trans hdemS2
              have hlifS2 : ∀ g ∈ s2.lifted,
                  isCleanNoU32 g.body = true ∧
                  WorldHasFn world (qualified g.name) (g.params.map Prod.fst)
                    (qualifyExprF F (Peephole.rewriteExpr g.body)) :=
                fun g hg => hLifted g (hleCase.lifted ▸ hg)
              have hlifS1 : ∀ g ∈ s1.lifted,
                  isCleanNoU32 g.body = true ∧
                  WorldHasFn world (qualified g.name) (g.params.map Prod.fst)
                    (qualifyExprF F (Peephole.rewriteExpr g.body)) :=
                fun g hg => hlifS2 g (hleOpt.lifted g hg)
              have hLocPres :
                  TEnvRel P cert feat h fsh vm ρ loc' ∧
                  TJEnvRel P cert feat world d h fsh jenv J loc' ∧
                  OffsRel ρ loc' offs := by
                rcases hlocRel with rfl | ⟨_, kq, nq, hkqGe, rfl⟩
                · exact ⟨henv, hjenv, hoffs⟩
                · have hstLeKq : st.nextLocal ≤ kq :=
                    Nat.le_trans (hleAlts.trans hleOpt).nextLocal hkqGe
                  exact ⟨henv.cons_unused (hlocVm.not_mem hstLeKq),
                         hjenv.cons_unused (hlocJ.not_mem hstLeKq),
                         hoffs.cons_unused (hlocOffs.not_mem hstLeKq)⟩
              obtain ⟨henv', hjenv', hoffs'⟩ := hLocPres
              obtain ⟨hSome, hNone⟩ := tAltsE_find_sound (k := ck) halts
              rcases hbranch with hfindSome | ⟨hfindNone, hdEq⟩
              · obtain ⟨b, stA, stB, hbSz, hbCode, hleA, hlifB, hdemB, hbOk, hbNd, hbNoW, hbCore, hevAlts⟩ :=
                  hSome (ck, be) hfindSome
                have hnzB : NzRel ρ (if rx.isFieldNat && P.known.natSucc == some ck then
                    if nz.contains x then nz else x :: nz else nz) := by
                  by_cases hcond : (rx.isFieldNat && P.known.natSucc == some ck) = true
                  · simp only [hcond, ↓reduceIte]
                    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
                    obtain ⟨hfnat, hks⟩ := hcond
                    have hpos : ∃ n, vx = .lit (.nat n) ∧ 0 < n := by
                      cases rx with
                      | nat _ | w8 | w16 =>
                        cases htvrX
                        rename_i n0 _
                        cases n0 with
                        | zero =>
                          simp only [Fir.Val.asCtor] at hasCtor
                          cases hkz : P.known.natZero with
                          | none => simp [hkz] at hasCtor
                          | some kz =>
                            simp only [hkz] at hasCtor
                            cases hasCtor
                            have hnp := natCoreProgram_natPinsDistinct hnc
                            simp [natPinsDistinct, hkz, hks] at hnp
                        | succ m0 => exact ⟨m0 + 1, rfl, Nat.succ_pos m0⟩
                      | irr | w32 | w64 | «enum» _ | data _ | obj =>
                        simp [Rep.isFieldNat] at hfnat
                    obtain ⟨n0, rfl, hn0Pos⟩ := hpos
                    split
                    · exact hnz
                    · exact hnz.cons hρx hn0Pos
                  · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
                    exact hnz
                have hbLt : b.size < n := by rw [← hcsz]; simp only [Code.size]; omega
                obtain ⟨k1, v1, hevalB, htvr1⟩ := ihS b.size hbLt b rfl fid fsh retR vm jenv _ offs
                  stA stB be ρ J loc' h r h'
                  hretEq hretCore (hbOk hAltsOk) (hbNd hcpNd.1) (hbNoW hnoW.1) (hbCore hcore.1)
                  hvmCore hjCore hbCode (hdemB.trans hdemS1) (hlocVm.mono hleA) (hlocJ.mono hleA)
                  (hlocOffs.mono hleA) (fun g hg => hlifS1 g (hlifB g hg))
                  hEnvOk henv' hjenv' hnzB hoffs' evBe
                refine ⟨k1, v1, ?_, htvr1⟩
                rw [Fir.eval_case, hρx]
                simp only [Sem.Result.ofOption, Sem.Result.bind_ok, hasCtor]
                rw [hevAlts k1 ρ J dOpt]
                exact hevalB
              · cases dOpt with
                | none =>
                  obtain ⟨hdNone, _⟩ := tOptE_none_inv hdOpt
                  rw [hdNone] at hdEq; cases hdEq
                | some dc =>
                  obtain ⟨de, hcodeD, hdSome⟩ := tOptE_some_inv hdOpt
                  rw [hdSome, Option.some.injEq] at hdEq
                  subst hdEq
                  cases hOptOk with
                  | present hdcOk =>
                    have hdcLt : dc.size < n := by rw [← hcsz]; simp only [Code.size, Code.optSize]; omega
                    obtain ⟨k1, v1, hevalD, htvr1⟩ := ihS dc.size hdcLt dc rfl fid fsh retR vm jenv
                      nz offs s1 s2 de ρ J loc' h r h'
                      hretEq hretCore hdcOk hcpNd.2 hnoW.2 hcore.2 hvmCore hjCore hcodeD hdemS2
                      (hlocVm.mono hleAlts.nextLocal) (hlocJ.mono hleAlts.nextLocal)
                      (hlocOffs.mono hleAlts.nextLocal) hlifS2
                      hEnvOk henv' hjenv' hnz hoffs' evBe
                    refine ⟨k1, v1, ?_, htvr1⟩
                    rw [Fir.eval_case, hρx]
                    simp only [Sem.Result.ofOption, Sem.Result.bind_ok, hasCtor]
                    rw [hNone hfindNone k1 ρ J (some dc)]
                    exact hevalD
        | ret a =>
          cases hCodeOk with
          | ret hArgOk =>
            unfold tCodeE at hcode
            obtain ⟨v1, haEv, htvr1, _⟩ :=
              eval_tArgE fc lw hwf hkeys hnd hdatas hcode hvmCore hretCore hdemLp henv ev
                (fun v hv => hretEq ▸ CoerceTargetOk.of_valOk (Fir.Proof.Shape.argSound hEnvOk hArgOk hv))
            exact ⟨0, v1, by simp [Fir.eval_ret, haEv, Sem.Result.ofOption], htvr1⟩
        | tcall g as =>
          cases hCodeOk with
          | tcall hArgsOk hRetLe =>
            unfold tCodeE at hcode
            dsimp only [cx] at hcode
            cases hfun : P.fun? g with
            | none => simp only [hfun] at hcode; exact False.elim (tLift_throw_elim hcode (fun _ _ => rfl))
            | some gd =>
              simp only [hfun] at hcode
              by_cases hsz : g < P.size
              · simp only [hsz, ↓reduceIte] at hcode
                by_cases har : (as.length == gd.params.length) = true
                · simp only [har, ↓reduceIte] at hcode
                  obtain ⟨argEs, s1, hmap, hco⟩ := tBind_step_inv hcode
                  obtain ⟨hgParamsOk, _⟩ := hchk.funs g gd hfun
                  have hgParamsEq : (cert.fn g).params = (gd.params.map Prod.fst).map (cert.fn g).var :=
                    paramsOk_eq_map hgParamsOk
                  obtain ⟨_, _, _, hgRetCore, hgParamCore, _⟩ := natCoreProgram_funInfo hnc hfun hsz
                  have hσsCore : ∀ σ ∈ (cert.fn g).params, isNatCoreRep (repOf P cert feat σ) = true := by
                    intro σ hσ
                    rw [hgParamsEq] at hσ
                    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hσ
                    exact hgParamCore p hp
                  have hmap' : ((as.zip ((cert.fn g).params.map fun σ => repOf P cert feat σ)).mapM
                      (m := TLowerM) fun (a, pr) => tArgE cx vm a pr) st = .ok (argEs, s1) := by
                    have hrepsEq : ((cert.fn g).params.map fun σ => repOf P cert feat σ) =
                        (gd.params.map Prod.fst).map (fun p => cx.rep ((cx.funShapes g).var p)) := by
                      rw [hgParamsEq, List.map_map]; rfl
                    rwa [hrepsEq]
                  have hdemS1 : DemandLe s1.demand lp.demand := (coerceE_spec hco).1.demand.trans hdemLp
                  obtain ⟨v1, ⟨vs, hvs, k1, hcall1, hv1Ok⟩, htvr1, _⟩ :=
                    eval_coerceE fc lw hwf hkeys hnd hdatas hco hgRetCore hretCore hdemLp ev
                      (Q := fun v => ∃ vs, evalArgs ρ as = some vs ∧
                        ∃ k1, Fir.evalCall P k1 g vs = .ok v ∧ ValOk cert dummyEnc fsh.ret v)
                      (fun w0 hm0 evCall => by
                        simp only [callE, qualifyExprF, qualifyExpr, qualifyName_funName,
                          Option.map_some, Aiur.Generic.Expr.map, List.map_map] at evCall
                        obtain ⟨d', ws, hm1, hd', hargsEv, hcal⟩ := evalExprN_call_inv evCall
                        have hargsEv' : EvalArgsN world d [] locals (argEs.map (qualifyExprF F)) h ws hm1 :=
                          hargsEv
                        obtain ⟨vs, hvs, hvsOk, htvrs, ext1⟩ :=
                          eval_tArgEs fc lw hwf hkeys hnd hdatas hvmCore hEnvOk
                            hArgsOk hσsCore hmap' hdemS1 henv hargsEv'
                        have htvrs' : TVRs P cert feat hm1
                            ((gd.params.map Prod.fst).map fun p => repOf P cert feat ((cert.fn g).var p))
                            vs ws := by
                          simpa [feat, hgParamsEq, List.map_map, Function.comp_def] using htvrs
                        obtain ⟨k1, v1, hcall1, htvr1⟩ :=
                          hFunSound d' hd' g gd hfun hsz vs ws hm1 w0 hm0 htvrs' hvsOk hcal
                        have hv1Ok := Fir.Proof.Shape.leSound dummyEnc cert _ _ _ hRetLe
                          (evalCall_valOk hchk hsz hvsOk hcall1)
                        exact ⟨v1, ⟨vs, hvs, k1, hcall1, hv1Ok⟩, htvr1, ext1.trans hcal.heap_extends⟩)
                      (fun _ ⟨_, _, _, _, hvOk⟩ => hretEq ▸ CoerceTargetOk.of_valOk hvOk)
                  refine ⟨k1, v1, ?_, htvr1⟩
                  rw [Fir.eval_tcall, hvs]
                  simpa [Sem.Result.ofOption, Fir.run_eq] using hcall1
                · have harf : (as.length == gd.params.length) = false := Bool.eq_false_iff.mpr har
                  simp only [harf, Bool.false_eq_true, ↓reduceIte] at hcode
                  obtain ⟨_, _, h1, _⟩ := tBind_step_inv hcode
                  exact False.elim (tLift_throw_elim h1 (fun _ _ => rfl))
              · simp only [hsz, ↓reduceIte] at hcode
                obtain ⟨_, _, h1, _⟩ := tBind_step_inv hcode
                exact False.elim (tLift_throw_elim h1 (fun _ _ => rfl))
        | trap =>
          unfold tCodeE at hcode
          have htrp := (tTrapE_ok_inv hcode (fun _ _ _ => rfl)
            (fun fuel _ r => by cases r <;> first | rfl | (cases fuel <;> rfl))
            (fun _ _ => rfl) (fun _ _ => rfl)).1
          exact False.elim (evalExprN_of_isTrapExpr htrp ev)
    intro fid fsh retR vm jenv nz offs c st st' e ρ J locals h r h'
    exact bySize c.size c rfl fid fsh retR vm jenv nz offs st st' e ρ J locals h r h'

end MainTypedProof

/-! ## Section 8: Headline Typed Backward Simulation & End-to-End Circuit Soundness -/

section TypedHeadline

variable {F : Type} [Field F] [DecidableEq F]

/-- **Full Typed Backward Simulation Theorem (Internal Fir Functions):**
Every `EvalFn` derivation of a typed/unboxed lowered Fir function `Prog::f<f>` (including
peephole rewriting) on `TVRs`-related, shape-valid arguments yields a terminating
`Fir.run P k f vs = .ok v` whose result `v` is `TVR`-related to `r` at `repOf (cert.fn f).ret`. -/
theorem typed_backward_sound {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld P cert sched lp world)
    (hnc : natCoreProgram P cert = true)
    {f : FunId} {fd : Fun} (hfun : P.fun? f = some fd) (hsz : f < P.size)
    {vs : List Fir.Val} {ws : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (htvrs : TVRs P cert (scanFeatures P) h
      ((fd.params.map Prod.fst).map fun p => repOf P cert (scanFeatures P) ((cert.fn f).var p)) vs ws)
    (hvsOk : ValsOk cert dummyEnc (cert.fn f).params vs)
    (ev : EvalFn world (qualified (funName f)) ws h r h') :
    ∃ k v, Fir.run P k f vs = .ok v ∧
      TVR P cert (scanFeatures P) h' (repOf P cert (scanFeatures P) (cert.fn f).ret) v r := by
  obtain ⟨d, evN⟩ := EvalFnN.ofEvalFn ev
  obtain ⟨k, v, hcall, htvr⟩ :=
    tFunSoundN_of_tCodeSound lw hnc (fun d' _ => eval_tCodeE_sound_N fc lw hnc d')
      d (Nat.lt_succ_self d) f fd hfun hsz vs ws h r h' htvrs hvsOk evN
  exact ⟨k, v, by rw [Fir.run_eq]; exact hcall, htvr⟩

omit [Field F] [DecidableEq F] in
private theorem isCleanNoU32_entryArgs {cx : TCx}
    (hdatas : datasNatCoreReps cx.P cx.cert cx.feat = true) :
    ∀ {ls : List (Nat × Rep)} {s0 s1 : TState} {es : List Lower.Expr},
      (∀ p ∈ ls, isNatCoreRep p.2 = true) →
      (ls.mapM (m := TLowerM) fun (j, pr) =>
        coerceE cx (.nat natLimit) pr
          (seqE (callE "check_u56" [vE (entryParamName j)]) (vE (entryParamName j)))) s0 =
        .ok (es, s1) →
      TStateLe s0 s1 ∧ isCleanNoU32List es = true
  | [], s0, s1, es, _, h => by
    simp only [List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨TStateLe.refl _, rfl⟩
  | (j, pr) :: tl, s0, s1, es, hcore, h => by
    rw [List.mapM_cons] at h
    obtain ⟨e1, sm, hco, h⟩ := tBind_step_inv h
    obtain ⟨es2, s2, htl, h⟩ := tBind_step_inv h
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hle1, hcl1⟩ := coerceE_spec hco
    obtain ⟨hle2, hcl2⟩ := isCleanNoU32_entryArgs hdatas
      (fun p hp => hcore p (List.mem_cons_of_mem _ hp)) htl
    have hchkClean : isCleanNoU32
        (seqE (callE "check_u56" [vE (entryParamName j)]) (vE (entryParamName j))) = true := by
      simp [seqE, callE, vE, isCleanNoU32, isCleanNoU32List, isSimplePat, isPeepholeU32Name]
    exact ⟨hle1.trans hle2, by
      simp [isCleanNoU32List, hcl1 rfl (hcore _ List.mem_cons_self) hdatas hchkClean, hcl2]⟩

private theorem eval_tEntry_args_aux {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld P cert sched lp world)
    (hwf : cert.WF) (hkeys : (P.ctors.map (·.key)).Nodup) (hnd : (objCtorNames P).Nodup)
    (hdatas : datasNatCoreReps P cert (scanFeatures P) = true)
    {d : Nat} {locals : Environment F Nat} :
    ∀ {items : List (Nat × Shape)} {st1 st2 : TState} {argEs : List Lower.Expr}
      {h h' : Heap F} {ws : List (SourceValue F)},
      (items ≠ [] → lp.demand.needCheckU56 = true) →
      (∀ p ∈ items, (Shape.natLt natLimit).le p.2 = true ∧
        isNatCoreRep (repOf P cert (scanFeatures P) p.2) = true) →
      ((items.map fun (j, σ) => (j, repOf P cert (scanFeatures P) σ)).mapM (m := TLowerM)
        fun (j, pr) =>
          coerceE { P, cert, feat := scanFeatures P, sched } (.nat natLimit) pr
            (seqE (callE "check_u56" [vE (entryParamName j)]) (vE (entryParamName j)))) st1 =
        .ok (argEs, st2) →
      DemandLe st2.demand lp.demand →
      EvalArgsN world d [] locals (argEs.map (qualifyExprF F)) h ws h' →
      ∃ ns : List Nat,
        (∀ n ∈ ns, n < natLimit) ∧
        List.Forall₂ (fun (p : Nat × Shape) (n : Nat) => locals.find? (·.1 == entryParamName p.1) =
          some (entryParamName p.1, .field (n : F))) items ns ∧
        ValsOk cert dummyEnc (items.map Prod.snd) (ns.map fun n => .lit (.nat n)) ∧
        TVRs P cert (scanFeatures P) h'
          (items.map fun p => repOf P cert (scanFeatures P) p.2)
          (ns.map fun n => .lit (.nat n)) ws ∧
        Heap.Extends h h'
  | [], st1, st2, argEs, h, h', ws, _, _, hmap, _, ev => by
    simp only [List.map_nil, List.mapM, List.mapM.loop, pure, StateT.pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at hmap
    obtain ⟨rfl, rfl⟩ := hmap
    cases ev
    exact ⟨[], by simp, .nil, .nil, .nil, Heap.Extends.refl _⟩
  | (j, σ) :: rest, st1, st2, argEs, h, h', ws, hchk56, hall, hmap, hdem, ev => by
    simp only [List.map_cons] at hmap
    rw [List.mapM_cons] at hmap
    obtain ⟨e1, sm, hco, hmap⟩ := tBind_step_inv hmap
    obtain ⟨esRest, s2, hrest, hmap⟩ := tBind_step_inv hmap
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hmap
    obtain ⟨rfl, rfl⟩ := hmap
    simp only [List.map_cons] at ev
    cases ev with
    | cons ev1 evRest =>
      rename_i w1 hm wsRest
      have ⟨hleσ, hcoreσ⟩ := hall (j, σ) List.mem_cons_self
      have h56 : lp.demand.needCheckU56 = true := hchk56 (by simp)
      have hneNone : lp.tier ≠ .none :=
        tier_ne_none_of_usesRangeCheck lw.lowered (by simp [h56])
      have hleRest := (isCleanNoU32_entryArgs hdatas (fun p hp => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact (hall q (List.mem_cons_of_mem _ hq)).2) hrest).1
      have hdemSm : DemandLe sm.demand lp.demand := hleRest.demand.trans hdem
      obtain ⟨v1, ⟨n1, hn1, rfl, hloc1⟩, htvr1, ext1⟩ :=
        eval_coerceE fc lw hwf hkeys hnd hdatas hco rfl hcoreσ hdemSm ev1
          (Q := fun v => ∃ n, n < natLimit ∧ v = .lit (.nat n) ∧
            locals.find? (·.1 == entryParamName j) = some (entryParamName j, .field (n : F)))
          (fun w0 hm0 evSeq => by
            simp only [seqE, callE, vE, qualifyExprF, qualifyExpr, qualifyPat,
              qualifyName_check_u56, Option.map_some, Aiur.Generic.Expr.map,
              Aiur.Generic.Pattern.map, List.map] at evSeq
            obtain ⟨_, _, evCall, evVar2⟩ := evalExprN_let_wildcard_inv evSeq
            obtain ⟨_, vx1, _, _, evVar1, hcal⟩ := evalExprN_call1_inv evCall
            obtain ⟨hl1, rfl⟩ := evalExprN_var_inv evVar1
            obtain ⟨_, rfl, n0, hn0, rfl⟩ :=
              eval_check_u56 (lw.byteCheck hneNone) (lw.hasCheckU56 (Or.inl h56)) hcal.toEvalFn
            obtain ⟨hl2, rfl⟩ := evalExprN_var_inv evVar2
            rw [hl1, Option.some.injEq, Prod.mk.injEq] at hl2
            obtain ⟨_, rfl⟩ := hl2
            exact ⟨.lit (.nat n0), ⟨n0, hn0, rfl, hl1⟩,
              .nat (Nat.lt_min.mpr ⟨hn0, hn0⟩), Heap.Extends.refl _⟩)
          (fun _ ⟨n0, hn0, hvEq, _⟩ => by
            subst hvEq
            exact CoerceTargetOk.of_valOk
              (Fir.Proof.Shape.leSound dummyEnc cert _ _ _ hleσ (.natLt hn0)))
      obtain ⟨nsRest, hnsRest, hlocsRest, hvalsRest, htvrsRest, ext2⟩ :=
        eval_tEntry_args_aux fc lw hwf hkeys hnd hdatas
          (fun _ => h56)
          (fun p hp => hall p (List.mem_cons_of_mem _ hp))
          hrest hdem evRest
      refine ⟨n1 :: nsRest, ?_, .cons hloc1 hlocsRest,
        .cons (Fir.Proof.Shape.leSound dummyEnc cert _ _ _ hleσ (.natLt hn1)) hvalsRest,
        .cons (htvr1.extend ext2) htvrsRest, ext1.trans ext2⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | htl
      · exact hn1
      · exact hnsRest x htl

omit [Field F] [DecidableEq F] in
private theorem find?_zip_entryParams {args : List (SourceValue F)} :
    ∀ {k n : Nat} (hk : k < n) (hlen : args.length = n),
      (((List.range n).map entryParamName).zip args).find? (·.1 == entryParamName k) =
        some (entryParamName k, args[k]'(by omega)) := by
  intro k n hk hlen
  have hnd : ((List.range n).map entryParamName).Nodup :=
    List.Nodup.map (fun _ _ heq => entryParamName_inj heq) List.nodup_range
  have hlen1 : ((List.range n).map entryParamName).length = n := by simp
  have hget : (((List.range n).map entryParamName).zip args)[k]? =
      some (entryParamName k, args[k]'(by omega)) := by
    have hkZip : k < (((List.range n).map entryParamName).zip args).length := by
      simp [hlen1, hlen, hk]
    rw [List.getElem?_eq_getElem hkZip]
    simp [List.getElem_zip]
  have hmem := List.mem_of_getElem? hget
  -- Since keys in `zip` are `Nodup`, `find?` returns the unique pair with key `entryParamName k`.
  have aux : ∀ {xs : List String} {ys : List (SourceValue F)} {a : String} {v : SourceValue F},
      xs.Nodup → (a, v) ∈ xs.zip ys → (xs.zip ys).find? (·.1 == a) = some (a, v) := by
    intro xs
    induction xs with
    | nil => intro _ _ _ _ hm; cases hm
    | cons x xt ih =>
      intro ys a v hnd' hm
      cases ys with
      | nil => cases hm
      | cons y yt =>
        rw [List.nodup_cons] at hnd'
        simp only [List.zip_cons_cons, List.mem_cons, List.find?_cons] at hm ⊢
        rcases hm with hEq | htl
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
          simp
        · have haMem : a ∈ xt := (List.of_mem_zip htl).1
          have hne : x ≠ a := fun h => hnd'.1 (h ▸ haMem)
          have hneB : (x == a) = false := beq_false_of_ne hne
          rw [hneB]
          exact ih hnd'.2 htl
  exact aux hnd hmem

omit [DecidableEq F] in
private theorem args_eq_map_field_of_forall2 {args : List (SourceValue F)} {σs : List Shape}
    {ns : List Nat} (hlenA : args.length = σs.length)
    (hfa : List.Forall₂ (fun (p : Nat × Shape) (n : Nat) =>
      (((List.range σs.length).map entryParamName).zip args).find? (·.1 == entryParamName p.1) =
        some (entryParamName p.1, .field (n : F)))
      ((List.range σs.length).zip σs) ns) :
    args = ns.map (fun n => .field (n : F)) := by
  have hlenNs : ns.length = σs.length := by
    have h1 := hfa.length_eq
    simp only [List.length_zip, List.length_range, Nat.min_self] at h1
    exact h1.symm
  apply List.ext_getElem (by simp [hlenA, hlenNs])
  intro k hk1 hk2
  have hkLt : k < σs.length := by omega
  have hgetRel : ∀ {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β},
      List.Forall₂ R l1 l2 → ∀ (i : Nat) (h1 : i < l1.length) (h2 : i < l2.length), R l1[i] l2[i] := by
    intro _ _ _ l1 l2 h; induction h with
    | nil => intro _ h1 _; simp at h1
    | cons hd _ ih => intro i h1 h2; cases i with | zero => exact hd | succ i' => exact ih i' _ _
  have hrel := hgetRel hfa k (by simp [hkLt]) (by omega)
  have hzipGet : ((List.range σs.length).zip σs)[k]'(by simp [hkLt]) = (k, σs[k]'hkLt) := by
    simp
  rw [hzipGet] at hrel
  rw [find?_zip_entryParams hkLt hlenA, Option.some.injEq, Prod.mk.injEq] at hrel
  simpa using hrel.2

/-- **Typed Entrypoint Backward Simulation Theorem (`Prog::main<i>`):**
Every `EvalFn` derivation of an exported typed entry wrapper `Prog::main<i>` on raw `Field`
arguments proves that all arguments are `< 2^56` field casts and yields a terminating
`Fir.run P k f (ns.map (.lit ∘ .nat)) = .ok v` whose result `v` satisfies `TVR` at
the unboxed export return representation `repOf (cert.fn f).ret` (with `lp.exportReps[i]? = some retR`). -/
theorem typed_entry_backward_sound {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld P cert sched lp world)
    (hnc : natCoreProgram P cert = true)
    {i : Nat} {f : FunId} (hexp : P.exports[i]? = some f)
    {args : List (SourceValue F)} {h' : Heap F} {r : SourceValue F}
    (ev : EvalFn world (qualified (entryName i)) args [] r h') :
    ∃ (ns : List Nat) (k : Nat) (v : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : F)) ∧
      Fir.run P k f (ns.map fun n => .lit (.nat n)) = .ok v ∧
      lp.exportReps[i]? = some (repOf P cert (scanFeatures P) (cert.fn f).ret) ∧
      TVR P cert (scanFeatures P) h' (repOf P cert (scanFeatures P) (cert.fn f).ret) v r := by
  have hchk := natCoreProgram_checked hnc
  have hwf := hchk.wf
  have hkeys := lw.ctors_keys_nodup
  have hnd := lw.ctors_names_nodup
  have hdatas := natCoreProgram_datasNatCoreReps hnc
  obtain ⟨fd, st1, st2, argEs, hfun, hsz, hrepGet, hchk56, hmap, hdem2, hwfEnt⟩ := lw.hasEntry hexp
  obtain ⟨_, _, _, _, hparamCore, _⟩ := natCoreProgram_funInfo hnc hfun hsz
  obtain ⟨hpsOk, _⟩ := hchk.funs f fd hfun
  have hparamsEq : (cert.fn f).params = (fd.params.map Prod.fst).map (cert.fn f).var :=
    paramsOk_eq_map hpsOk
  have hcleanArgs : isCleanNoU32List argEs = true :=
    (isCleanNoU32_entryArgs hdatas (fun p hp => by
      obtain ⟨q, hq, hqEq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
      rw [← hqEq]; exact hparamCore q hq) hmap).2
  have hplain : isPlainExpr (qualifyExprF F (callE (funName f) argEs)) = true := by
    rw [isPlainExpr_qualifyExprF]
    exact isPlainExpr_of_isCleanNoU32
      (isCleanNoU32_callE (isPeepholeU32Name_funName f) hcleanArgs)
  obtain ⟨d, evN⟩ := EvalFnN.ofEvalFn ev
  obtain ⟨hlen, evBody⟩ := evalFnN_plain_inv hwfEnt hplain evN
  simp only [callE, qualifyExprF, qualifyExpr, qualifyName_funName, Option.map_some,
    Aiur.Generic.Expr.map, List.map_map] at evBody
  obtain ⟨d', ws, hm, _, hargsEv, hcal⟩ := evalExprN_call_inv evBody
  have hargsEv' : EvalArgsN world d [] (((List.range fd.params.length).map entryParamName).zip args)
      (argEs.map (qualifyExprF F)) [] ws hm := hargsEv
  set σs := (fd.params.map Prod.fst).map (cert.fn f).var
  have hlenσs : σs.length = fd.params.length := by simp [σs]
  have hitemsMap :
      (((List.range fd.params.length).zip σs).map fun (j, σ) => (j, repOf P cert (scanFeatures P) σ)) =
      (List.range fd.params.length).zip
        ((fd.params.map Prod.fst).map fun p => repOf P cert (scanFeatures P) ((cert.fn f).var p)) := by
    have hzipMap : ∀ {α β γ : Type} (l1 : List α) (l2 : List β) (g : β → γ),
        (l1.zip l2).map (fun (a, b) => (a, g b)) = l1.zip (l2.map g) := by
      intro _ _ _ l1; induction l1 with
      | nil => intro _ _; rfl
      | cons _ tl ih =>
        intro l2 g; cases l2 with
        | nil => rfl
        | cons _ tl2 => simp [ih]
    rw [hzipMap, List.map_map]; rfl
  have hmap' : ((((List.range fd.params.length).zip σs).map
      fun (j, σ) => (j, repOf P cert (scanFeatures P) σ)).mapM (m := TLowerM)
      fun (j, pr) =>
        coerceE { P, cert, feat := scanFeatures P, sched } (.nat natLimit) pr
          (seqE (callE "check_u56" [vE (entryParamName j)]) (vE (entryParamName j)))) st1 =
      .ok (argEs, st2) := by
    rw [hitemsMap]; exact hmap
  have hchk56Items : ((List.range fd.params.length).zip σs) ≠ [] → lp.demand.needCheckU56 = true := by
    intro hne
    apply hchk56
    cases hlen0 : fd.params.length with
    | zero => simp [hlen0] at hne
    | succ _ => omega
  have hallItems : ∀ p ∈ (List.range fd.params.length).zip σs,
      (Shape.natLt natLimit).le p.2 = true ∧
      isNatCoreRep (repOf P cert (scanFeatures P) p.2) = true := by
    intro p hp
    obtain ⟨v, hv, hvEq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← hvEq]
    exact ⟨natCoreProgram_exportParam_le hnc hexp hfun v hv, hparamCore v hv⟩
  obtain ⟨ns, hns, hlocs, hvalsOk, htvrs, _⟩ :=
    eval_tEntry_args_aux fc lw hwf hkeys hnd hdatas hchk56Items hallItems hmap' hdem2 hargsEv'
  have hlenA : args.length = σs.length := by
    simp only [List.length_map, List.length_range] at hlen
    omega
  have hargsEq : args = ns.map (fun n => .field (n : F)) := by
    have hlocs' : List.Forall₂ (fun (p : Nat × Shape) (n : Nat) =>
        (((List.range σs.length).map entryParamName).zip args).find? (·.1 == entryParamName p.1) =
          some (entryParamName p.1, .field (n : F)))
        ((List.range σs.length).zip σs) ns := by
      rw [hlenσs]; exact hlocs
    exact args_eq_map_field_of_forall2 hlenA hlocs'
  have hmapSnd : ((List.range fd.params.length).zip σs).map Prod.snd = σs :=
    List.map_snd_zip (by simp [hlenσs])
  have hvalsOk' : ValsOk cert dummyEnc (cert.fn f).params (ns.map fun n => .lit (.nat n)) := by
    rw [hparamsEq, ← hmapSnd]
    exact hvalsOk
  have htvrs' : TVRs P cert (scanFeatures P) hm
      ((fd.params.map Prod.fst).map fun p => repOf P cert (scanFeatures P) ((cert.fn f).var p))
      (ns.map fun n => .lit (.nat n)) ws := by
    have hmapRep : (((List.range fd.params.length).zip σs).map
        fun p => repOf P cert (scanFeatures P) p.2) =
        (fd.params.map Prod.fst).map fun p => repOf P cert (scanFeatures P) ((cert.fn f).var p) := by
      have : (((List.range fd.params.length).zip σs).map fun p => repOf P cert (scanFeatures P) p.2) =
          (((List.range fd.params.length).zip σs).map Prod.snd).map (repOf P cert (scanFeatures P)) := by
        rw [List.map_map]; rfl
      rw [this, hmapSnd, List.map_map]; rfl
    rwa [← hmapRep]
  obtain ⟨k, v, hrun, htvr⟩ := typed_backward_sound fc lw hnc hfun hsz htvrs' hvalsOk' hcal.toEvalFn
  exact ⟨ns, k, v, hns, hargsEq, hrun, hrepGet, htvr⟩

/-- **End-to-End Certified Typed Circuit Soundness (General `FieldCompatible64 F`):**
Composes `typed_entry_backward_sound` with
`Aiur.Modules.Prepared.depth_grouped_activated_heap_sound`. -/
theorem typed_circuit_sound {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {moduleProg : Aiur.Modules.Program F}
    {id : String → Except String Nat}
    (fc : FieldCompatible64 F)
    (prepared : Aiur.Modules.Prepared moduleProg)
    (lw : TypedLoweredWorld P cert sched lp prepared.environment.source.world)
    (hnc : natCoreProgram P cert = true)
    (compiled : Aiur.Optimized.ModulesArtifact prepared)
    (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
    {cfg : Aiur.Optimized.Depth.Config}
    (certified : Aiur.Optimized.Physical.Prepared.DepthCertified compiled.circuit physical cfg)
    (bits : cfg.bits ≤ 24)
    (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {external : String}
    {entry : Aiur.Modules.Selection moduleProg prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {i : Nat} {f : FunId}
    (hname : entry.resolved.name = qualified (entryName i))
    (hexp : P.exports[i]? = some f)
    {rom : Aiur.WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Aiur.Value F}
    {wires : List (Aiur.WireValue F)} {output : Aiur.WireValue F}
    (signed : Aiur.Circuit.Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message F}
    (rooted : Aiur.Optimized.Depth.erase cfg root =
      Aiur.Circuit.Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (Aiur.Circuit.WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : F) ≠ 0)
    (checked : plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ (value : SourceValue F) (heap : Heap F) (ns : List Nat) (k : Nat) (v : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : F)) ∧
      Fir.run P k f (ns.map fun n => .lit (.nat n)) = .ok v ∧
      lp.exportReps[i]? = some (repOf P cert (scanFeatures P) (cert.fn f).ret) ∧
      TVR P cert (scanFeatures P) heap (repOf P cert (scanFeatures P) (cert.fn f).ret) v value ∧
      Aiur.Represents ((Aiur.Circuit.Erasure.typedROM compiled.circuit.system rom).decode
        compiled.specialized.program.enums) heap value result := by
  obtain ⟨value, heap, hevalMod, hrep⟩ :=
    prepared.depth_grouped_activated_heap_sound compiled physical certified bits plan activated
      selected valid signed rooted outside bound characteristic checked arguments decoded
  obtain ⟨entry', hsel', hevalFn⟩ := hevalMod
  rw [selected, Option.some.injEq] at hsel'
  subst hsel'
  rw [hname] at hevalFn
  obtain ⟨ns, k, v, hns, hargs, hrun, hrepGet, htvr⟩ :=
    typed_entry_backward_sound fc lw hnc hexp hevalFn
  exact ⟨value, heap, ns, k, v, hns, hargs, hrun, hrepGet, htvr, hrep⟩

/-- **End-to-End Certified Typed Circuit Soundness over Goldilocks (`U32.Goldilocks.F`):**
Discharges BOTH `FieldCompatible64` (`fieldCompatible64_goldilocks`) and the depth-pass
characteristic bound (`Depth.goldilocks_characteristic`). -/
theorem typed_circuit_sound_goldilocks {P : Program} {cert : ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program Aiur.Library.U32.Goldilocks.F}
    {id : String → Except String Nat}
    (prepared : Aiur.Modules.Prepared moduleProg)
    (lw : TypedLoweredWorld P cert sched lp prepared.environment.source.world)
    (hnc : natCoreProgram P cert = true)
    (compiled : Aiur.Optimized.ModulesArtifact prepared)
    (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
    {cfg : Aiur.Optimized.Depth.Config}
    (certified : Aiur.Optimized.Physical.Prepared.DepthCertified compiled.circuit physical cfg)
    (bits : cfg.bits ≤ 24)
    (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {external : String}
    {entry : Aiur.Modules.Selection moduleProg prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {i : Nat} {f : FunId}
    (hname : entry.resolved.name = qualified (entryName i))
    (hexp : P.exports[i]? = some f)
    {rom : Aiur.WidthROM Aiur.Library.U32.Goldilocks.F} (valid : rom.Valid)
    {args : List (SourceValue Aiur.Library.U32.Goldilocks.F)}
    {result : Aiur.Value Aiur.Library.U32.Goldilocks.F}
    {wires : List (Aiur.WireValue Aiur.Library.U32.Goldilocks.F)}
    {output : Aiur.WireValue Aiur.Library.U32.Goldilocks.F}
    (signed : Aiur.Circuit.Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message Aiur.Library.U32.Goldilocks.F}
    (rooted : Aiur.Optimized.Depth.erase cfg root =
      Aiur.Circuit.Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (Aiur.Circuit.WeightedRow Aiur.Library.U32.Goldilocks.F)}
    (bound : rows.length ≤ 2 ^ 39)
    (checked : plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ (value : SourceValue Aiur.Library.U32.Goldilocks.F) (heap : Heap Aiur.Library.U32.Goldilocks.F)
      (ns : List Nat) (k : Nat) (v : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : Aiur.Library.U32.Goldilocks.F)) ∧
      Fir.run P k f (ns.map fun n => .lit (.nat n)) = .ok v ∧
      lp.exportReps[i]? = some (repOf P cert (scanFeatures P) (cert.fn f).ret) ∧
      TVR P cert (scanFeatures P) heap (repOf P cert (scanFeatures P) (cert.fn f).ret) v value ∧
      Aiur.Represents ((Aiur.Circuit.Erasure.typedROM compiled.circuit.system rom).decode
        compiled.specialized.program.enums) heap value result :=
  typed_circuit_sound fieldCompatible64_goldilocks prepared lw hnc compiled physical certified bits
    plan activated selected hname hexp valid signed rooted outside bound
    Aiur.Optimized.Depth.goldilocks_characteristic checked arguments decoded

end TypedHeadline

end IxCC.AiurBackend.TypedBackward
