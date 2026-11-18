import IxVMRefinement.Claim.TopDecode
import IxVMRefinement.Binding.ClaimExport

/-! # Claim decoding for a binding claim

`verify_claim_decode_binding_spec` inverts `IxVM::verify_claim` (`KernelClaim::run_claim`) on a
`binding spec a` claim: the run hashed a collision with the claim's bytes, or it took arm 10 of
`run_claim` and called `KernelRoles::validate_binding` on the claim's binding address
(`RoleVal.ValidateBindingIn`). `run_claim` has no generated observation, so the derivation is
inverted step by step, as `verify_claim_decode_typing_spec` does for the typing arms; the steps
up to the dispatch on the variant are the same.

`bindingClaimDecodes_of_run` is the first named part of the binding claim's export
(`Binding.BindingClaimDecodes`), and `bindingClaimExport_of_table_and_stores` the export from
the three parts that remain.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM (F)
open Ix (Claim ClaimContext AssumptionTree)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-! ## Helpers -/

private theorem bd_blake3Pure_hash_size (b : ByteArray) :
    (Address.blake3Pure b).hash.size = 32 := by
  cases b with
  | mk arr =>
    have h := L1.blake3Pure_eq arr.toList
    simp only [Array.toArray_toList] at h
    rw [h]
    exact (Blake3.Pure.digest arr.toList).size_toArray

private theorem bd_getScope_ok_inv {variant : UInt64} {bs : List UInt8} {i : Nat}
    {fmt valByte : UInt8}
    (h1 : Ixon.getU8 { idx := i, bytes := ⟨bs.toArray⟩ } =
      .ok fmt { idx := i + 1, bytes := ⟨bs.toArray⟩ })
    (h2 : Ixon.getU8 { idx := i + 1, bytes := ⟨bs.toArray⟩ } =
      .ok valByte { idx := i + 2, bytes := ⟨bs.toArray⟩ })
    {w : UInt8} {st : Ixon.GetState}
    (hok : Claim.getScope variant { idx := i, bytes := ⟨bs.toArray⟩ } = .ok w st) :
    w = valByte ∧ st = { idx := i + 2, bytes := ⟨bs.toArray⟩ } := by
  unfold Claim.getScope at hok
  simp only [bind, EStateM.bind, pure, EStateM.pure, h1] at hok
  by_cases hfmt : (fmt == Ixon.Env.OBJECT_FORMAT) = true
  case neg =>
    simp [hfmt, bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok
  simp only [hfmt, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure, h2] at hok
  by_cases hc1 : (valByte == Claim.validatorForVariant variant) = true
  · simp only [hc1, ↓reduceIte] at hok
    obtain ⟨hw, hst⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    exact ⟨hw.symm, hst⟩
  simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hc2 : (valByte == Claim.VALIDATOR_ERASED_LEAN_ASSUMED &&
      Claim.variantMayAssume variant) = true
  · simp only [hc2, ↓reduceIte] at hok
    obtain ⟨hw, hst⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    exact ⟨hw.symm, hst⟩
  simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hc3 : (valByte == Claim.VALIDATOR_ERASED_LEAN_CLASS &&
      variant == Claim.VARIANT_CHECK_ENV_CLAIM) = true
  · simp only [hc3, ↓reduceIte] at hok
    obtain ⟨hw, hst⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    exact ⟨hw.symm, hst⟩
  simp only [hc3, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hc4 : (Claim.validatorForVariant variant == Claim.VALIDATOR_ERASED_LEAN &&
      valByte == Claim.VALIDATOR_ERASED_LEAN_RETIRED) = true
  · simp [hc4, bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok
  · simp [hc4, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok

/-- A `binding` claim's payload is read at variant `10`. -/
private theorem bd_getPayload_binding_variant {variant : UInt64} {valByte : UInt8}
    {s : Ixon.GetState} {spec a : _root_.Address} {st : Ixon.GetState}
    (hok : Claim.getPayload variant valByte s = .ok (Claim.binding spec a) st) :
    variant = 10 := by
  unfold Claim.getPayload at hok
  by_cases hv3 : (variant == Claim.VARIANT_EVAL_CLAIM) = true
  · simp only [hv3, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨hc, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hc
  simp only [hv3, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv4 : (variant == Claim.VARIANT_CHECK_CLAIM) = true
  · simp only [hv4, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨hc, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hc
  simp only [hv4, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv5 : (variant == Claim.VARIANT_CHECK_ENV_CLAIM) = true
  · simp only [hv5, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨hc, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hc
  simp only [hv5, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv6 : (variant == Claim.VARIANT_REVEAL_CLAIM) = true
  · simp only [hv6, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨hc, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hc
  simp only [hv6, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv7 : (variant == Claim.VARIANT_CONTAINS_CLAIM) = true
  · simp only [hv7, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨hc, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hc
  simp only [hv7, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv8 : (variant == Claim.VARIANT_CATALOG_CLAIM) = true
  · simp only [hv8, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨hc, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hc
  simp only [hv8, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv10 : (variant == Claim.VARIANT_BINDING_CLAIM) = true
  · exact beq_iff_eq.mp hv10
  simp [hv10, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok

/-! ## `IxVM::verify_claim` on a binding claim -/

/-- **`IxVM::verify_claim` on a `binding spec a` claim**: the run hashed a collision with the
claim's bytes, or it called `KernelRoles::validate_binding` on the address `a`. -/
theorem verify_claim_decode_binding_spec
    {d : Digest} {value : SourceValue F} {heap : Heap F} {calls : List (Call F)}
    (ev : ObsFn W verifyClaim [digestValue d] [] value heap calls)
    {bytes : ByteArray} {c : Claim} (hde : Claim.de bytes = .ok c)
    (hpack : packDigest (Address.blake3Pure bytes) = d)
    {spec a : _root_.Address} (hcb : c = Claim.binding spec a) (V : View) :
    V.HashedCollision (bytes :: IxVM.Consistency.committedFootprint) calls ∨
      RoleVal.ValidateBindingIn calls a := by
  obtain ⟨cs_run, ev_run, hc_top⟩ := Obs.«IxVM::verify_claim».obs ev
  have hsub_run : ∀ cl ∈ cs_run, cl ∈ calls := fun cl hcl => by rw [hc_top]; simp [hcl]
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelClaim.run_claim.lookup
    (by simp [IxVM.KernelClaim.run_claim, ControlLower.hasControl]) ev_run
  simp only [IxVM.KernelClaim.run_claim] at d0
  -- 1. `let (idx, len) = hint::<(Field, Field)>("ixvm.io.claim", digest);`
  obtain ⟨v_hint, m_hint, bs_hint, c_hint, c1, d_hint, mt_hint, d1, rfl⟩ := d0.letValue_inv
  obtain ⟨_, _, d_harg, _, rfl⟩ := d_hint.hint_inv
  obtain ⟨_, rfl, rfl⟩ := d_harg.var_inv
  obtain ⟨_, -, -, ml_hint⟩ := matchPattern_tuple_inv mt_hint
  obtain ⟨x_idx, _, _, _, rfl, mt_idx, ml_hint1, rfl⟩ := matchListWith_cons_inv ml_hint
  obtain rfl := matchPattern_bind_inv mt_idx
  obtain ⟨x_len, _, _, _, rfl, mt_len, ml_hint2, rfl⟩ := matchListWith_cons_inv ml_hint1
  obtain rfl := matchPattern_bind_inv mt_len
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_hint2
  -- 2. `let bytes = IxByteStream::read_finite_byte_stream(0, idx, len);`
  obtain ⟨x_bytes, m_read, bs_read, c_read, c2, d_read, mt_read, d2, rfl⟩ := d1.letValue_inv
  obtain ⟨_, _, _, cs_read, a_read, ev_read, rfl⟩ := d_read.call_inv
  rw [instanceName_plain_some] at ev_read
  obtain ⟨_, _, _, _, _, rfl, d_r0, a_read1, rfl⟩ := a_read.cons_inv
  obtain ⟨rfl, rfl, rfl⟩ := d_r0.literal_inv
  obtain ⟨_, _, _, _, _, rfl, d_r1, a_read2, rfl⟩ := a_read1.cons_inv
  obtain ⟨l_r1, rfl, rfl⟩ := d_r1.var_inv; simp at l_r1; subst l_r1
  obtain ⟨_, _, _, _, _, rfl, d_r2, a_read3, rfl⟩ := a_read2.cons_inv
  obtain ⟨l_r2, rfl, rfl⟩ := d_r2.var_inv; simp at l_r2; subst l_r2
  obtain ⟨rfl, rfl, rfl⟩ := a_read3.nil_inv
  obtain rfl := matchPattern_bind_inv mt_read
  obtain ⟨_, rawBytes, hraw_lt, -, hst_raw⟩ := L1.read_finite_byte_stream_spec ev_read
  -- 3. `let h = Blake3::hash(bytes);`
  obtain ⟨x_h, m_hash, bs_hash, c_hash, c3, d_hash, mt_hash, d3, rfl⟩ := d2.letValue_inv
  obtain ⟨_, _, _, cs_hash, a_hash, ev_hash, rfl⟩ := d_hash.call_inv
  rw [instanceName_plain_some] at ev_hash
  obtain ⟨_, _, _, _, _, rfl, d_h0, a_hash1, rfl⟩ := a_hash.cons_inv
  obtain ⟨l_h0, rfl, rfl⟩ := d_h0.var_inv; simp at l_h0; subst l_h0
  obtain ⟨rfl, rfl, rfl⟩ := a_hash1.nil_inv
  obtain rfl := matchPattern_bind_inv mt_hash
  obtain ⟨ext_hash, rfl, hcv_raw⟩ :=
    L1.hash_digest_spec hst_raw (L1.native_of_lt hraw_lt) ev_hash
  have hhashed_raw : Hashed calls ⟨rawBytes.toArray⟩ :=
    L1.hashed_of_call (hsub_run _ (by simp [instanceName_plain_some])) hst_raw
  -- 4. `assert_eq!(Blake3::pack_digest(h), digest, ...);`
  obtain ⟨_, m_eq1, bs_eq1, c_eq1, c4, d_eq1, mt_eq1, d4, rfl⟩ := d3.letValue_inv
  obtain ⟨_, a_eq1, ap_eq1⟩ := d_eq1.builtin_inv
  obtain ⟨v_pd, _, m_pd, _, _, rfl, d_pd, a_eq1', rfl⟩ := a_eq1.cons_inv
  obtain ⟨_, _, _, cs_pd, a_pd, ev_pd, rfl⟩ := d_pd.call_inv
  rw [instanceName_plain_some] at ev_pd
  obtain ⟨_, _, _, _, _, rfl, d_pd0, a_pd1, rfl⟩ := a_pd.cons_inv
  obtain ⟨l_pd0, rfl, rfl⟩ := d_pd0.var_inv; simp at l_pd0; subst l_pd0
  obtain ⟨rfl, rfl, rfl⟩ := a_pd1.nil_inv
  obtain ⟨_, _, _, _, _, rfl, d_dig, a_eq1'', rfl⟩ := a_eq1'.cons_inv
  obtain ⟨l_dig, rfl, rfl⟩ := d_dig.var_inv; simp at l_dig; subst l_dig
  obtain ⟨rfl, rfl, rfl⟩ := a_eq1''.nil_inv
  obtain ⟨heq_pd, rfl⟩ := Builtin.assertEq_inv ap_eq1
  obtain rfl := matchPattern_wildcard_inv mt_eq1
  obtain ⟨hv_pd, rfl⟩ := pack_digest_spec ev_pd
  rw [hv_pd, hcv_raw] at heq_pd
  have hblk_eq : Address.blake3Pure ⟨rawBytes.toArray⟩ = Address.blake3Pure bytes := by
    apply packDigest_inj (bd_blake3Pure_hash_size _) (bd_blake3Pure_hash_size _)
    have hp := digestValue_inj heq_pd
    rw [← hpack] at hp
    rw [L1.blake3Pure_eq]
    exact hp
  by_cases heq_bytes : (⟨rawBytes.toArray⟩ : ByteArray) = bytes
  case neg =>
    exact .inl (.inl ⟨Address.blake3Pure bytes, bytes, ⟨rawBytes.toArray⟩,
      .inr (.inl ⟨by simp, rfl⟩), hhashed_raw, heq_bytes, hblk_eq⟩)
  -- No collision on the claim's bytes: `⟨rawBytes.toArray⟩ = bytes`
  rw [← heq_bytes] at hde
  -- Unpack `Claim.de ⟨rawBytes.toArray⟩ = .ok c`
  have hget_top : ∃ st_end, Claim.get { idx := 0, bytes := ⟨rawBytes.toArray⟩ } = .ok c st_end := by
    unfold Claim.de Ixon.runGetExact EStateM.run at hde
    cases hres : Claim.get { idx := 0, bytes := ⟨rawBytes.toArray⟩ } with
    | error e s => simp [hres] at hde
    | ok c' s =>
      simp only [hres] at hde
      by_cases hidx : s.idx = (ByteArray.mk rawBytes.toArray).size
      · simp [hidx] at hde; subst hde; exact ⟨s, rfl⟩
      · simp [hidx] at hde
  obtain ⟨st_end, hget_claim⟩ := hget_top
  -- 5. `let (tag, s) = IxonDeserialize::get_tagn4(bytes);`
  obtain ⟨v_tagn, m_tagn, bs_tagn, c_tagn, c5, d_tagn, mt_tagn, d5, rfl⟩ := d4.letValue_inv
  obtain ⟨_, _, _, cs_tagn, a_tagn, ev_tagn, rfl⟩ := d_tagn.call_inv
  rw [instanceName_plain_some] at ev_tagn
  obtain ⟨_, _, _, _, _, rfl, d_tn0, a_tn1, rfl⟩ := a_tagn.cons_inv
  obtain ⟨l_tn0, rfl, rfl⟩ := d_tn0.var_inv; simp at l_tn0; subst l_tn0
  obtain ⟨rfl, rfl, rfl⟩ := a_tn1.nil_inv
  obtain ⟨_, hv_tagn, -, ml_tagn⟩ := matchPattern_tuple_inv mt_tagn
  subst hv_tagn
  obtain ⟨x_tag0, _, _, _, rfl, mt_tag0, ml_tagn1, rfl⟩ := matchListWith_cons_inv ml_tagn
  obtain rfl := matchPattern_bind_inv mt_tag0
  obtain ⟨x_s0, _, _, _, rfl, mt_s0, ml_tagn2, rfl⟩ := matchListWith_cons_inv ml_tagn1
  obtain rfl := matchPattern_bind_inv mt_s0
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_tagn2
  obtain ⟨rfl, tag, n1, restPtr1, hok_tag, hs_n1, htagn_tup⟩ :=
    TagN.getTagN4_refines_at (i := 0) (by simpa using L1.Stream.mono ext_hash hst_raw) ev_tagn.erase
  simp only [Nat.zero_add] at hok_tag hs_n1
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htagn_tup
  obtain ⟨rfl, rfl⟩ := htagn_tup
  -- 6. `let (flag, size) = tag;`
  obtain ⟨v_ft, m_ft, bs_ft, c_ft, c6, d_ft, mt_ft, d6, rfl⟩ := d5.letValue_inv
  obtain ⟨l_ft, rfl, rfl⟩ := d_ft.var_inv; simp at l_ft
  obtain ⟨_, hv_ft, -, ml_ft⟩ := matchPattern_tuple_inv mt_ft
  rw [← l_ft] at hv_ft
  simp only [Value.tuple.injEq] at hv_ft
  subst hv_ft
  obtain ⟨x_flag, _, _, _, hxf, mt_flag, ml_ft1, rfl⟩ := matchListWith_cons_inv ml_ft
  obtain rfl := matchPattern_bind_inv mt_flag
  obtain ⟨x_size, _, _, _, hxs, mt_size, ml_ft2, rfl⟩ := matchListWith_cons_inv ml_ft1
  obtain rfl := matchPattern_bind_inv mt_size
  obtain ⟨_, rfl⟩ := matchListWith_nil_inv ml_ft2
  simp only [List.cons.injEq] at hxf
  obtain ⟨rfl, hxf'⟩ := hxf
  rw [← hxf'] at hxs
  simp only [List.cons.injEq] at hxs
  obtain ⟨rfl, _⟩ := hxs
  -- 7. `assert_eq!(flag, 14, ...);`
  obtain ⟨_, m_eq2, bs_eq2, c_eq2, c7, d_eq2, mt_eq2, d7, rfl⟩ := d6.letValue_inv
  have ext_eq2 := d_eq2.heap_extends
  obtain rfl := matchPattern_wildcard_inv mt_eq2
  -- 8. `let [_, sz1, sz2, sz3, sz4, sz5, sz6, sz7] = size;`
  obtain ⟨_, m_sz, bs_sz, c_sz, c8, d_sz, mt_sz, d8, rfl⟩ := d7.letValue_inv
  obtain ⟨l_sz0, rfl, rfl⟩ := d_sz.var_inv; simp at l_sz0
  obtain ⟨_, hv_sz, -, ml_sz0⟩ := matchPattern_array_inv mt_sz
  rw [← l_sz0, TagN.u64Value] at hv_sz
  simp only [Value.tuple.injEq] at hv_sz
  subst hv_sz
  obtain ⟨_, _, _, _, hsz0, mt_w0, ml_sz1, rfl⟩ := matchListWith_cons_inv ml_sz0
  obtain rfl := matchPattern_wildcard_inv mt_w0
  obtain ⟨sz1, _, _, _, hsz1, mt_w1, ml_sz2, rfl⟩ := matchListWith_cons_inv ml_sz1
  obtain rfl := matchPattern_bind_inv mt_w1
  obtain ⟨sz2, _, _, _, hsz2, mt_w2, ml_sz3, rfl⟩ := matchListWith_cons_inv ml_sz2
  obtain rfl := matchPattern_bind_inv mt_w2
  obtain ⟨sz3, _, _, _, hsz3, mt_w3, ml_sz4, rfl⟩ := matchListWith_cons_inv ml_sz3
  obtain rfl := matchPattern_bind_inv mt_w3
  obtain ⟨sz4, _, _, _, hsz4, mt_w4, ml_sz5, rfl⟩ := matchListWith_cons_inv ml_sz4
  obtain rfl := matchPattern_bind_inv mt_w4
  obtain ⟨sz5, _, _, _, hsz5, mt_w5, ml_sz6, rfl⟩ := matchListWith_cons_inv ml_sz5
  obtain rfl := matchPattern_bind_inv mt_w5
  obtain ⟨sz6, _, _, _, hsz6, mt_w6, ml_sz7, rfl⟩ := matchListWith_cons_inv ml_sz6
  obtain rfl := matchPattern_bind_inv mt_w6
  obtain ⟨sz7, _, _, _, hsz7, mt_w7, ml_sz8, rfl⟩ := matchListWith_cons_inv ml_sz7
  obtain rfl := matchPattern_bind_inv mt_w7
  obtain ⟨_, rfl⟩ := matchListWith_nil_inv ml_sz8
  -- 9. `assert_eq!(sz1 + ... + sz7, 0, ...);`
  obtain ⟨_, m_eq3, bs_eq3, c_eq3, c9, d_eq3, mt_eq3, d9, rfl⟩ := d8.letValue_inv
  have ext_eq3 := d_eq3.heap_extends
  obtain rfl := matchPattern_wildcard_inv mt_eq3
  -- 10. `let variant = size[0];`
  obtain ⟨x_variant, m_var, bs_var, c_var, c10, d_var, mt_var, d10, rfl⟩ := d9.letValue_inv
  obtain ⟨p_sz, d_szv, pr_sz0⟩ := d_var.index_inv
  obtain ⟨l_szv, rfl, rfl⟩ := d_szv.var_inv; simp at l_szv; subst l_szv
  obtain rfl := matchPattern_bind_inv mt_var
  -- 11. `let (format, s) = IxonDeserialize::read_byte(s);`
  obtain ⟨v_fmt, m_fmt, bs_fmt, c_fmt, c11, d_fmt, mt_fmt, d11, rfl⟩ := d10.letValue_inv
  obtain ⟨_, _, _, cs_fmt, a_fmt, ev_fmt, rfl⟩ := d_fmt.call_inv
  rw [instanceName_plain_some] at ev_fmt
  obtain ⟨_, _, _, _, _, rfl, d_f0, a_f1, rfl⟩ := a_fmt.cons_inv
  obtain ⟨l_f0, rfl, rfl⟩ := d_f0.var_inv; simp at l_f0; subst l_f0
  obtain ⟨rfl, rfl, rfl⟩ := a_f1.nil_inv
  obtain ⟨_, hv_fmt, -, ml_fmt⟩ := matchPattern_tuple_inv mt_fmt
  subst hv_fmt
  obtain ⟨x_fmt, _, _, _, rfl, mt_xfmt, ml_fmt1, rfl⟩ := matchListWith_cons_inv ml_fmt
  obtain rfl := matchPattern_bind_inv mt_xfmt
  obtain ⟨x_s1, _, _, _, rfl, mt_xs1, ml_fmt2, rfl⟩ := matchListWith_cons_inv ml_fmt1
  obtain rfl := matchPattern_bind_inv mt_xs1
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_fmt2
  obtain ⟨rfl, fmtByte, restFmt, _, hcons_fmt, hs_fmt, htup_fmt⟩ :=
    Deserialize.readByte_refines (L1.Stream.mono (ext_eq2.trans ext_eq3) hs_n1) ev_fmt.erase
  injection htup_fmt with htup_fmt'; simp only [List.cons.injEq, and_true] at htup_fmt'
  obtain ⟨rfl, rfl⟩ := htup_fmt'
  obtain ⟨hu8_fmt, hdrop_fmt, -⟩ := Deserialize.getU8_of_drop_cons hcons_fmt
  rw [← hdrop_fmt] at hs_fmt
  -- 12. `assert_eq!(UInt8::to_field(format), 4, ...);`
  obtain ⟨_, m_eq4, bs_eq4, c_eq4, c12, d_eq4, mt_eq4, d12, rfl⟩ := d11.letValue_inv
  have ext_eq4 := d_eq4.heap_extends
  obtain rfl := matchPattern_wildcard_inv mt_eq4
  -- 13. `let (validator, s) = IxonDeserialize::read_byte(s);`
  obtain ⟨v_val, m_val, bs_val, c_val, c13, d_val, mt_val, d13, rfl⟩ := d12.letValue_inv
  obtain ⟨_, _, _, cs_val, a_val, ev_val, rfl⟩ := d_val.call_inv
  rw [instanceName_plain_some] at ev_val
  obtain ⟨_, _, _, _, _, rfl, d_v0, a_v1, rfl⟩ := a_val.cons_inv
  obtain ⟨l_v0, rfl, rfl⟩ := d_v0.var_inv; simp at l_v0; subst l_v0
  obtain ⟨rfl, rfl, rfl⟩ := a_v1.nil_inv
  obtain ⟨_, hv_val, -, ml_val⟩ := matchPattern_tuple_inv mt_val
  subst hv_val
  obtain ⟨x_val, _, _, _, rfl, mt_xval, ml_val1, rfl⟩ := matchListWith_cons_inv ml_val
  obtain rfl := matchPattern_bind_inv mt_xval
  obtain ⟨x_s2, _, _, _, rfl, mt_xs2, ml_val2, rfl⟩ := matchListWith_cons_inv ml_val1
  obtain rfl := matchPattern_bind_inv mt_xs2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_val2
  obtain ⟨rfl, valByte, restVal, _, hcons_val, hs_val, htup_val⟩ :=
    Deserialize.readByte_refines (L1.Stream.mono ext_eq4 hs_fmt) ev_val.erase
  injection htup_val with htup_val'; simp only [List.cons.injEq, and_true] at htup_val'
  obtain ⟨rfl, rfl⟩ := htup_val'
  obtain ⟨hu8_val, hdrop_val, -⟩ := Deserialize.getU8_of_drop_cons hcons_val
  rw [← hdrop_val] at hs_val
  rw [Nat.add_assoc] at hu8_val hs_val
  -- Align `Claim.get` through `getTagN 4` and `getScope`
  unfold Claim.get at hget_claim
  simp only [bind, EStateM.bind, pure, EStateM.pure, hok_tag] at hget_claim
  by_cases hflag_ne : (tag.flag != Claim.FLAG_CLAIM) = true
  · simp [hflag_ne, bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hget_claim
  simp only [hflag_ne, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hget_claim
  by_cases hret9 : (tag.value == Claim.VARIANT_RESOURCE_CLAIM_RETIRED) = true
  · simp [hret9, bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hget_claim
  simp only [hret9, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hget_claim
  obtain ⟨w_val, st_scope, hok_scope, hok_payload⟩ := Ixon.Verify.TagN.bind_ok_inv hget_claim
  obtain ⟨hw_val, rfl⟩ := bd_getScope_ok_inv hu8_fmt hu8_val hok_scope
  subst w_val
  subst hcb
  have htv10 : tag.value = 10 := bd_getPayload_binding_variant hok_payload
  -- 14. `match UInt8::to_field(variant) { ... }`
  obtain ⟨v_scrut, m_scrut, bs_arm, body_arm, c_scrut, c_arm, d_scrut, sel_arm, d_arm, rfl⟩ :=
    d13.matchValue_inv
  obtain ⟨_, _, _, cs_scrut, a_scrut, ev_scrut, rfl⟩ := d_scrut.call_inv
  rw [instanceName_plain_some] at ev_scrut
  obtain ⟨_, _, _, _, _, rfl, d_sc0, a_sc1, rfl⟩ := a_scrut.cons_inv
  obtain ⟨l_sc0, rfl, rfl⟩ := d_sc0.var_inv; simp at l_sc0; subst l_sc0
  obtain ⟨rfl, rfl, rfl⟩ := a_sc1.nil_inv
  obtain ⟨hv_scrut, hm_scrut⟩ := L1.u8_toField ev_scrut
  subst v_scrut m_scrut
  have hsub_arm : ∀ cl ∈ c_arm, cl ∈ calls := fun cl hcl =>
    hsub_run cl (by simp [hcl])
  rw [htv10] at pr_sz0 hok_payload
  change projectValue (TagN.u64Value 10) 0 = .ok x_variant at pr_sz0
  simp only [TagN.u64Value, projectValue, List.getElem?_cons_zero, pure, Except.pure,
    Except.ok.injEq] at pr_sz0
  subst x_variant
  -- Select arm `10`: skip `3`, `4`, `5`, `6`, `7`, `9`
  rcases selectArm_cons_inv sel_arm with ⟨mt3, _⟩ | ⟨_, sel_arm1⟩
  · obtain ⟨heq3, _⟩ := MatchesConst.some_inv (MatchesConst.literal 3) mt3
    simp at heq3
    exact absurd heq3 (by decide)
  rcases selectArm_cons_inv sel_arm1 with ⟨mt4, _⟩ | ⟨_, sel_arm2⟩
  · obtain ⟨heq4, _⟩ := MatchesConst.some_inv (MatchesConst.literal 4) mt4
    simp at heq4
    exact absurd heq4 (by decide)
  rcases selectArm_cons_inv sel_arm2 with ⟨mt5, _⟩ | ⟨_, sel_arm3⟩
  · obtain ⟨heq5, _⟩ := MatchesConst.some_inv (MatchesConst.literal 5) mt5
    simp at heq5
    exact absurd heq5 (by decide)
  rcases selectArm_cons_inv sel_arm3 with ⟨mt6, _⟩ | ⟨_, sel_arm4⟩
  · obtain ⟨heq6, _⟩ := MatchesConst.some_inv (MatchesConst.literal 6) mt6
    simp at heq6
    exact absurd heq6 (by decide)
  rcases selectArm_cons_inv sel_arm4 with ⟨mt7, _⟩ | ⟨_, sel_arm5⟩
  · obtain ⟨heq7, _⟩ := MatchesConst.some_inv (MatchesConst.literal 7) mt7
    simp at heq7
    exact absurd heq7 (by decide)
  rcases selectArm_cons_inv sel_arm5 with ⟨mt9, _⟩ | ⟨_, sel_arm6⟩
  · obtain ⟨heq9, _⟩ := MatchesConst.some_inv (MatchesConst.literal 9) mt9
    simp at heq9
    exact absurd heq9 (by decide)
  rcases selectArm_cons_inv sel_arm6 with ⟨mt10, rfl⟩ | ⟨nm10, _⟩
  case inr =>
    exact absurd rfl (MatchesConst.none_inv (MatchesConst.literal 10) nm10)
  obtain ⟨_, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 10) mt10
  -- Arm 10 body:
  -- `assert_eq!(UInt8::to_field(validator), 3, ...);`
  obtain ⟨_, m_b1, bs_b1, c_b1, cb1, d_b1, mt_b1, db1, rfl⟩ := d_arm.letValue_inv
  have ext_b1 := d_b1.heap_extends
  obtain rfl := matchPattern_wildcard_inv mt_b1
  -- `let (spec, s2) = IxonDeserialize::get_address(s);`
  obtain ⟨_, m_sp, bs_sp, c_sp, cb2, d_sp, mt_sp, db2, rfl⟩ := db1.letValue_inv
  obtain ⟨_, _, _, cs_sp, a_sp, ev_sp, rfl⟩ := d_sp.call_inv
  rw [instanceName_plain_some] at ev_sp
  obtain ⟨_, _, _, _, _, rfl, d_sp0, a_sp1, rfl⟩ := a_sp.cons_inv
  obtain ⟨l_sp0, rfl, rfl⟩ := d_sp0.var_inv; simp at l_sp0; subst l_sp0
  obtain ⟨rfl, rfl, rfl⟩ := a_sp1.nil_inv
  obtain ⟨_, hv_sp, -, ml_sp⟩ := matchPattern_tuple_inv mt_sp
  subst hv_sp
  obtain ⟨x_spec, _, _, _, rfl, mt_xsp, ml_sp1, rfl⟩ := matchListWith_cons_inv ml_sp
  obtain rfl := matchPattern_bind_inv mt_xsp
  obtain ⟨x_s3, _, _, _, rfl, mt_xs3, ml_sp2, rfl⟩ := matchListWith_cons_inv ml_sp1
  obtain rfl := matchPattern_bind_inv mt_xs3
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_sp2
  -- `assert_eq!(Bytes::address_eq(spec, KernelRoleSpec::spec_digest()), 1, ...);`
  obtain ⟨_, m_b3, bs_b3, c_b3, cb3, d_b3, mt_b3, db3, rfl⟩ := db2.letValue_inv
  have ext_b3 := d_b3.heap_extends
  obtain rfl := matchPattern_wildcard_inv mt_b3
  -- `let (binding, rest) = IxonDeserialize::get_address(s2);`
  obtain ⟨_, m_bd, bs_bd, c_bd, cb4, d_bd, mt_bd, db4, rfl⟩ := db3.letValue_inv
  obtain ⟨_, _, _, cs_bd, a_bd, ev_bd, rfl⟩ := d_bd.call_inv
  rw [instanceName_plain_some] at ev_bd
  obtain ⟨_, _, _, _, _, rfl, d_bd0, a_bd1, rfl⟩ := a_bd.cons_inv
  obtain ⟨l_bd0, rfl, rfl⟩ := d_bd0.var_inv; simp at l_bd0; subst l_bd0
  obtain ⟨rfl, rfl, rfl⟩ := a_bd1.nil_inv
  obtain ⟨_, hv_bd, -, ml_bd⟩ := matchPattern_tuple_inv mt_bd
  subst hv_bd
  obtain ⟨x_binding, _, _, _, rfl, mt_xbd, ml_bd1, rfl⟩ := matchListWith_cons_inv ml_bd
  obtain rfl := matchPattern_bind_inv mt_xbd
  obtain ⟨x_rest, _, _, _, rfl, mt_xrest, ml_bd2, rfl⟩ := matchListWith_cons_inv ml_bd1
  obtain rfl := matchPattern_bind_inv mt_xrest
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_bd2
  -- `let Lists::Node::Nil = (*(rest));`
  obtain ⟨_, m_nil, bs_nil, c_nil, cb5, d_nil, mt_nil, db5, rfl⟩ := db4.letValue_inv
  obtain ⟨_, d_nil_v, _⟩ := d_nil.load_inv
  obtain ⟨_, rfl, rfl⟩ := d_nil_v.var_inv
  obtain ⟨_, _, -, ml_nil⟩ := matchPattern_construct_inv mt_nil
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_nil
  -- `KernelRoles::validate_binding(binding)`
  obtain ⟨_, _, _, cs_vb, a_vb, ev_vb, rfl⟩ := db5.call_inv
  rw [instanceName_plain_some] at ev_vb
  obtain ⟨_, _, _, _, _, rfl, d_vb0, a_vb1, rfl⟩ := a_vb.cons_inv
  obtain ⟨l_vb0, rfl, rfl⟩ := d_vb0.var_inv; simp at l_vb0; subst l_vb0
  obtain ⟨rfl, rfl, rfl⟩ := a_vb1.nil_inv
  -- Align `getPayload 10 valByte` with the two `get_address` calls
  obtain ⟨ext_sp, hlen_sp, _, _, htup_sp, haddr_sp, hs_sp⟩ :=
    Deserialize.getAddress_refines (L1.Stream.mono ext_b1 hs_val) ev_sp.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_sp
  obtain ⟨rfl, rfl⟩ := htup_sp
  rw [List.drop_drop] at hs_sp
  have hget_sp := getAddress_of_drop hlen_sp
  obtain ⟨ext_bd, hlen_bd, _, _, htup_bd, haddr_bd, hs_bd⟩ :=
    Deserialize.getAddress_refines (L1.Stream.mono ext_b3 hs_sp) ev_bd.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_bd
  obtain ⟨rfl, rfl⟩ := htup_bd
  have hget_bd := getAddress_of_drop hlen_bd
  unfold Claim.getPayload at hok_payload
  have hv3_f : (10 == Claim.VARIANT_EVAL_CLAIM) = false := rfl
  have hv4_f : (10 == Claim.VARIANT_CHECK_CLAIM) = false := rfl
  have hv5_f : (10 == Claim.VARIANT_CHECK_ENV_CLAIM) = false := rfl
  have hv6_f : (10 == Claim.VARIANT_REVEAL_CLAIM) = false := rfl
  have hv7_f : (10 == Claim.VARIANT_CONTAINS_CLAIM) = false := rfl
  have hv8_f : (10 == Claim.VARIANT_CATALOG_CLAIM) = false := rfl
  have hv10_t : (10 == Claim.VARIANT_BINDING_CLAIM) = true := rfl
  simp only [hv3_f, hv4_f, hv5_f, hv6_f, hv7_f, hv8_f, hv10_t, Bool.false_eq_true, ↓reduceIte,
    bind, EStateM.bind, pure, EStateM.pure, hget_sp, hget_bd] at hok_payload
  obtain ⟨hc, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok_payload
  injection hc with hspec_eq ha_eq
  subst ha_eq
  exact .inr ⟨_, _, x_binding, _, cs_vb, ⟨_, haddr_bd, rfl⟩, ev_vb,
    fun cl hcl => hsub_arm cl (by simp [instanceName_plain_some, hcl])⟩

end IxVM.Refinement.Claim

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

/-- **The decode of an accepted binding claim, from the observed `verify_claim` derivation**:
the first named part of the binding claim's export. -/
theorem bindingClaimDecodes_of_run {d : Digest} {value : SourceValue F} {heap : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn Core.W verifyClaim [digestValue d] [] value heap calls) :
    BindingClaimDecodes calls d :=
  fun _ _ _ hde hdig V => Claim.verify_claim_decode_binding_spec ev hde hdig rfl V

/-- **The binding claim's export from the three parts that remain**: the loaded table's
admission, the prelude pin and the stores of a run. -/
theorem bindingClaimExport_of_table_and_stores
    (tableAdmits : LoadedTableAdmits)
    (preludePins : LoadedTablePinsPrelude)
    (groupStores : ∀ calls, GroupStoresOfRun calls) :
    SourceSoundBounded fun calls d => BindingClaimExportObs (BindingRun calls) calls d :=
  bindingClaimExport_of_parts (fun _ _ _ _ ev => bindingClaimDecodes_of_run ev) tableAdmits
    preludePins groupStores

end IxVM.Refinement.Binding
