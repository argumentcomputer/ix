import IxVMRefinement.Claim.TopBase
import IxVMRefinement.Claim.Decode

/-! # Claim decoding for a typing claim at a role-context limit

`verify_claim_decode_typing_spec` inverts `IxVM::verify_claim` (`KernelClaim::run_claim`) on a
typing claim in scope (`InScopeTyping`: a `check` or `checkEnv` claim that names no user axioms,
assumes no leaves and is not a literal class), whether it validates its role table (validator
`3`) or assumes it (validator `4`), for a table `t` admitted at the address its context names.
The run hashed a collision with the claim's bytes, the table's bytes or the committed footprint,
or it loaded the context at the limit `some 77` or `none` (`load_role_ctx_lim_spec`) and called
the seed's check (`assert_claimable`, `run_check_transitive`) or the walk of the leaves
(`walk_leaves_owned`) under it. The proof is that of `verify_claim_decode_spec` with the table
taken from its admission and the context represented at its limit (`RCLimRep`). -/

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

private theorem td_blake3Pure_hash_size (b : ByteArray) :
    (Address.blake3Pure b).hash.size = 32 := by
  cases b with
  | mk arr =>
    have h := Ingress.blake3Pure_eq arr.toList
    simp only [Array.toArray_toList] at h
    rw [h]
    exact (Blake3.Pure.digest arr.toList).size_toArray

private theorem td_getScope_ok_inv {variant : UInt64} {bs : List UInt8} {i : Nat}
    {fmt valByte : UInt8}
    (h1 : Ixon.getU8 { idx := i, bytes := ⟨bs.toArray⟩ } =
      .ok fmt { idx := i + 1, bytes := ⟨bs.toArray⟩ })
    (h2 : Ixon.getU8 { idx := i + 1, bytes := ⟨bs.toArray⟩ } =
      .ok valByte { idx := i + 2, bytes := ⟨bs.toArray⟩ })
    {w : UInt8} {st : Ixon.GetState}
    (hok : Claim.getScope variant { idx := i, bytes := ⟨bs.toArray⟩ } = .ok w st) :
    w = valByte ∧ st = { idx := i + 2, bytes := ⟨bs.toArray⟩ } ∧
      (valByte = Claim.validatorForVariant variant ∨
        valByte = Claim.VALIDATOR_ERASED_LEAN_ASSUMED ∨
        valByte = Claim.VALIDATOR_ERASED_LEAN_CLASS) := by
  unfold Claim.getScope at hok
  simp only [bind, EStateM.bind, pure, EStateM.pure, h1] at hok
  by_cases hfmt : (fmt == Ixon.Env.OBJECT_FORMAT) = true
  case neg =>
    simp [hfmt, bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok
  simp only [hfmt, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure, h2] at hok
  by_cases hc1 : (valByte == Claim.validatorForVariant variant) = true
  · simp only [hc1, ↓reduceIte] at hok
    obtain ⟨hw, hst⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    exact ⟨hw.symm, hst, .inl (beq_iff_eq.mp hc1)⟩
  simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hc2 : (valByte == Claim.VALIDATOR_ERASED_LEAN_ASSUMED &&
      Claim.variantMayAssume variant) = true
  · simp only [hc2, ↓reduceIte] at hok
    obtain ⟨hw, hst⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    exact ⟨hw.symm, hst, .inr (.inl (beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp hc2).1))⟩
  simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hc3 : (valByte == Claim.VALIDATOR_ERASED_LEAN_CLASS &&
      variant == Claim.VARIANT_CHECK_ENV_CLAIM) = true
  · simp only [hc3, ↓reduceIte] at hok
    obtain ⟨hw, hst⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    exact ⟨hw.symm, hst, .inr (.inr (beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp hc3).1))⟩
  simp only [hc3, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hc4 : (Claim.validatorForVariant variant == Claim.VALIDATOR_ERASED_LEAN &&
      valByte == Claim.VALIDATOR_ERASED_LEAN_RETIRED) = true
  · simp [hc4, bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok
  · simp [hc4, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok

/-- A typing claim in scope is a `check` (variant `4`) or `checkEnv` (variant `5`) claim. -/
private theorem td_getPayload_typing_variant {variant : UInt64} {valByte : UInt8}
    {s : Ixon.GetState} {c : Claim} {st : Ixon.GetState}
    (hok : Claim.getPayload variant valByte s = .ok c st)
    (hscope : IxVM.Consistency.InScopeTyping c) :
    variant = 4 ∨ variant = 5 := by
  unfold Claim.getPayload at hok
  by_cases hv3 : (variant == Claim.VARIANT_EVAL_CLAIM) = true
  · simp only [hv3, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hscope
  simp only [hv3, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv4 : (variant == Claim.VARIANT_CHECK_CLAIM) = true
  · exact .inl (beq_iff_eq.mp hv4)
  simp only [hv4, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv5 : (variant == Claim.VARIANT_CHECK_ENV_CLAIM) = true
  · exact .inr (beq_iff_eq.mp hv5)
  simp only [hv5, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv6 : (variant == Claim.VARIANT_REVEAL_CLAIM) = true
  · simp only [hv6, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hscope
  simp only [hv6, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv7 : (variant == Claim.VARIANT_CONTAINS_CLAIM) = true
  · simp only [hv7, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hscope
  simp only [hv7, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv8 : (variant == Claim.VARIANT_CATALOG_CLAIM) = true
  · simp only [hv8, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hscope
  simp only [hv8, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv10 : (variant == Claim.VARIANT_BINDING_CLAIM) = true
  · simp only [hv10, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hscope
  simp [hv10, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok

/-- **`KernelRoles::role_ctx_axioms` at a limit**: the empty user-axiom map, in both modes. -/
private theorem td_role_ctx_axioms_lim_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {x_rc r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc)
    (ev : ObsFn W "KernelRoles::role_ctx_axioms" [x_rc] h r h' calls) :
    r = .construct addrMapEnum "Nil" [] ∧ h' = h := by
  obtain ⟨tbl, htbl, ⟨n, -, -, hl⟩ | ⟨-, hl⟩⟩ := hrc.cases
  · rcases Obs.«KernelRoles::role_ctx_axioms».obs ev with
      ⟨_, _, x_axioms, ld12, rfl, rfl, -⟩ | ⟨_, _, ld12, -⟩ | ⟨_, _, _, _, ld12, -⟩ | ⟨_, _, _, ld12, -⟩
    · rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      exact ⟨hargs.2.2.symm, rfl⟩
    · rw [hl] at ld12
      simp at ld12
    · rw [hl] at ld12
      simp at ld12
    · rw [hl] at ld12
      simp at ld12
  · rcases Obs.«KernelRoles::role_ctx_axioms».obs ev with
      ⟨_, _, _, ld12, -⟩ | ⟨_, x_axioms, ld12, rfl, rfl, -⟩ | ⟨_, _, _, _, ld12, -⟩ | ⟨_, _, _, ld12, -⟩
    · rw [hl] at ld12
      simp at ld12
    · rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      exact ⟨hargs.2.symm, rfl⟩
    · rw [hl] at ld12
      simp at ld12
    · rw [hl] at ld12
      simp at ld12

/-- **`KernelClaim::run_check_env` on `asm = None` at a limit**: `run_check_env_none_spec` over
`RCLimRep`. -/
private theorem td_run_check_env_none_lim_spec {V : View} {extra : List ByteArray}
    {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Option Nat}
    {tTree : AssumptionTree} (htTree : tTree ∈ V.trees)
    {x_rc x_env_root r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc)
    (hroot : BaseSeams.addr h x_env_root (treeRoot tTree))
    (ev : ObsFn W "KernelClaim::run_check_env"
      [x_rc, x_env_root, .construct Obs.Names.«Options::Option<&[Field; 32]>» "None" []]
      h r h' calls) :
    V.HashedCollision extra calls ∨
    ∃ (as : List Bytes.Address) (m₁ : Heap F) (x_leaves : SourceValue F) (cs₁ : List (Call F)),
      treeLeaves tTree ≠ [] ∧
      as.map ixAddr = treeLeaves tTree ∧
      RCLimRep t bAddr lim m₁ x_rc ∧
      RepList addrListEnum (Bytes.RepAddressRef addrTy) m₁ as x_leaves ∧
      ObsFn W "KernelClaim::walk_leaves_owned" [x_rc, x_leaves] m₁ r h' cs₁ ∧
      (⟨"KernelClaim::walk_leaves_owned", [x_rc, x_leaves], m₁⟩ : Call F) ∈ calls ∧
      (∀ cl ∈ cs₁, cl ∈ calls) := by
  rcases Obs.«KernelClaim::run_check_env».obs ev with
    ⟨v1, m2, cs12, v98, m99, cs101, m124, cs135, cs155,
      ev14, sg106, _, ev137, ev157, hc174⟩ |
    ⟨v1, m2, cs12, v98, m99, cs101, m124, cs135, _, _, _, _, _, _, _, _, _,
      ev14, sg106, _, ev137, _, _, hc264⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, hne266, _⟩
  · rcases load_assumption_tree_spec (V := V) (extra := extra) htTree hroot ev14 with
      hcoll | ⟨ext1, as, hmap, hlLeaves⟩
    · exact .inl (hashedCollision_mono (by intro c hc; rw [hc174]; simp [hc]) hcoll)
    · rcases sg106 with ⟨_, heq67, _, _, _⟩ | ⟨w80, w81, ld34, _, hm99, hc101⟩
      · simp at heq67
      · subst m99 cs101
        obtain ⟨a0, as0, hcons_as, _, _⟩ := Lib.rep_cons_of_load hlLeaves ld34
        have hne_leaves : treeLeaves tTree ≠ [] := by
          rw [← hmap, hcons_as]; simp
        have hrc2 := hrc.mono ext1
        obtain ⟨_, hm124⟩ := td_role_ctx_axioms_lim_spec hrc2 ev137
        subst m124
        exact .inr ⟨as, m2, v1, cs155, hne_leaves, hmap, hrc2, hlLeaves, ev157,
          by rw [hc174]; simp, fun cl hcl => by rw [hc174]; simp [hcl]⟩
  · rcases load_assumption_tree_spec (V := V) (extra := extra) htTree hroot ev14 with
      hcoll | ⟨ext1, _, _, _⟩
    · exact .inl (hashedCollision_mono (by intro c hc; rw [hc264]; simp [hc]) hcoll)
    · have hm99 : m99 = m2 := by
        rcases sg106 with ⟨_, _, _, hm, _⟩ | ⟨_, _, _, _, hm, _⟩ <;> exact hm
      subst hm99
      obtain ⟨hax, _⟩ := td_role_ctx_axioms_lim_spec (hrc.mono ext1) ev137
      simp at hax
  · exact absurd rfl (hne266 [] rfl)

/-- The context `load_role_ctx_lim_spec` loads is at the limit `some 77` or `none`. -/
private theorem td_lim_of {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {x_v r : SourceValue F} {h : Heap F}
    (hok : (x_v = .field 3 ∧ RCLimRep t bAddr (some 77) h r) ∨
      (x_v = .field 4 ∧ RCLimRep t bAddr none h r)) :
    ∃ lim : Option Nat, (lim = some 77 ∨ lim = none) ∧ RCLimRep t bAddr lim h r := by
  rcases hok with ⟨-, hr⟩ | ⟨-, hr⟩
  · exact ⟨_, .inl rfl, hr⟩
  · exact ⟨_, .inr rfl, hr⟩

/-! ## `IxVM::verify_claim` on a typing claim in scope -/

/-- **`IxVM::verify_claim` on a typing claim in scope** (`InScopeTyping`), for a table `t`
admitted at the address the claim's context names from the bytes `tb`: the run hashed a
collision with the claim's bytes, `tb` or the committed footprint, or it loaded the context at
the limit `some 77` (validator `3`) or `none` (validator `4`) and called, for `check`, the
seed's `assert_claimable` and `run_check_transitive`, and for `checkEnv`, `walk_leaves_owned`
on the tree's leaves. -/
theorem verify_claim_decode_typing_spec
    {d : Digest} {value : SourceValue F} {heap : Heap F} {calls : List (Call F)}
    (ev : ObsFn W verifyClaim [digestValue d] [] value heap calls)
    {bytes : ByteArray} {c : Claim} (hde : Claim.de bytes = .ok c)
    (hpack : packDigest (Address.blake3Pure bytes) = d)
    (hscope : IxVM.Consistency.InScopeTyping c)
    {V : View} {seeds : List _root_.Address} (hseeds : IxVM.Consistency.ClaimSeeds c V seeds)
    {ctx : ClaimContext} (hctx : c.context? = some ctx) {tb : ByteArray}
    {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨ctx.binding, tb⟩ = .ok t) :
    V.HashedCollision (bytes :: tb :: IxVM.Consistency.committedFootprint) calls ∨
    ∃ lim : Option Nat, (lim = some 77 ∨ lim = none) ∧
      ((∃ (a : _root_.Address) (h₁ h₂ h₃ : Heap F) (x_rc x_a v₁ v₂ : SourceValue F)
          (cs₁ cs₂ : List (Call F)),
          seeds = [a] ∧ RCLimRep t ctx.binding lim h₁ x_rc ∧ BaseSeams.addr h₁ x_a a ∧
          ObsFn W "KernelClaim::assert_claimable" [x_rc, x_a] h₁ v₁ h₂ cs₁ ∧
          ObsFn W "KernelClaim::run_check_transitive" [x_rc, x_a] h₂ v₂ h₃ cs₂ ∧
          (⟨"KernelClaim::assert_claimable", [x_rc, x_a], h₁⟩ : Call F) ∈ calls ∧
          (⟨"KernelClaim::run_check_transitive", [x_rc, x_a], h₂⟩ : Call F) ∈ calls ∧
          (∀ cl ∈ cs₁, cl ∈ calls) ∧ (∀ cl ∈ cs₂, cl ∈ calls)) ∨
       (∃ (as : List Bytes.Address) (h₁ h₂ : Heap F) (x_rc x_leaves v₁ : SourceValue F)
          (cs₁ : List (Call F)),
          seeds ≠ [] ∧ as.map ixAddr = seeds ∧ RCLimRep t ctx.binding lim h₁ x_rc ∧
          RepList addrListEnum (Bytes.RepAddressRef addrTy) h₁ as x_leaves ∧
          ObsFn W "KernelClaim::walk_leaves_owned" [x_rc, x_leaves] h₁ v₁ h₂ cs₁ ∧
          (⟨"KernelClaim::walk_leaves_owned", [x_rc, x_leaves], h₁⟩ : Call F) ∈ calls ∧
          (∀ cl ∈ cs₁, cl ∈ calls))) := by
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
  obtain ⟨_, rawBytes, hraw_lt, -, hst_raw⟩ := Ingress.read_finite_byte_stream_spec ev_read
  -- 3. `let h = Blake3::hash(bytes);`
  obtain ⟨x_h, m_hash, bs_hash, c_hash, c3, d_hash, mt_hash, d3, rfl⟩ := d2.letValue_inv
  obtain ⟨_, _, _, cs_hash, a_hash, ev_hash, rfl⟩ := d_hash.call_inv
  rw [instanceName_plain_some] at ev_hash
  obtain ⟨_, _, _, _, _, rfl, d_h0, a_hash1, rfl⟩ := a_hash.cons_inv
  obtain ⟨l_h0, rfl, rfl⟩ := d_h0.var_inv; simp at l_h0; subst l_h0
  obtain ⟨rfl, rfl, rfl⟩ := a_hash1.nil_inv
  obtain rfl := matchPattern_bind_inv mt_hash
  obtain ⟨ext_hash, rfl, hcv_raw⟩ :=
    Ingress.hash_digest_spec hst_raw (Ingress.native_of_lt hraw_lt) ev_hash
  have hhashed_raw : Hashed calls ⟨rawBytes.toArray⟩ :=
    Ingress.hashed_of_call (hsub_run _ (by simp [instanceName_plain_some])) hst_raw
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
    apply packDigest_inj (td_blake3Pure_hash_size _) (td_blake3Pure_hash_size _)
    have hp := digestValue_inj heq_pd
    rw [← hpack] at hp
    rw [Ingress.blake3Pure_eq]
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
    TagN.getTagN4_refines_at (i := 0) (by simpa using Ingress.Stream.mono ext_hash hst_raw) ev_tagn.erase
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
    Deserialize.readByte_refines (Ingress.Stream.mono (ext_eq2.trans ext_eq3) hs_n1) ev_fmt.erase
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
    Deserialize.readByte_refines (Ingress.Stream.mono ext_eq4 hs_fmt) ev_val.erase
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
  obtain ⟨hw_val, rfl, hval_ok⟩ := td_getScope_ok_inv hu8_fmt hu8_val hok_scope
  subst w_val
  have hvar_45 := td_getPayload_typing_variant hok_payload hscope
  -- 14. `match UInt8::to_field(variant) { ... }`
  obtain ⟨v_scrut, m_scrut, bs_arm, body_arm, c_scrut, c_arm, d_scrut, sel_arm, d_arm, rfl⟩ :=
    d13.matchValue_inv
  obtain ⟨_, _, _, cs_scrut, a_scrut, ev_scrut, rfl⟩ := d_scrut.call_inv
  rw [instanceName_plain_some] at ev_scrut
  obtain ⟨_, _, _, _, _, rfl, d_sc0, a_sc1, rfl⟩ := a_scrut.cons_inv
  obtain ⟨l_sc0, rfl, rfl⟩ := d_sc0.var_inv; simp at l_sc0; subst l_sc0
  obtain ⟨rfl, rfl, rfl⟩ := a_sc1.nil_inv
  obtain ⟨hv_scrut, hm_scrut⟩ := Ingress.u8_toField ev_scrut
  subst v_scrut m_scrut
  have hsub_arm : ∀ cl ∈ c_arm, cl ∈ calls := fun cl hcl =>
    hsub_run cl (by simp [hcl])
  rcases hvar_45 with htv4 | htv5
  · -- Variant 4 (`Claim.check`)
    rw [htv4] at pr_sz0 hok_payload hval_ok
    change projectValue (TagN.u64Value 4) 0 = .ok x_variant at pr_sz0
    simp only [TagN.u64Value, projectValue, List.getElem?_cons_zero, pure, Except.pure,
      Except.ok.injEq] at pr_sz0
    subst x_variant
    -- Select arm `4`: skip `3`, match `4`
    rcases selectArm_cons_inv sel_arm with ⟨mt3, _⟩ | ⟨_, sel_arm1⟩
    · obtain ⟨heq34, _⟩ := MatchesConst.some_inv (MatchesConst.literal 3) mt3
      simp at heq34
      exact absurd heq34 (by decide)
    rcases selectArm_cons_inv sel_arm1 with ⟨mt4, rfl⟩ | ⟨nm4, _⟩
    case inr =>
      exact absurd rfl (MatchesConst.none_inv (MatchesConst.literal 4) nm4)
    obtain ⟨_, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 4) mt4
    -- `match UInt8::to_field(validator) { 10 => ..., 11 => ..., _ => ... }`
    obtain ⟨v_vsc, m_vsc, bs_varm, body_varm, c_vsc, c_varm, d_vsc, sel_varm, d_arm, rfl⟩ :=
      d_arm.matchValue_inv
    obtain ⟨_, _, _, cs_vsc, a_vsc, ev_vsc, rfl⟩ := d_vsc.call_inv
    rw [instanceName_plain_some] at ev_vsc
    obtain ⟨_, _, _, _, _, rfl, d_vsc0, a_vsc1, rfl⟩ := a_vsc.cons_inv
    obtain ⟨l_vsc0, rfl, rfl⟩ := d_vsc0.var_inv; simp at l_vsc0; subst l_vsc0
    obtain ⟨rfl, rfl, rfl⟩ := a_vsc1.nil_inv
    obtain ⟨rfl, rfl⟩ := Ingress.u8_toField ev_vsc
    have hsub_arm : ∀ cl ∈ c_varm, cl ∈ calls := fun cl hcl =>
      hsub_arm cl (by simp [hcl])
    rcases selectArm_cons_inv sel_varm with ⟨mt10, _⟩ | ⟨_, sel_varm1⟩
    · obtain ⟨heq10, _⟩ := MatchesConst.some_inv (MatchesConst.literal 10) mt10
      rcases hval_ok with rfl | rfl | rfl <;>
        exact absurd (Value.field.inj heq10) (by decide)
    rcases selectArm_cons_inv sel_varm1 with ⟨mt11, _⟩ | ⟨_, sel_varm2⟩
    · obtain ⟨heq11, _⟩ := MatchesConst.some_inv (MatchesConst.literal 11) mt11
      rcases hval_ok with rfl | rfl | rfl <;>
        exact absurd (Value.field.inj heq11) (by decide)
    rcases selectArm_cons_inv sel_varm2 with ⟨mt_w, rfl⟩ | ⟨nm_w, _⟩
    case inr => exact (matchPattern_wildcard_none nm_w).elim
    obtain rfl := matchPattern_wildcard_inv mt_w
    -- Arm 4 body:
    -- `let (binding, axioms, s) = get_claim_context(s);`
    obtain ⟨_, m_ctx, bs_ctx, c_ctx, ca1, d_ctx, mt_ctx, da1, rfl⟩ := d_arm.letValue_inv
    obtain ⟨_, _, _, cs_ctx, a_ctx, ev_ctx, rfl⟩ := d_ctx.call_inv
    rw [instanceName_plain_some] at ev_ctx
    obtain ⟨_, _, _, _, _, rfl, d_cx0, a_cx1, rfl⟩ := a_ctx.cons_inv
    obtain ⟨l_cx0, rfl, rfl⟩ := d_cx0.var_inv; simp at l_cx0; subst l_cx0
    obtain ⟨rfl, rfl, rfl⟩ := a_cx1.nil_inv
    obtain ⟨_, hv_ctx, -, ml_ctx⟩ := matchPattern_tuple_inv mt_ctx
    subst hv_ctx
    obtain ⟨x_binding, _, _, _, rfl, mt_xb, ml_ctx1, rfl⟩ := matchListWith_cons_inv ml_ctx
    obtain rfl := matchPattern_bind_inv mt_xb
    obtain ⟨x_axioms, _, _, _, rfl, mt_xax, ml_ctx2, rfl⟩ := matchListWith_cons_inv ml_ctx1
    obtain rfl := matchPattern_bind_inv mt_xax
    obtain ⟨x_s3, _, _, _, rfl, mt_xs3, ml_ctx3, rfl⟩ := matchListWith_cons_inv ml_ctx2
    obtain rfl := matchPattern_bind_inv mt_xs3
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_ctx3
    obtain ⟨ext_ctx, ctx₀, kCtx, _, _, _, hget_ctx, htup_ctx, haddr_bind, hax_none, hs_ctx⟩ :=
      get_claim_context_spec hs_val ev_ctx
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_ctx
    obtain ⟨rfl, rfl, rfl⟩ := htup_ctx
    -- `let rc = KernelRoles::load_role_ctx(binding, UInt8::to_field(validator), axioms);`
    obtain ⟨x_rc, m_rc, bs_rc, c_rc, ca2, d_rc, mt_rc, da2, rfl⟩ := da1.letValue_inv
    obtain ⟨_, _, _, cs_rc, a_rc, ev_rc, rfl⟩ := d_rc.call_inv
    rw [instanceName_plain_some] at ev_rc
    obtain ⟨_, _, _, _, _, rfl, d_rc0, a_rc1, rfl⟩ := a_rc.cons_inv
    obtain ⟨l_rc0, rfl, rfl⟩ := d_rc0.var_inv; simp at l_rc0; subst l_rc0
    obtain ⟨_, _, _, _, _, rfl, d_rc1, a_rc2, rfl⟩ := a_rc1.cons_inv
    obtain ⟨_, _, _, cs_rc_v, a_rc_v, ev_rc_v, rfl⟩ := d_rc1.call_inv
    rw [instanceName_plain_some] at ev_rc_v
    obtain ⟨_, _, _, _, _, rfl, d_rcv0, a_rcv1, rfl⟩ := a_rc_v.cons_inv
    obtain ⟨l_rcv0, rfl, rfl⟩ := d_rcv0.var_inv; simp at l_rcv0; subst l_rcv0
    obtain ⟨rfl, rfl, rfl⟩ := a_rcv1.nil_inv
    obtain ⟨rfl, rfl⟩ := Ingress.u8_toField ev_rc_v
    obtain ⟨_, _, _, _, _, rfl, d_rc2, a_rc3, rfl⟩ := a_rc2.cons_inv
    obtain ⟨l_rc2, rfl, rfl⟩ := d_rc2.var_inv; simp at l_rc2; subst l_rc2
    obtain ⟨rfl, rfl, rfl⟩ := a_rc3.nil_inv
    obtain rfl := matchPattern_bind_inv mt_rc
    -- `let (target, s2) = IxonDeserialize::get_address(s);`
    obtain ⟨_, m_tgt, bs_tgt, c_tgt, ca3, d_tgt, mt_tgt, da3, rfl⟩ := da2.letValue_inv
    obtain ⟨_, _, _, cs_tgt, a_tgt, ev_tgt, rfl⟩ := d_tgt.call_inv
    rw [instanceName_plain_some] at ev_tgt
    obtain ⟨_, _, _, _, _, rfl, d_tg0, a_tg1, rfl⟩ := a_tgt.cons_inv
    obtain ⟨l_tg0, rfl, rfl⟩ := d_tg0.var_inv; simp at l_tg0; subst l_tg0
    obtain ⟨rfl, rfl, rfl⟩ := a_tg1.nil_inv
    obtain ⟨_, hv_tgt, -, ml_tgt⟩ := matchPattern_tuple_inv mt_tgt
    subst hv_tgt
    obtain ⟨x_target, _, _, _, rfl, mt_xt, ml_tgt1, rfl⟩ := matchListWith_cons_inv ml_tgt
    obtain rfl := matchPattern_bind_inv mt_xt
    obtain ⟨x_s4, _, _, _, rfl, mt_xs4, ml_tgt2, rfl⟩ := matchListWith_cons_inv ml_tgt1
    obtain rfl := matchPattern_bind_inv mt_xs4
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_tgt2
    -- `let (asm, rest) = get_opt_addr(s2);`
    obtain ⟨_, m_asm, bs_asm, c_asm, ca4, d_asm, mt_asm, da4, rfl⟩ := da3.letValue_inv
    obtain ⟨_, _, _, cs_asm, a_asm, ev_asm, rfl⟩ := d_asm.call_inv
    rw [instanceName_plain_some] at ev_asm
    obtain ⟨_, _, _, _, _, rfl, d_as0, a_as1, rfl⟩ := a_asm.cons_inv
    obtain ⟨l_as0, rfl, rfl⟩ := d_as0.var_inv; simp at l_as0; subst l_as0
    obtain ⟨rfl, rfl, rfl⟩ := a_as1.nil_inv
    obtain ⟨_, hv_asm, -, ml_asm⟩ := matchPattern_tuple_inv mt_asm
    subst hv_asm
    obtain ⟨x_asm, _, _, _, rfl, mt_xasm, ml_asm1, rfl⟩ := matchListWith_cons_inv ml_asm
    obtain rfl := matchPattern_bind_inv mt_xasm
    obtain ⟨x_rest, _, _, _, rfl, mt_xrest, ml_asm2, rfl⟩ := matchListWith_cons_inv ml_asm1
    obtain rfl := matchPattern_bind_inv mt_xrest
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_asm2
    -- `let Lists::Node::Nil = (*(rest));`
    obtain ⟨_, m_nil, bs_nil, c_nil, ca5, d_nil, mt_nil, da5, rfl⟩ := da4.letValue_inv
    obtain ⟨_, d_nil_v, _⟩ := d_nil.load_inv
    obtain ⟨_, rfl, rfl⟩ := d_nil_v.var_inv
    obtain ⟨_, _, -, ml_nil⟩ := matchPattern_construct_inv mt_nil
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_nil
    -- `assert_claimable(rc, target);`
    obtain ⟨v_ac, m_ac, bs_ac, c_ac, ca6, d_ac, mt_ac, da6, rfl⟩ := da5.letValue_inv
    obtain ⟨_, _, _, cs_ac, a_ac, ev_ac, rfl⟩ := d_ac.call_inv
    rw [instanceName_plain_some] at ev_ac
    obtain ⟨_, _, _, _, _, rfl, d_ac0, a_ac1, rfl⟩ := a_ac.cons_inv
    obtain ⟨l_ac0, rfl, rfl⟩ := d_ac0.var_inv; simp at l_ac0; subst l_ac0
    obtain ⟨_, _, _, _, _, rfl, d_ac1, a_ac2, rfl⟩ := a_ac1.cons_inv
    obtain ⟨l_ac1, rfl, rfl⟩ := d_ac1.var_inv; simp at l_ac1; subst l_ac1
    obtain ⟨rfl, rfl, rfl⟩ := a_ac2.nil_inv
    obtain rfl := matchPattern_wildcard_inv mt_ac
    -- `match asm { None => run_check_transitive(rc, target), Some(r) => ... };`
    obtain ⟨v_mw, m_mw, bs_mw, c_mw, ca7, d_mw, mt_mw, _, rfl⟩ := da6.letValue_inv
    obtain rfl := matchPattern_wildcard_inv mt_mw
    obtain ⟨_, _, bs_asm_m, body_asm_m, _, c_asm_body, d_asm_sc, sel_asm, d_asm_body, rfl⟩ :=
      d_mw.matchValue_inv
    obtain ⟨l_asm_sc, rfl, rfl⟩ := d_asm_sc.var_inv; simp at l_asm_sc; subst l_asm_sc
    -- Align `getPayload 4 valByte` with `get_claim_context`, `get_address`, `get_opt_addr`
    have ext_rc0 := ev_rc.heap_extends
    obtain ⟨ext_tgt, hlen_tgt, _, _, htup_tgt, haddr_tgt, hs_tgt⟩ :=
      Deserialize.getAddress_refines (Ingress.Stream.mono ext_rc0 hs_ctx) ev_tgt.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_tgt
    obtain ⟨rfl, rfl⟩ := htup_tgt
    rw [List.drop_drop] at hs_tgt
    have hget_tgt := getAddress_of_drop hlen_tgt
    obtain ⟨ext_asm, optAsm, kAsm, _, _, hget_asm, htup_asm, hopt_asm, _⟩ :=
      get_opt_addr_spec hs_tgt ev_asm
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_asm
    obtain ⟨rfl, rfl⟩ := htup_asm
    unfold Claim.getPayload at hok_payload
    have hv3_f : (4 == Claim.VARIANT_EVAL_CLAIM) = false := rfl
    have hv4_t : (4 == Claim.VARIANT_CHECK_CLAIM) = true := rfl
    simp only [hv3_f, hv4_t, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, pure,
      EStateM.pure, hget_ctx, hget_tgt, hget_asm] at hok_payload
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok_payload
    obtain ⟨hctx_ax, hasm_none, -⟩ := hscope
    dsimp only at hctx_ax
    subst hasm_none
    have hx_ax := hax_none hctx_ax
    rw [hx_ax] at ev_rc
    simp only [Claim.context?, Option.some.injEq] at hctx
    have hb_eq : ctx.binding = ctx₀.binding := by rw [← hctx]
    rw [← hb_eq] at haddr_bind
    rcases load_role_ctx_lim_spec (V := V)
        (extra := bytes :: tb :: IxVM.Consistency.committedFootprint)
        hadm (by simp) haddr_bind ev_rc with hcoll | ⟨_, hok_rc⟩
    · exact .inl (hashedCollision_mono
        (fun cl hcl => hsub_arm cl (by simp [instanceName_plain_some, hcl])) hcoll)
    obtain ⟨lim, hlim, hrc_rep⟩ := td_lim_of hok_rc
    dsimp only at hopt_asm
    subst hopt_asm
    rcases selectArm_cons_inv sel_asm with ⟨mt_none, rfl⟩ | ⟨nm_none, _⟩
    case inr =>
      have hne_none := matchPattern_construct_none (by trivial) nm_none
      rw [Obs.Names.n253830841395321305] at hne_none
      exact absurd rfl (hne_none [] rfl)
    obtain ⟨_, _, -, ml_none⟩ := matchPattern_construct_inv mt_none
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_none
    obtain ⟨_, _, _, cs_tr, a_tr, ev_tr, rfl⟩ := d_asm_body.call_inv
    rw [instanceName_plain_some] at ev_tr
    obtain ⟨_, _, _, _, _, rfl, d_tr0, a_tr1, rfl⟩ := a_tr.cons_inv
    obtain ⟨l_tr0, rfl, rfl⟩ := d_tr0.var_inv; simp at l_tr0; subst l_tr0
    obtain ⟨_, _, _, _, _, rfl, d_tr1, a_tr2, rfl⟩ := a_tr1.cons_inv
    obtain ⟨l_tr1, rfl, rfl⟩ := d_tr1.var_inv; simp at l_tr1; subst l_tr1
    obtain ⟨rfl, rfl, rfl⟩ := a_tr2.nil_inv
    obtain ⟨_, hseeds_eq⟩ := hseeds
    exact .inr ⟨lim, hlim, .inl ⟨_, _, _, _, x_rc, x_target, v_ac, v_mw, cs_ac, cs_tr,
      hseeds_eq, hrc_rep.mono (ext_tgt.trans ext_asm),
      ⟨_, Bytes.repAddressRef_heapMono₂ addrTy ext_asm haddr_tgt, rfl⟩,
      ev_ac, ev_tr,
      hsub_arm _ (by simp [instanceName_plain_some]),
      hsub_arm _ (by simp [instanceName_plain_some]),
      fun cl hcl => hsub_arm cl (by simp [instanceName_plain_some, hcl]),
      fun cl hcl => hsub_arm cl (by simp [instanceName_plain_some, hcl])⟩⟩
  · -- Variant 5 (`Claim.checkEnv`)
    rw [htv5] at pr_sz0 hok_payload hval_ok
    change projectValue (TagN.u64Value 5) 0 = .ok x_variant at pr_sz0
    simp only [TagN.u64Value, projectValue, List.getElem?_cons_zero, pure, Except.pure,
      Except.ok.injEq] at pr_sz0
    subst x_variant
    -- Select arm `5`: skip `3`, skip `4`, match `5`
    rcases selectArm_cons_inv sel_arm with ⟨mt3, _⟩ | ⟨_, sel_arm1⟩
    · obtain ⟨heq35, _⟩ := MatchesConst.some_inv (MatchesConst.literal 3) mt3
      simp at heq35
      exact absurd heq35 (by decide)
    rcases selectArm_cons_inv sel_arm1 with ⟨mt4, _⟩ | ⟨_, sel_arm2⟩
    · obtain ⟨heq45, _⟩ := MatchesConst.some_inv (MatchesConst.literal 4) mt4
      simp at heq45
      exact absurd heq45 (by decide)
    rcases selectArm_cons_inv sel_arm2 with ⟨mt5, rfl⟩ | ⟨nm5, _⟩
    case inr =>
      exact absurd rfl (MatchesConst.none_inv (MatchesConst.literal 5) nm5)
    obtain ⟨_, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 5) mt5
    -- `match UInt8::to_field(validator) { 10 => ..., 11 => ..., _ => ... }`
    obtain ⟨v_vsc, m_vsc, bs_varm, body_varm, c_vsc, c_varm, d_vsc, sel_varm, d_arm, rfl⟩ :=
      d_arm.matchValue_inv
    obtain ⟨_, _, _, cs_vsc, a_vsc, ev_vsc, rfl⟩ := d_vsc.call_inv
    rw [instanceName_plain_some] at ev_vsc
    obtain ⟨_, _, _, _, _, rfl, d_vsc0, a_vsc1, rfl⟩ := a_vsc.cons_inv
    obtain ⟨l_vsc0, rfl, rfl⟩ := d_vsc0.var_inv; simp at l_vsc0; subst l_vsc0
    obtain ⟨rfl, rfl, rfl⟩ := a_vsc1.nil_inv
    obtain ⟨rfl, rfl⟩ := Ingress.u8_toField ev_vsc
    have hsub_arm : ∀ cl ∈ c_varm, cl ∈ calls := fun cl hcl =>
      hsub_arm cl (by simp [hcl])
    rcases selectArm_cons_inv sel_varm with ⟨mt10, _⟩ | ⟨_, sel_varm1⟩
    · obtain ⟨heq10, _⟩ := MatchesConst.some_inv (MatchesConst.literal 10) mt10
      rcases hval_ok with rfl | rfl | rfl <;>
        exact absurd (Value.field.inj heq10) (by decide)
    rcases selectArm_cons_inv sel_varm1 with ⟨mt11, _⟩ | ⟨_, sel_varm2⟩
    · obtain ⟨heq11, _⟩ := MatchesConst.some_inv (MatchesConst.literal 11) mt11
      rcases hval_ok with rfl | rfl | rfl <;>
        exact absurd (Value.field.inj heq11) (by decide)
    rcases selectArm_cons_inv sel_varm2 with ⟨mt_w, rfl⟩ | ⟨nm_w, _⟩
    case inr => exact (matchPattern_wildcard_none nm_w).elim
    obtain rfl := matchPattern_wildcard_inv mt_w
    -- Arm 5 body:
    -- `let (binding, axioms, s) = get_claim_context(s);`
    obtain ⟨_, m_ctx, bs_ctx, c_ctx, ca1, d_ctx, mt_ctx, da1, rfl⟩ := d_arm.letValue_inv
    obtain ⟨_, _, _, cs_ctx, a_ctx, ev_ctx, rfl⟩ := d_ctx.call_inv
    rw [instanceName_plain_some] at ev_ctx
    obtain ⟨_, _, _, _, _, rfl, d_cx0, a_cx1, rfl⟩ := a_ctx.cons_inv
    obtain ⟨l_cx0, rfl, rfl⟩ := d_cx0.var_inv; simp at l_cx0; subst l_cx0
    obtain ⟨rfl, rfl, rfl⟩ := a_cx1.nil_inv
    obtain ⟨_, hv_ctx, -, ml_ctx⟩ := matchPattern_tuple_inv mt_ctx
    subst hv_ctx
    obtain ⟨x_binding, _, _, _, rfl, mt_xb, ml_ctx1, rfl⟩ := matchListWith_cons_inv ml_ctx
    obtain rfl := matchPattern_bind_inv mt_xb
    obtain ⟨x_axioms, _, _, _, rfl, mt_xax, ml_ctx2, rfl⟩ := matchListWith_cons_inv ml_ctx1
    obtain rfl := matchPattern_bind_inv mt_xax
    obtain ⟨x_s3, _, _, _, rfl, mt_xs3, ml_ctx3, rfl⟩ := matchListWith_cons_inv ml_ctx2
    obtain rfl := matchPattern_bind_inv mt_xs3
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_ctx3
    obtain ⟨ext_ctx, ctx₀, kCtx, _, _, _, hget_ctx, htup_ctx, haddr_bind, hax_none, hs_ctx⟩ :=
      get_claim_context_spec hs_val ev_ctx
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_ctx
    obtain ⟨rfl, rfl, rfl⟩ := htup_ctx
    -- `let rc = KernelRoles::load_role_ctx(binding, UInt8::to_field(validator), axioms);`
    obtain ⟨x_rc, m_rc, bs_rc, c_rc, ca2, d_rc, mt_rc, da2, rfl⟩ := da1.letValue_inv
    obtain ⟨_, _, _, cs_rc, a_rc, ev_rc, rfl⟩ := d_rc.call_inv
    rw [instanceName_plain_some] at ev_rc
    obtain ⟨_, _, _, _, _, rfl, d_rc0, a_rc1, rfl⟩ := a_rc.cons_inv
    obtain ⟨l_rc0, rfl, rfl⟩ := d_rc0.var_inv; simp at l_rc0; subst l_rc0
    obtain ⟨_, _, _, _, _, rfl, d_rc1, a_rc2, rfl⟩ := a_rc1.cons_inv
    obtain ⟨_, _, _, cs_rc_v, a_rc_v, ev_rc_v, rfl⟩ := d_rc1.call_inv
    rw [instanceName_plain_some] at ev_rc_v
    obtain ⟨_, _, _, _, _, rfl, d_rcv0, a_rcv1, rfl⟩ := a_rc_v.cons_inv
    obtain ⟨l_rcv0, rfl, rfl⟩ := d_rcv0.var_inv; simp at l_rcv0; subst l_rcv0
    obtain ⟨rfl, rfl, rfl⟩ := a_rcv1.nil_inv
    obtain ⟨rfl, rfl⟩ := Ingress.u8_toField ev_rc_v
    obtain ⟨_, _, _, _, _, rfl, d_rc2, a_rc3, rfl⟩ := a_rc2.cons_inv
    obtain ⟨l_rc2, rfl, rfl⟩ := d_rc2.var_inv; simp at l_rc2; subst l_rc2
    obtain ⟨rfl, rfl, rfl⟩ := a_rc3.nil_inv
    obtain rfl := matchPattern_bind_inv mt_rc
    -- `let (root, s2) = IxonDeserialize::get_address(s);`
    obtain ⟨_, m_rt, bs_rt, c_rt, ca3, d_rt, mt_rt, da3, rfl⟩ := da2.letValue_inv
    obtain ⟨_, _, _, cs_rt, a_rt, ev_rt, rfl⟩ := d_rt.call_inv
    rw [instanceName_plain_some] at ev_rt
    obtain ⟨_, _, _, _, _, rfl, d_rt0, a_rt1, rfl⟩ := a_rt.cons_inv
    obtain ⟨l_rt0, rfl, rfl⟩ := d_rt0.var_inv; simp at l_rt0; subst l_rt0
    obtain ⟨rfl, rfl, rfl⟩ := a_rt1.nil_inv
    obtain ⟨_, hv_rt, -, ml_rt⟩ := matchPattern_tuple_inv mt_rt
    subst hv_rt
    obtain ⟨x_root, _, _, _, rfl, mt_xrt, ml_rt1, rfl⟩ := matchListWith_cons_inv ml_rt
    obtain rfl := matchPattern_bind_inv mt_xrt
    obtain ⟨x_s4, _, _, _, rfl, mt_xs4, ml_rt2, rfl⟩ := matchListWith_cons_inv ml_rt1
    obtain rfl := matchPattern_bind_inv mt_xs4
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_rt2
    -- `let (asm, rest) = get_opt_addr(s2);`
    obtain ⟨_, m_asm, bs_asm, c_asm, ca4, d_asm, mt_asm, da4, rfl⟩ := da3.letValue_inv
    obtain ⟨_, _, _, cs_asm, a_asm, ev_asm, rfl⟩ := d_asm.call_inv
    rw [instanceName_plain_some] at ev_asm
    obtain ⟨_, _, _, _, _, rfl, d_as0, a_as1, rfl⟩ := a_asm.cons_inv
    obtain ⟨l_as0, rfl, rfl⟩ := d_as0.var_inv; simp at l_as0; subst l_as0
    obtain ⟨rfl, rfl, rfl⟩ := a_as1.nil_inv
    obtain ⟨_, hv_asm, -, ml_asm⟩ := matchPattern_tuple_inv mt_asm
    subst hv_asm
    obtain ⟨x_asm, _, _, _, rfl, mt_xasm, ml_asm1, rfl⟩ := matchListWith_cons_inv ml_asm
    obtain rfl := matchPattern_bind_inv mt_xasm
    obtain ⟨x_rest, _, _, _, rfl, mt_xrest, ml_asm2, rfl⟩ := matchListWith_cons_inv ml_asm1
    obtain rfl := matchPattern_bind_inv mt_xrest
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_asm2
    -- `let Lists::Node::Nil = (*(rest));`
    obtain ⟨_, m_nil, bs_nil, c_nil, ca5, d_nil, mt_nil, da5, rfl⟩ := da4.letValue_inv
    obtain ⟨_, d_nil_v, _⟩ := d_nil.load_inv
    obtain ⟨_, rfl, rfl⟩ := d_nil_v.var_inv
    obtain ⟨_, _, -, ml_nil⟩ := matchPattern_construct_inv mt_nil
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_nil
    -- `run_check_env(rc, root, asm);`
    obtain ⟨v_rce, m_rce, bs_rce, c_rce, ca6, d_rce, mt_rce, _, rfl⟩ := da5.letValue_inv
    obtain ⟨_, _, _, cs_rce, a_rce, ev_rce, rfl⟩ := d_rce.call_inv
    rw [instanceName_plain_some] at ev_rce
    obtain ⟨_, _, _, _, _, rfl, d_ce0, a_ce1, rfl⟩ := a_rce.cons_inv
    obtain ⟨l_ce0, rfl, rfl⟩ := d_ce0.var_inv; simp at l_ce0; subst l_ce0
    obtain ⟨_, _, _, _, _, rfl, d_ce1, a_ce2, rfl⟩ := a_ce1.cons_inv
    obtain ⟨l_ce1, rfl, rfl⟩ := d_ce1.var_inv; simp at l_ce1; subst l_ce1
    obtain ⟨_, _, _, _, _, rfl, d_ce2, a_ce3, rfl⟩ := a_ce2.cons_inv
    obtain ⟨l_ce2, rfl, rfl⟩ := d_ce2.var_inv; simp at l_ce2; subst l_ce2
    obtain ⟨rfl, rfl, rfl⟩ := a_ce3.nil_inv
    obtain rfl := matchPattern_wildcard_inv mt_rce
    -- Align `getPayload 5 valByte`
    have ext_rc0 := ev_rc.heap_extends
    obtain ⟨ext_rt, hlen_rt, _, _, htup_rt, haddr_rt, hs_rt⟩ :=
      Deserialize.getAddress_refines (Ingress.Stream.mono ext_rc0 hs_ctx) ev_rt.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_rt
    obtain ⟨rfl, rfl⟩ := htup_rt
    rw [List.drop_drop] at hs_rt
    have hget_rt := getAddress_of_drop hlen_rt
    obtain ⟨ext_asm, optAsm, kAsm, _, _, hget_asm, htup_asm, hopt_asm, _⟩ :=
      get_opt_addr_spec hs_rt ev_asm
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_asm
    obtain ⟨rfl, rfl⟩ := htup_asm
    unfold Claim.getPayload at hok_payload
    have hv3_f : (5 == Claim.VARIANT_EVAL_CLAIM) = false := rfl
    have hv4_f : (5 == Claim.VARIANT_CHECK_CLAIM) = false := rfl
    have hv5_t : (5 == Claim.VARIANT_CHECK_ENV_CLAIM) = true := rfl
    simp only [hv3_f, hv4_f, hv5_t, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, pure,
      EStateM.pure, hget_ctx, hget_rt, hget_asm] at hok_payload
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok_payload
    obtain ⟨hctx_ax, hasm_none, -⟩ := hscope
    dsimp only at hctx_ax
    subst hasm_none
    have hx_ax := hax_none hctx_ax
    rw [hx_ax] at ev_rc
    simp only [Claim.context?, Option.some.injEq] at hctx
    have hb_eq : ctx.binding = ctx₀.binding := by rw [← hctx]
    rw [← hb_eq] at haddr_bind
    rcases load_role_ctx_lim_spec (V := V)
        (extra := bytes :: tb :: IxVM.Consistency.committedFootprint)
        hadm (by simp) haddr_bind ev_rc with hcoll | ⟨_, hok_rc⟩
    · exact .inl (hashedCollision_mono
        (fun cl hcl => hsub_arm cl (by simp [instanceName_plain_some, hcl])) hcoll)
    obtain ⟨lim, hlim, hrc_rep⟩ := td_lim_of hok_rc
    dsimp only at hopt_asm
    subst hopt_asm
    obtain ⟨tTree, hv_trees, htree_root, hseeds_eq⟩ := hseeds
    have htTree_mem : tTree ∈ V.trees := by rw [hv_trees]; simp
    have hroot_addr : BaseSeams.addr _ x_root (treeRoot tTree) :=
      ⟨_, Bytes.repAddressRef_heapMono₂ addrTy ext_asm haddr_rt, htree_root.symm⟩
    rcases td_run_check_env_none_lim_spec (V := V)
        (extra := bytes :: tb :: IxVM.Consistency.committedFootprint)
        htTree_mem (hrc_rep.mono (ext_rt.trans ext_asm)) hroot_addr ev_rce with
      hcoll | ⟨as, m₁, x_leaves, cs₁, hne_leaves, hmap_as, hrc_m1, hl_leaves, ev_wlo, hcl_wlo, hsub1⟩
    · exact .inl (hashedCollision_mono
        (fun cl hcl => hsub_arm cl (by simp [instanceName_plain_some, hcl])) hcoll)
    · rw [← hseeds_eq] at hne_leaves hmap_as
      exact .inr ⟨lim, hlim, .inr ⟨as, m₁, m_rce, x_rc, x_leaves, v_rce, cs₁,
        hne_leaves, hmap_as, hrc_m1, hl_leaves, ev_wlo,
        hsub_arm _ (by simp [instanceName_plain_some, hcl_wlo]),
        fun cl hcl => hsub_arm cl (by simp [instanceName_plain_some, hsub1 cl hcl])⟩⟩

end IxVM.Refinement.Claim
