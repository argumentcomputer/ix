import IxCC.CompileClaim
import IxCC.Compiler.Proof
import IxCC.Recheck.Proof.Soundness
import IxCC.Recheck.Rc.Proof.ObjectSound
import IxCC.Recheck.Proof.RootShape

/-! # `CompileClaim.Proof`: Wire Roundtrip & End-to-End Soundness Theorems

Proves canonical wire serialization roundtrip (`ofPayloadBytes_toPayloadBytes`,
`ofClaimBytes_toClaimBytes`) and end-to-end verification soundness across all
three policies (`.immortal`, `.zeroRc`, `.plainRc`):

- `verifyProgram_immortal_sound`, `verifyProgram_zeroRc_sound`, `verifyProgram_plainRc_sound`
- `verifyBytes_immortal_sound`, `verifyBytes_zeroRc_sound`, `verifyBytes_plainRc_sound`

## Scope and Trust Boundary Notes

1. **Ingress & Kernel Typechecking**:
   - `verifyBytes` defaults to `typecheck := true`, and `verifyBytes_*_sound`
     explicitly exposes `Recheck.ingress envBytes equations (selectTargetRoots cfg equations c.target) typecheck = .ok inp`,
     `Ixon.V3.decodeAnonymousEnv envBytes = .ok inp.env`,
     `typecheck = true → Ixon.V3.Tc.checkEnv inp.env = .ok ()`, and
     `Src.Resource.validate inp.program = .ok ()`.

2. **Front-End Recheck Step**:
   - Every soundness theorem exposes `Recheck.front cfg P cert = .ok (a.src, a.checked)`
     (or `Recheck.front cfg P cert.base = .ok (a.front.src, a.front.checked)` under
     `.plainRc`). `Recheck.front` runs `Src.Table.ofCert`, then
     `Src.Recheck.annotation`, which installs the annotation and runs
     `Relevance.check`, then `Relevance.checkCanonical` (on every program, whatever
     its pinned identities), then `Lazify.run`.
   - Note (stage S): `CheckedProgram` evaluates `a.src` after table installation,
     relevance annotation recheck, and `Lazify` under `SrcEval` (`Lam.Erase.Proof`).
     These theorems state that `front` ran, not what it preserves. The byte-level
     `verifyBytes_*_sound` also state how `a.src` was built from `inp.program`
     (`Table.ofCert`, the annotation equal to `Relevance.annotate`'s output,
     `install`, `check`, `WellAnnotated`, `Lazify.run`, which changes only
     application modes: `Lazify.run_modeEq`). None of these relates `a.src` to
     `inp.program` semantically (open item S6 in `IxCC/docs/certification-design.md`), and nothing
     relates either to the kernel's meaning of `c.target` (open item S8 in
     `IxCC/docs/certification-design.md`). The value clause is relative to SrcEval on `a.src` and
     disjoined with `a.front.GoesWrong`, which no theorem bounds.

3. **Observable Roots & `Nat`-Parameter ABI**:
   - `verifyProgram` rejects roots with `root.ty = none`, a declaration whose
     Π-telescope length is not `root.params` or whose parameters are not `Nat`
     (`rootParamsAllNat`), and, on the immortal/`.zeroRc` paths, return types
     other than `Nat` or an enumeration of field-less constructors
     (`isImmortalViewType`). These checks make the value clause observe the
     root's result (a root without a readback type observes nothing).
   - On the immortal and `.zeroRc` paths the view reads back every result of
     the shape the root's declared type describes (`Recheck.ResultShape`: a
     `Nat`, a pinned `Bool` constructor, or a constructor of the result
     enumeration), so the view-rejection case of `Front.GoesWrong` happens at
     the claim's root only for a result off that shape, or, on the pinned-`Bool`
     route, when a pinned `Bool` constructor has no row in the constructor table
     (`verifyProgram_immortal_rootShape` and its `.zeroRc` and `verifyBytes`
     forms). This does not bound `Front.GoesWrong`: nothing proves that SrcEval
     on `a.src` returns a result of that shape, or does not get stuck. -/

set_option autoImplicit false

namespace IxCC.CompileClaim

open IxCC.Sem (Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)

theorem checkWellFormed_iff (c : CompileClaim) :
    c.checkWellFormed = true ↔ c.WellFormed := by
  simp [checkWellFormed, WellFormed]

/-! ### The `N0` code of `abiArity` -/

theorem leBytes_length (x w : Nat) : (leBytes x w).length = w := by
  induction w generalizing x with
  | zero => rfl
  | succ w ih => simp [leBytes, ih]

theorem leValue_leBytes {x w : Nat} (h : x < 256 ^ w) : leValue (leBytes x w) = x := by
  induction w generalizing x with
  | zero => simp [leBytes, leValue]; omega
  | succ w ih =>
    have hdiv : x / 256 < 256 ^ w := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [Nat.pow_succ] using h
    simp only [leBytes, leValue, ih hdiv, UInt8.toNat_ofNat']
    omega

/-- Below `2 ^ 64`, the header of `n0Bytes v` announces its payload width and the
header and payload denote `v`. -/
theorem n0_spec {v : Nat} (hv : v < 2 ^ 64) :
    n0Width (n0Header v) = some (n0Payload v).length ∧
      n0Value (n0Header v) (n0Payload v) = v := by
  by_cases h1 : v < 128
  · have hh : (n0Header v).toNat = v := by
      simp only [n0Header, h1, ite_true, UInt8.toNat_ofNat']
      omega
    simp [n0Width, n0Value, n0Payload, hh, h1]
  by_cases h2 : v < 16512
  · have hh : (n0Header v).toNat = 128 + (v - 128) / 256 := by
      simp only [n0Header, h1, h2, ite_true, ite_false, UInt8.toNat_ofNat']
      omega
    have hp : n0Payload v = leBytes ((v - 128) % 256) 1 := by simp [n0Payload, h1, h2]
    have hlv : leValue (leBytes ((v - 128) % 256) 1) = (v - 128) % 256 :=
      leValue_leBytes (by omega)
    refine ⟨?_, ?_⟩
    · simp only [n0Width, hh, hp, leBytes_length]
      split <;> first | omega | (split <;> first | rfl | omega)
    · simp only [n0Value, hh, hp, hlv]
      split
      · omega
      · split
        · omega
        · omega
  by_cases h3 : v < 82048
  · have hh : n0Header v = 0xC0 := by simp [n0Header, h1, h2, h3]
    have hp : n0Payload v = leBytes (v - 16512) 2 := by simp [n0Payload, h1, h2, h3]
    have hlv := leValue_leBytes (x := v - 16512) (w := 2) (by omega)
    refine ⟨?_, ?_⟩
    · simp [n0Width, hh, hp, leBytes_length]
    · simp [n0Value, hh, hp, hlv]; omega
  by_cases h4 : v < 16859264
  · have hh : n0Header v = 0xC1 := by simp [n0Header, h1, h2, h3, h4]
    have hp : n0Payload v = leBytes (v - 82048) 3 := by simp [n0Payload, h1, h2, h3, h4]
    have hlv := leValue_leBytes (x := v - 82048) (w := 3) (by omega)
    refine ⟨?_, ?_⟩
    · simp [n0Width, hh, hp, leBytes_length]
    · simp [n0Value, hh, hp, hlv]; omega
  by_cases h5 : v < 4311826560
  · have hh : n0Header v = 0xC2 := by simp [n0Header, h1, h2, h3, h4, h5]
    have hp : n0Payload v = leBytes (v - 16859264) 4 := by simp [n0Payload, h1, h2, h3, h4, h5]
    have hlv := leValue_leBytes (x := v - 16859264) (w := 4) (by omega)
    refine ⟨?_, ?_⟩
    · simp [n0Width, hh, hp, leBytes_length]
    · simp [n0Value, hh, hp, hlv]; omega
  · have hh : n0Header v = 0xC3 := by simp [n0Header, h1, h2, h3, h4, h5]
    have hp : n0Payload v = leBytes (v - 4311826560) 8 := by simp [n0Payload, h1, h2, h3, h4, h5]
    have hlv := leValue_leBytes (x := v - 4311826560) (w := 8) (by omega)
    refine ⟨?_, ?_⟩
    · simp [n0Width, hh, hp, leBytes_length]
    · simp [n0Value, hh, hp, hlv]; omega

theorem getN0_eq : getN0 = (Ixon.getU8 >>= fun header =>
    match n0Width header with
    | some width => Ixon.getBytes width >>= n0Finish header
    | none => throw "CompileClaim: invalid abiArity code") := by
  rfl

/-- `getN0` reads `n0Bytes v` back as `v` for every `v < 2 ^ 64`. -/
theorem getN0_encoded_spec {v : Nat} (hv : v < 2 ^ 64) :
    Ixon.GetSpec getN0 (n0Bytes v) v := by
  obtain ⟨hw, hval⟩ := n0_spec hv
  let payload : ByteArray := ⟨(n0Payload v).toArray⟩
  have hsize : payload.size = (n0Payload v).length := by simp [payload, ByteArray.size]
  have hlist : payload.data.toList = n0Payload v := by simp [payload]
  have hcheck : v < 2 ^ 64 ∧ n0Bytes v = Ixon.u8Bytes (n0Header v) ++ payload := ⟨hv, rfl⟩
  have hb : n0Bytes v = Ixon.u8Bytes (n0Header v) ++ (payload ++ ByteArray.empty) := by
    simp [n0Bytes, payload]
  have hfinish : n0Finish (n0Header v) payload = pure v := by
    simp only [n0Finish, hlist, hval]
    exact ite_eq_left hcheck
  rw [hb, getN0_eq]
  refine Ixon.GetSpec.bind (Ixon.getU8_spec (n0Header v)) ?_
  simp only [hw]
  rw [← hsize]
  refine Ixon.GetSpec.bind (Ixon.getBytes_spec payload) ?_
  rw [hfinish]
  exact Ixon.GetSpec.pure v

/-- Every successful `getN0` read returns a value below `2 ^ 64` and consumed
exactly its `N0` code: the reader is canonical. -/
theorem getN0_sound (pre rest : ByteArray) {value : Nat} {st' : Ixon.GetState}
    (h : getN0.run ⟨pre ++ rest, pre.size⟩ = .ok (value, st')) :
    value < 2 ^ 64 ∧ ∃ suffix,
      rest = n0Bytes value ++ suffix ∧
      st' = ⟨pre ++ rest, pre.size + (n0Bytes value).size⟩ := by
  rw [getN0_eq] at h
  simp only [StateT.run_bind] at h
  cases hh : Ixon.getU8.run ⟨pre ++ rest, pre.size⟩ with
  | error e => rw [hh] at h; contradiction
  | ok r =>
    rcases r with ⟨header, mid⟩
    rw [hh] at h
    simp only [bind, Except.bind] at h
    obtain ⟨afterHead, hrest, hmid⟩ := Ixon.getU8_canonical pre rest hh
    let headPre := pre ++ Ixon.u8Bytes header
    have hmid' : mid = ⟨headPre ++ afterHead, headPre.size⟩ := by
      rw [hmid]
      simp [headPre, hrest, ByteArray.append_assoc]
    rw [hmid'] at h
    cases hw : n0Width header with
    | none =>
      simp only [hw] at h
      change (Except.error _) = Except.ok (value, st') at h
      contradiction
    | some width =>
      simp only [hw] at h
      change ((Ixon.getBytes width >>= n0Finish header).run
        ⟨headPre ++ afterHead, headPre.size⟩) = .ok (value, st') at h
      simp only [StateT.run_bind] at h
      cases hp : (Ixon.getBytes width).run ⟨headPre ++ afterHead, headPre.size⟩ with
      | error e => rw [hp] at h; contradiction
      | ok r2 =>
        rcases r2 with ⟨payload, after⟩
        rw [hp] at h
        simp only [bind, Except.bind] at h
        obtain ⟨suffix, hafter, hst⟩ := Ixon.getBytes_canonical width headPre afterHead hp
        change (n0Finish header payload).run after = .ok (value, st') at h
        unfold n0Finish at h
        split at h
        · rename_i hcond
          obtain ⟨hlt, hbytes⟩ := hcond
          change Except.ok (n0Value header payload.data.toList, after) = Except.ok (value, st') at h
          cases h
          refine ⟨hlt, suffix, ?_, ?_⟩
          · rw [hrest, hafter, hbytes]
            simp [ByteArray.append_assoc]
          · rw [hst, hbytes]
            simp [headPre, hrest, ByteArray.size_append, ByteArray.append_assoc, Nat.add_assoc]
        · change (Except.error _) = Except.ok (value, st') at h
          contradiction

theorem getN0_canonical : Ixon.GetCanonical getN0 n0Bytes :=
  fun pre rest _ _ h => (getN0_sound pre rest h).2

/-- `getPayloadM` consumes `c.toPayloadBytes` and returns `c` for any well-formed `CompileClaim`. -/
theorem getPayloadM_spec {c : CompileClaim} (hwf : c.WellFormed) :
    Ixon.GetSpec getPayloadM c.toPayloadBytes c := by
  have henv : Ixon.GetSpec (Ixon.Serialize.get : Ixon.GetM Ixon.Address) c.env.hash c.env :=
    Ixon.Address.get_spec c.env
  have htarget : Ixon.GetSpec (Ixon.Serialize.get : Ixon.GetM Ixon.Address) c.target.hash c.target :=
    Ixon.Address.get_spec c.target
  have hpol : Ixon.GetSpec Ixon.getU8 (Ixon.u8Bytes c.policy.toUInt8) c.policy.toUInt8 :=
    Ixon.getU8_spec c.policy.toUInt8
  have harity : Ixon.GetSpec getN0 (n0Bytes c.abiArity) c.abiArity :=
    getN0_encoded_spec hwf
  have helf : Ixon.GetSpec (Ixon.Serialize.get : Ixon.GetM Ixon.Address) c.elfHash.hash c.elfHash :=
    Ixon.Address.get_spec c.elfHash
  have hstep4 : Ixon.GetSpec (do
      let elfHash ← (Ixon.Serialize.get : Ixon.GetM Ixon.Address)
      pure ({
        env := c.env
        target := c.target
        policy := c.policy
        abiArity := c.abiArity
        elfHash
      } : CompileClaim)) c.elfHash.hash c := by
    have hpure : Ixon.GetSpec (pure ({
      env := c.env
      target := c.target
      policy := c.policy
      abiArity := c.abiArity
      elfHash := c.elfHash
    } : CompileClaim)) ByteArray.empty ({
      env := c.env
      target := c.target
      policy := c.policy
      abiArity := c.abiArity
      elfHash := c.elfHash
    } : CompileClaim) := Ixon.GetSpec.pure _
    have h := Ixon.GetSpec.bind (next := fun elfHash => pure ({
      env := c.env
      target := c.target
      policy := c.policy
      abiArity := c.abiArity
      elfHash
    } : CompileClaim)) helf hpure
    rcases c with ⟨env, target, pol, arity, elfHash⟩
    simpa [ByteArray.append_empty] using h
  unfold getPayloadM toPayloadBytes
  simp only [ByteArray.append_assoc]
  refine Ixon.GetSpec.bind henv ?_
  refine Ixon.GetSpec.bind htarget ?_
  refine Ixon.GetSpec.bind hpol ?_
  rw [CompilePolicy.ofUInt8?_toUInt8]
  dsimp only
  refine Ixon.GetSpec.bind harity ?_
  exact hstep4

/-- `getClaimM` consumes `c.toClaimBytes` and returns `c` for any well-formed `CompileClaim`. -/
theorem getClaimM_spec {c : CompileClaim} (hwf : c.WellFormed) :
    Ixon.GetSpec getClaimM c.toClaimBytes c := by
  have hhdr : Ixon.GetSpec (Ixon.getBytes 4) validatorHeader validatorHeader := by
    have hsize : validatorHeader.size = 4 := rfl
    simpa [hsize] using Ixon.getBytes_spec validatorHeader
  let next (hdr : ByteArray) : Ixon.GetM CompileClaim := do
    if hdr != validatorHeader then
      throw "CompileClaim: invalid validator header"
    getPayloadM
  have hnext : Ixon.GetSpec (next validatorHeader) c.toPayloadBytes c := by
    have hfalse : (validatorHeader != validatorHeader) = false := by decide
    simpa [next, hfalse] using getPayloadM_spec hwf
  simpa [getClaimM, next, toClaimBytes] using Ixon.GetSpec.bind (next := next) hhdr hnext

/-- Canonical payload serialization roundtrip. -/
theorem ofPayloadBytes_toPayloadBytes {c : CompileClaim} (hwf : c.WellFormed) :
    ofPayloadBytes c.toPayloadBytes = some c := by
  unfold ofPayloadBytes
  rw [Ixon.runGet_eq_ok_of_spec (getPayloadM_spec hwf)]
  rfl

/-- Canonical full wire-envelope serialization roundtrip. -/
theorem ofClaimBytes_toClaimBytes {c : CompileClaim} (hwf : c.WellFormed) :
    ofClaimBytes c.toClaimBytes = some c := by
  unfold ofClaimBytes
  rw [Ixon.runGet_eq_ok_of_spec (getClaimM_spec hwf)]
  rfl

/-- Canonical address reader inversion: every accepted 32-byte address slice equals `a.hash`. -/
theorem address_get_canonical :
    Ixon.GetCanonical (Ixon.Serialize.get : Ixon.GetM Ixon.Address) (fun a => a.hash) := by
  intro pre rest a st' h
  change (do
    let bytes ← Ixon.getBytes 32
    match Ixon.Address.ofBytes? bytes with
    | some a => return a
    | none => throw "internal: getBytes returned a non-32-byte address").run
      ⟨pre ++ rest, pre.size⟩ = .ok (a, st') at h
  simp only [StateT.run_bind] at h
  cases hb : (Ixon.getBytes 32).run ⟨pre ++ rest, pre.size⟩ with
  | error err => rw [hb] at h; contradiction
  | ok res =>
    rcases res with ⟨bytes, mid⟩
    rw [hb] at h
    simp only [bind, Except.bind] at h
    obtain ⟨suffix, hrest, hmid⟩ := Ixon.getBytes_canonical 32 pre rest hb
    cases haddr : Ixon.Address.ofBytes? bytes with
    | none => rw [haddr] at h; contradiction
    | some a' =>
      rw [haddr] at h
      cases h
      unfold Ixon.Address.ofBytes? at haddr
      split at haddr <;> cases haddr
      exact ⟨suffix, hrest, hmid⟩

theorem CompilePolicy.toUInt8_ofUInt8? {b : UInt8} {p : CompilePolicy}
    (h : CompilePolicy.ofUInt8? b = some p) : p.toUInt8 = b := by
  unfold CompilePolicy.ofUInt8? at h
  split at h <;> cases h <;> rfl

/-- Converse payload reader specification: every successful `getPayloadM` parse
yields a well-formed `CompileClaim` and consumes its exact `toPayloadBytes` prefix. -/
theorem getPayloadM_canonical (pre rest : ByteArray) {c : CompileClaim} {st' : Ixon.GetState}
    (h : getPayloadM.run ⟨pre ++ rest, pre.size⟩ = .ok (c, st')) :
    c.WellFormed ∧
      ∃ suffix,
        rest = c.toPayloadBytes ++ suffix ∧
        st' = ⟨pre ++ rest, pre.size + c.toPayloadBytes.size⟩ := by
  unfold getPayloadM at h
  simp only [StateT.run_bind] at h
  cases henv : (Ixon.Serialize.get : Ixon.GetM Ixon.Address).run ⟨pre ++ rest, pre.size⟩ with
  | error e => rw [henv] at h; contradiction
  | ok r1 =>
    rcases r1 with ⟨env, st1⟩
    rw [henv] at h
    simp only [bind, Except.bind] at h
    obtain ⟨rest1, hrest1, hst1⟩ := address_get_canonical pre rest henv
    let pre1 := pre ++ env.hash
    have hst1' : st1 = ⟨pre1 ++ rest1, pre1.size⟩ := by
      rw [hst1]; simp [pre1, hrest1, ByteArray.append_assoc]
    rw [hst1'] at h
    cases htarget : (Ixon.Serialize.get : Ixon.GetM Ixon.Address).run ⟨pre1 ++ rest1, pre1.size⟩ with
    | error e => rw [htarget] at h; contradiction
    | ok r2 =>
      rcases r2 with ⟨target, st2⟩
      rw [htarget] at h
      dsimp only at h
      obtain ⟨rest2, hrest2, hst2⟩ := address_get_canonical pre1 rest1 htarget
      let pre2 := pre1 ++ target.hash
      have hst2' : st2 = ⟨pre2 ++ rest2, pre2.size⟩ := by
        rw [hst2]; simp [pre2, hrest2, ByteArray.append_assoc]
      rw [hst2'] at h
      cases hpol : Ixon.getU8.run ⟨pre2 ++ rest2, pre2.size⟩ with
      | error e => rw [hpol] at h; contradiction
      | ok r3 =>
        rcases r3 with ⟨polByte, st3⟩
        rw [hpol] at h
        dsimp only at h
        obtain ⟨rest3, hrest3, hst3⟩ := Ixon.getU8_canonical pre2 rest2 hpol
        cases hpolOpt : CompilePolicy.ofUInt8? polByte with
        | none =>
          rw [hpolOpt] at h
          change Except.error _ = Except.ok (c, st') at h
          contradiction
        | some policy =>
          rw [hpolOpt] at h
          change (do
            let abiArity ← getN0
            let elfHash ← (Ixon.Serialize.get : Ixon.GetM Ixon.Address)
            pure ({ env, target, policy, abiArity, elfHash } : CompileClaim)).run st3 =
              .ok (c, st') at h
          simp only [StateT.run_bind] at h
          have hpolEq : policy.toUInt8 = polByte := CompilePolicy.toUInt8_ofUInt8? hpolOpt
          let pre3 := pre2 ++ Ixon.u8Bytes polByte
          have hst3' : st3 = ⟨pre3 ++ rest3, pre3.size⟩ := by
            rw [hst3]; simp [pre3, hrest3, ByteArray.append_assoc]
          rw [hst3'] at h
          cases harity : getN0.run ⟨pre3 ++ rest3, pre3.size⟩ with
          | error e => rw [harity] at h; contradiction
          | ok r4 =>
            rcases r4 with ⟨abiArity, st4⟩
            rw [harity] at h
            simp only [bind, Except.bind] at h
            obtain ⟨harityLt, rest4, hrest4, hst4⟩ := getN0_sound pre3 rest3 harity
            let pre4 := pre3 ++ n0Bytes abiArity
            have hst4' : st4 = ⟨pre4 ++ rest4, pre4.size⟩ := by
              rw [hst4]; simp [pre4, hrest4, ByteArray.append_assoc]
            rw [hst4'] at h
            cases helf : (Ixon.Serialize.get : Ixon.GetM Ixon.Address).run ⟨pre4 ++ rest4, pre4.size⟩ with
            | error e => rw [helf] at h; contradiction
            | ok r5 =>
              rcases r5 with ⟨elfHash, st5⟩
              rw [helf] at h
              change Except.ok ({ env, target, policy, abiArity, elfHash }, st5) =
                Except.ok (c, st') at h
              cases h
              obtain ⟨suffix, hrest5, hst5⟩ := address_get_canonical pre4 rest4 helf
              have hwf : ({ env, target, policy, abiArity, elfHash } : CompileClaim).WellFormed :=
                harityLt
              refine ⟨hwf, suffix, ?_, ?_⟩
              · rw [hrest1, hrest2, hrest3, hrest4, hrest5]
                simp [toPayloadBytes, hpolEq, ByteArray.append_assoc]
              · rw [hst5]
                simp [pre4, pre3, pre2, pre1, hrest1, hrest2, hrest3, hrest4, hrest5,
                  toPayloadBytes, hpolEq, ByteArray.append_assoc, Nat.add_assoc]

private theorem byteArray_eq_empty_of_size_zero {bs : ByteArray} (h : bs.size = 0) :
    bs = ByteArray.empty := by
  rcases bs with ⟨data⟩
  have hdata : data = #[] := Array.eq_empty_of_size_eq_zero h
  subst hdata
  rfl

private theorem runGet_toOption_some {α : Type} {m : Ixon.GetM α} {bs : ByteArray} {a : α}
    (h : (Ixon.runGet m bs).toOption = some a) :
    ∃ st, m.run ⟨bs, 0⟩ = .ok (a, st) ∧ st.idx = st.bytes.size := by
  unfold Ixon.runGet at h
  cases hrun : m.run ⟨bs, 0⟩ with
  | error e => rw [hrun] at h; cases h
  | ok res =>
    rcases res with ⟨a', st⟩
    rw [hrun] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i htrail
      cases h
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at htrail
      exact ⟨st, rfl, htrail⟩

/-- Decoding payload bytes recovers a well-formed `CompileClaim` whose canonical
encoding equals `bs`. -/
theorem toPayloadBytes_ofPayloadBytes (bs : ByteArray) (c : CompileClaim)
    (h : ofPayloadBytes bs = some c) :
    c.toPayloadBytes = bs ∧ c.WellFormed := by
  obtain ⟨st, hrun, htrail⟩ := runGet_toOption_some h
  have hrun' : getPayloadM.run ⟨ByteArray.empty ++ bs, ByteArray.empty.size⟩ = .ok (c, st) := by
    simpa [ByteArray.empty_append, ByteArray.size_empty] using hrun
  obtain ⟨hwf, suffix, hbs, hst⟩ := getPayloadM_canonical ByteArray.empty bs hrun'
  simp only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at hst
  subst hst
  have hsufSize : suffix.size = 0 := by
    have := congrArg ByteArray.size hbs
    simp only [ByteArray.size_append] at this htrail
    omega
  have hsufEmpty : suffix = ByteArray.empty := byteArray_eq_empty_of_size_zero hsufSize
  subst hsufEmpty
  rw [ByteArray.append_empty] at hbs
  exact ⟨hbs.symm, hwf⟩

/-- Decoding full wire-envelope claim bytes recovers a well-formed `CompileClaim`
whose canonical wire encoding equals `bs`. -/
theorem toClaimBytes_ofClaimBytes (bs : ByteArray) (c : CompileClaim)
    (h : ofClaimBytes bs = some c) :
    c.toClaimBytes = bs ∧ c.WellFormed := by
  obtain ⟨st2, hrun, htrail⟩ := runGet_toOption_some h
  unfold getClaimM at hrun
  simp only [StateT.run_bind] at hrun
  have hinit : (⟨bs, 0⟩ : Ixon.GetState) = ⟨ByteArray.empty ++ bs, ByteArray.empty.size⟩ := by
    simp [ByteArray.empty_append, ByteArray.size_empty]
  rw [hinit] at hrun
  cases hhdr : (Ixon.getBytes 4).run ⟨ByteArray.empty ++ bs, ByteArray.empty.size⟩ with
  | error e => rw [hhdr] at hrun; cases hrun
  | ok r1 =>
    rcases r1 with ⟨hdr, st1⟩
    rw [hhdr] at hrun
    simp only [bind, Except.bind] at hrun
    obtain ⟨rest1, hbs, hst1⟩ := Ixon.getBytes_canonical 4 ByteArray.empty bs hhdr
    split at hrun
    · cases hrun
    · rename_i hhdrEq
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hhdrEq
      subst hhdrEq
      have hst1' : st1 = ⟨validatorHeader ++ rest1, validatorHeader.size⟩ := by
        rw [hst1]; simp [hbs, ByteArray.empty_append]
      rw [hst1'] at hrun
      obtain ⟨hwf, suffix, hrest1, hst2⟩ := getPayloadM_canonical validatorHeader rest1 hrun
      subst hst2
      have hsufSize : suffix.size = 0 := by
        have := congrArg ByteArray.size hrest1
        simp only [ByteArray.size_append] at this htrail
        omega
      have hsufEmpty : suffix = ByteArray.empty := byteArray_eq_empty_of_size_zero hsufSize
      subst hsufEmpty
      rw [ByteArray.append_empty] at hrest1
      rw [hrest1] at hbs
      exact ⟨hbs.symm, hwf⟩

/-- Soundness of `CompileClaim.verifyProgram` under `.immortal` policy, backed by
`Recheck.sound`, `Recheck.object_refines`, `Recheck.run_front`, and `checkImmortalRoot`.
It holds for every `P`; that the check runs within an 8 MiB stack assumes
`P` came from ingress (`Recheck.run`'s precondition). -/
theorem verifyProgram_immortal_sound {cfg : Recheck.Config} {P : Src.Program}
    {c : CompileClaim} {certText : String}
    (hpol : c.policy = .immortal)
    (hver : verifyProgram cfg P c certText = true) :
    ∃ (cert : Recheck.Cert) (a : Recheck.Artifact) (rootId : Src.CId) (root : Recheck.Root)
      (sig : Rt.Sig) (ty : Rt.FoTy),
      c.WellFormed ∧
      P.roots.head? = some (c.target, rootId) ∧
      Recheck.Cert.ofText certText = .ok cert ∧
      Recheck.run cfg P cert = .ok a ∧
      Recheck.front cfg P cert = .ok (a.src, a.checked) ∧
      a.roots.head? = some root ∧
      rootParamsAllNat a.src root = true ∧
      root.ty = some (sig, ty) ∧
      isImmortalViewType sig ty = true ∧
      root.params = c.abiArity ∧
      Ixon.Address.blake3Pure a.object = c.elfHash ∧
      ∀ (D : X86.Driver), D.Ok a.backend.encoded.text.size →
        Sem.Refines a.front.source (a.linked D) ∧
        ∀ (i : Nat × List Nat),
          (∀ k w, Lang.run (a.linked D) i k = .ok w →
            (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
              a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrong i) ∧
          (¬ a.front.GoesWrong i → ∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) ∧
          ((∀ k, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k = .timeout) →
            (∀ k, Lang.run (a.linked D) i k = .timeout) ∨
              ∃ k failure, Lang.run (a.linked D) i k = .resource failure) := by
  unfold verifyProgram at hver
  rw [Bool.and_eq_true] at hver
  rcases hver with ⟨hwf_b, hver⟩
  have hwf := (checkWellFormed_iff c).mp hwf_b
  cases hhead : P.roots.head? with
  | none => simp [hhead] at hver
  | some pair =>
    obtain ⟨rootAddr, rootId⟩ := pair
    simp only [hhead, hpol] at hver
    split at hver
    · next htarget =>
      have htargetEq : rootAddr = c.target := eq_of_beq htarget
      subst htargetEq
      cases hcert : Recheck.Cert.ofText certText with
      | error e => simp [hcert] at hver
      | ok cert =>
        simp only [hcert] at hver
        cases hrun : Recheck.run cfg P cert with
        | error e => simp [hrun] at hver
        | ok a =>
          simp only [hrun] at hver
          cases hahead : a.roots.head? with
          | none => simp [hahead] at hver
          | some root =>
            simp only [hahead, Bool.and_eq_true, beq_iff_eq] at hver
            rcases hver with ⟨⟨hrootOk, hparams⟩, hhash⟩
            unfold checkImmortalRoot at hrootOk
            rw [Bool.and_eq_true] at hrootOk
            rcases hrootOk with ⟨hnatParams, htyOk⟩
            cases hty : root.ty with
            | none => simp [hty] at htyOk
            | some st =>
              rcases st with ⟨sig, ty⟩
              simp only [hty] at htyOk
              refine ⟨cert, a, rootId, root, sig, ty, hwf, rfl, rfl, hrun,
                Recheck.run_front hrun, hahead, hnatParams, hty, htyOk, hparams, hhash, ?_⟩
              intro D hD
              exact ⟨Recheck.object_refines hrun D hD, fun i => Recheck.sound hrun D hD i⟩
    · cases hver

/-- Soundness of `CompileClaim.verifyProgram` under `.zeroRc` policy, backed by
`Recheck.recheckWithContracts_sound`, `Recheck.run_front`, and `checkImmortalRoot`.
It holds for every `P`; that the check runs within an 8 MiB stack assumes
`P` came from ingress (`Recheck.run`'s precondition). -/
theorem verifyProgram_zeroRc_sound {cfg : Recheck.Config} {P : Src.Program}
    {c : CompileClaim} {certText : String}
    (hpol : c.policy = .zeroRc)
    (hver : verifyProgram cfg P c certText = true) :
    ∃ (cert : Recheck.Cert) (a : Recheck.Artifact) (rootId : Src.CId) (root : Recheck.Root)
      (sig : Rt.Sig) (ty : Rt.FoTy),
      c.WellFormed ∧
      P.roots.head? = some (c.target, rootId) ∧
      Recheck.Cert.ofText certText = .ok cert ∧
      Recheck.runWithContracts cfg P cert = .ok a ∧
      Recheck.run cfg P cert = .ok a ∧
      Recheck.front cfg P cert = .ok (a.src, a.checked) ∧
      Own.Plain.selectRcPolicyForSrc a.src a.front.fir = .zeroRc ∧
      Own.Plain.checkContractPlainMap a.front.fir (Own.Plain.Program.canonical a.front.fir).bodies = true ∧
      a.roots.head? = some root ∧
      rootParamsAllNat a.src root = true ∧
      root.ty = some (sig, ty) ∧
      isImmortalViewType sig ty = true ∧
      root.params = c.abiArity ∧
      Ixon.Address.blake3Pure a.object = c.elfHash ∧
      ∀ (D : X86.Driver), D.Ok a.backend.encoded.text.size →
        Sem.Refines (⟨a.src, a.checked⟩ : CheckedProgram) (Own.Plain.Program.canonical a.fir) ∧
        Sem.Refines a.front.source (a.linked D) ∧
        ∀ (i : Nat × List Nat),
          (∀ k w, Lang.run (a.linked D) i k = .ok w →
            (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
              a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrong i) ∧
          (¬ a.front.GoesWrong i → ∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) ∧
          ((∀ k, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k = .timeout) →
            (∀ k, Lang.run (a.linked D) i k = .timeout) ∨
              ∃ k failure, Lang.run (a.linked D) i k = .resource failure) := by
  unfold verifyProgram at hver
  rw [Bool.and_eq_true] at hver
  rcases hver with ⟨hwf_b, hver⟩
  have hwf := (checkWellFormed_iff c).mp hwf_b
  cases hhead : P.roots.head? with
  | none => simp [hhead] at hver
  | some pair =>
    obtain ⟨rootAddr, rootId⟩ := pair
    simp only [hhead, hpol] at hver
    split at hver
    · next htarget =>
      have htargetEq : rootAddr = c.target := eq_of_beq htarget
      subst htargetEq
      cases hcert : Recheck.Cert.ofText certText with
      | error e => simp [hcert] at hver
      | ok cert =>
        simp only [hcert] at hver
        cases hrunC : Recheck.runWithContracts cfg P cert with
        | error e => simp [hrunC] at hver
        | ok a =>
          simp only [hrunC] at hver
          cases hahead : a.roots.head? with
          | none => simp [hahead] at hver
          | some root =>
            simp only [hahead, Bool.and_eq_true, beq_iff_eq] at hver
            rcases hver with ⟨⟨⟨hrootOk, hrcPol⟩, hparams⟩, hhash⟩
            unfold checkImmortalRoot at hrootOk
            rw [Bool.and_eq_true] at hrootOk
            rcases hrootOk with ⟨hnatParams, htyOk⟩
            cases hty : root.ty with
            | none => simp [hty] at htyOk
            | some st =>
              rcases st with ⟨sig, ty⟩
              simp only [hty] at htyOk
              obtain ⟨hrun, hcheckMap⟩ := Recheck.runWithContracts_parts hrunC
              have hcheckOwn : a.checkContractOwn = true :=
                (Recheck.Artifact.checkContractOwn_iff a).mpr hcheckMap
              refine ⟨cert, a, rootId, root, sig, ty, hwf, rfl, rfl, hrunC, hrun,
                Recheck.run_front hrun, hrcPol, hcheckMap, hahead, hnatParams, hty, htyOk,
                hparams, hhash, ?_⟩
              intro D hD
              exact ⟨Recheck.recheck_contract_own_refines hrun hcheckOwn,
                Recheck.object_refines hrun D hD,
                fun i => Recheck.sound hrun D hD i⟩
    · cases hver

/-- Soundness of `CompileClaim.verifyProgram` under `.plainRc` policy, backed by
`Recheck.RcReplay.sound`, `Recheck.RcReplay.object_refines`, `Recheck.RcReplay.run_front`,
and `checkPlainRcRoot`.
It holds for every `P`; that the check runs within an 8 MiB stack assumes
`P` came from ingress (`Recheck.run`'s precondition). -/
theorem verifyProgram_plainRc_sound {cfg : Recheck.Config} {P : Src.Program}
    {c : CompileClaim} {certText : String}
    (hpol : c.policy = .plainRc)
    (hver : verifyProgram cfg P c certText = true) :
    ∃ (cert : Recheck.RcReplay.Cert) (a : Recheck.RcReplay.Artifact) (rootId : Src.CId)
      (root : Recheck.Root) (sig : Rt.Sig) (ty : Rt.FoTy),
      c.WellFormed ∧
      P.roots.head? = some (c.target, rootId) ∧
      Recheck.RcReplay.Cert.ofText certText = .ok cert ∧
      Recheck.RcReplay.run cfg P cert = .ok a ∧
      Recheck.front cfg P cert.base = .ok (a.front.src, a.front.checked) ∧
      a.roots.head? = some root ∧
      rootParamsAllNat a.front.src root = true ∧
      root.ty = some (sig, ty) ∧
      root.params = c.abiArity ∧
      Ixon.Address.blake3Pure a.backend.object = c.elfHash ∧
      ∀ (D : X86.Driver), D.Ok a.backend.encoded.text.size →
        Sem.Refines a.front.source (a.linked D) ∧
        ∀ (i : Nat × List Nat),
          (∀ clock output, Lang.run (a.linked D) i clock = .ok output →
            (∃ sourceClock value,
              Lang.run (⟨a.front.src, a.front.checked⟩ : CheckedProgram)
                i sourceClock = .ok value ∧
              a.front.view i.1 (Lang.obs value) = some output) ∨ a.front.GoesWrong i) ∧
          (¬ a.front.GoesWrong i →
            ∀ clock, ¬ (Lang.run (a.linked D) i clock).GoesWrong) ∧
          ((∀ clock, Lang.run (⟨a.front.src, a.front.checked⟩ : CheckedProgram)
              i clock = .timeout) →
            (∀ clock, Lang.run (a.linked D) i clock = .timeout) ∨
              ∃ clock resource, Lang.run (a.linked D) i clock = .resource resource) := by
  unfold verifyProgram at hver
  rw [Bool.and_eq_true] at hver
  rcases hver with ⟨hwf_b, hver⟩
  have hwf := (checkWellFormed_iff c).mp hwf_b
  cases hhead : P.roots.head? with
  | none => simp [hhead] at hver
  | some pair =>
    obtain ⟨rootAddr, rootId⟩ := pair
    simp only [hhead, hpol] at hver
    split at hver
    · next htarget =>
      have htargetEq : rootAddr = c.target := eq_of_beq htarget
      subst htargetEq
      cases hcert : Recheck.RcReplay.Cert.ofText certText with
      | error e => simp [hcert] at hver
      | ok cert =>
        simp only [hcert] at hver
        cases hrun : Recheck.RcReplay.run cfg P cert with
        | error e => simp [hrun] at hver
        | ok a =>
          simp only [hrun] at hver
          cases hahead : a.roots.head? with
          | none => simp [hahead] at hver
          | some root =>
            simp only [hahead, Bool.and_eq_true, beq_iff_eq] at hver
            rcases hver with ⟨⟨hrootOk, hparams⟩, hhash⟩
            unfold checkPlainRcRoot at hrootOk
            rw [Bool.and_eq_true] at hrootOk
            rcases hrootOk with ⟨hnatParams, htySome⟩
            cases hty : root.ty with
            | none => simp [hty] at htySome
            | some st =>
              rcases st with ⟨sig, ty⟩
              refine ⟨cert, a, rootId, root, sig, ty, hwf, rfl, rfl, hrun,
                Recheck.RcReplay.run_front hrun, hahead, hnatParams, hty, hparams, hhash, ?_⟩
              intro D hD
              exact ⟨Recheck.RcReplay.object_refines hrun D hD,
                fun i => Recheck.RcReplay.sound hrun D hD i⟩
    · cases hver

/-- End-to-end byte-level soundness of `CompileClaim.verifyBytes` under `.immortal` policy,
exposing `Recheck.ingress`, `Ixon.V3.decodeAnonymousEnv`, `Ixon.V3.Tc.checkEnv` (when `typecheck = true`),
`Src.Resource.validate`, `Src.Ingress.ofEnv` (`Recheck.ingress_parts`), canonical relevance
(`Recheck.checkCanonicalRelevance_iff`), `Recheck.front` (`Src.Relevance.Proof.WellAnnotated`),
and `verifyProgram_immortal_sound`. -/
theorem verifyBytes_immortal_sound {cfg : Recheck.Config} {envBytes : ByteArray}
    {equations : Lean.Json} {c : CompileClaim} {certText : String} {typecheck : Bool}
    (hpol : c.policy = .immortal)
    (hver : verifyBytes cfg envBytes equations c certText typecheck = true) :
    ∃ (inp : Recheck.Input) (cert : Recheck.Cert) (a : Recheck.Artifact)
      (rootId : Src.CId) (root : Recheck.Root) (sig : Rt.Sig) (ty : Rt.FoTy),
      c.WellFormed ∧
      Recheck.ingress envBytes equations (selectTargetRoots cfg equations c.target) typecheck = .ok inp ∧
      Ixon.V3.decodeAnonymousEnv envBytes = .ok inp.env ∧
      (typecheck = true → Ixon.V3.Tc.checkEnv inp.env = .ok ()) ∧
      Src.Resource.validate inp.program = .ok () ∧
      (∃ rawHints chosen rawProg,
        Src.Hints.ofK1Json equations = .ok rawHints ∧
        Recheck.selectRoots rawHints.roots (selectTargetRoots cfg equations c.target) = .ok chosen ∧
        chosen.isEmpty = false ∧
        Src.Ingress.ofEnv inp.env (chosen.map (·.1)) = .ok rawProg ∧
        inp.program = { rawProg with known := Src.Pinned.known rawProg, resource := inp.hints.resource }) ∧
      inp.env.root = c.env ∧
      inp.program.roots.head? = some (c.target, rootId) ∧
      Recheck.Cert.ofText certText = .ok cert ∧
      Recheck.run cfg inp.program cert = .ok a ∧
      Recheck.front cfg inp.program cert = .ok (a.src, a.checked) ∧
      (∃ table installed,
        Src.Table.ofCert cfg.table inp.program cert.table = .ok table ∧
        Src.Relevance.annotate inp.env { inp.program with table } = .ok cert.relevance ∧
        Src.Relevance.install { inp.program with table } cert.relevance = .ok installed ∧
        Src.Relevance.check installed cert.relevance = .ok a.checked ∧
        Src.Relevance.Proof.WellAnnotated installed cert.relevance a.checked ∧
        a.src = Src.Lazify.run installed a.checked.keys) ∧
      a.roots.head? = some root ∧
      rootParamsAllNat a.src root = true ∧
      root.ty = some (sig, ty) ∧
      isImmortalViewType sig ty = true ∧
      root.params = c.abiArity ∧
      Ixon.Address.blake3Pure a.object = c.elfHash ∧
      ∀ (D : X86.Driver), D.Ok a.backend.encoded.text.size →
        Sem.Refines a.front.source (a.linked D) ∧
        ∀ (i : Nat × List Nat),
          (∀ k w, Lang.run (a.linked D) i k = .ok w →
            (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
              a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrong i) ∧
          (¬ a.front.GoesWrong i → ∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) ∧
          ((∀ k, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k = .timeout) →
            (∀ k, Lang.run (a.linked D) i k = .timeout) ∨
              ∃ k failure, Lang.run (a.linked D) i k = .resource failure) := by
  unfold verifyBytes at hver
  cases hing : Recheck.ingress envBytes equations (selectTargetRoots cfg equations c.target) typecheck with
  | error e => simp [hing] at hver
  | ok inp =>
    simp only [hing, Bool.and_eq_true] at hver
    obtain ⟨⟨henv_b, hcanonRel⟩, hprog⟩ := hver
    have henv : inp.env.root = c.env := eq_of_beq henv_b
    obtain ⟨hdec, htc, hres, hingProg⟩ := Recheck.ingress_parts hing
    obtain ⟨cert, a, rootId, root, sig, ty, hwf, hhead, hcert, hrun, hfront, hahead,
      hnatParams, hty, htyOk, hparams, hhash, hsem⟩ :=
      verifyProgram_immortal_sound hpol hprog
    simp only [checkCertCanonicalRelevance, hpol, hcert] at hcanonRel
    obtain ⟨table₀, htab₀, hann⟩ :=
      (Recheck.checkCanonicalRelevance_iff cfg inp cert.table cert.relevance).mp hcanonRel
    obtain ⟨table, installed, htab, hinst, hchk, hwa, hlaz⟩ :=
      Recheck.front_wellAnnotated hfront
    have htabEq : table₀ = table := by
      rw [htab₀] at htab
      cases htab
      rfl
    subst htabEq
    exact ⟨inp, cert, a, rootId, root, sig, ty, hwf, rfl, hdec, htc, hres, hingProg,
      henv, hhead, hcert, hrun, hfront, ⟨table₀, installed, htab₀, hann, hinst, hchk, hwa, hlaz⟩,
      hahead, hnatParams, hty, htyOk, hparams, hhash, hsem⟩

/-- End-to-end byte-level soundness of `CompileClaim.verifyBytes` under `.zeroRc` policy,
exposing `Recheck.ingress`, `Ixon.V3.decodeAnonymousEnv`, `Ixon.V3.Tc.checkEnv` (when `typecheck = true`),
`Src.Resource.validate`, `Src.Ingress.ofEnv` (`Recheck.ingress_parts`), canonical relevance
(`Recheck.checkCanonicalRelevance_iff`), `Recheck.front` (`Src.Relevance.Proof.WellAnnotated`),
and `verifyProgram_zeroRc_sound`. -/
theorem verifyBytes_zeroRc_sound {cfg : Recheck.Config} {envBytes : ByteArray}
    {equations : Lean.Json} {c : CompileClaim} {certText : String} {typecheck : Bool}
    (hpol : c.policy = .zeroRc)
    (hver : verifyBytes cfg envBytes equations c certText typecheck = true) :
    ∃ (inp : Recheck.Input) (cert : Recheck.Cert) (a : Recheck.Artifact)
      (rootId : Src.CId) (root : Recheck.Root) (sig : Rt.Sig) (ty : Rt.FoTy),
      c.WellFormed ∧
      Recheck.ingress envBytes equations (selectTargetRoots cfg equations c.target) typecheck = .ok inp ∧
      Ixon.V3.decodeAnonymousEnv envBytes = .ok inp.env ∧
      (typecheck = true → Ixon.V3.Tc.checkEnv inp.env = .ok ()) ∧
      Src.Resource.validate inp.program = .ok () ∧
      (∃ rawHints chosen rawProg,
        Src.Hints.ofK1Json equations = .ok rawHints ∧
        Recheck.selectRoots rawHints.roots (selectTargetRoots cfg equations c.target) = .ok chosen ∧
        chosen.isEmpty = false ∧
        Src.Ingress.ofEnv inp.env (chosen.map (·.1)) = .ok rawProg ∧
        inp.program = { rawProg with known := Src.Pinned.known rawProg, resource := inp.hints.resource }) ∧
      inp.env.root = c.env ∧
      inp.program.roots.head? = some (c.target, rootId) ∧
      Recheck.Cert.ofText certText = .ok cert ∧
      Recheck.runWithContracts cfg inp.program cert = .ok a ∧
      Recheck.run cfg inp.program cert = .ok a ∧
      Recheck.front cfg inp.program cert = .ok (a.src, a.checked) ∧
      (∃ table installed,
        Src.Table.ofCert cfg.table inp.program cert.table = .ok table ∧
        Src.Relevance.annotate inp.env { inp.program with table } = .ok cert.relevance ∧
        Src.Relevance.install { inp.program with table } cert.relevance = .ok installed ∧
        Src.Relevance.check installed cert.relevance = .ok a.checked ∧
        Src.Relevance.Proof.WellAnnotated installed cert.relevance a.checked ∧
        a.src = Src.Lazify.run installed a.checked.keys) ∧
      Own.Plain.selectRcPolicyForSrc a.src a.front.fir = .zeroRc ∧
      Own.Plain.checkContractPlainMap a.front.fir (Own.Plain.Program.canonical a.front.fir).bodies = true ∧
      a.roots.head? = some root ∧
      rootParamsAllNat a.src root = true ∧
      root.ty = some (sig, ty) ∧
      isImmortalViewType sig ty = true ∧
      root.params = c.abiArity ∧
      Ixon.Address.blake3Pure a.object = c.elfHash ∧
      ∀ (D : X86.Driver), D.Ok a.backend.encoded.text.size →
        Sem.Refines (⟨a.src, a.checked⟩ : CheckedProgram) (Own.Plain.Program.canonical a.fir) ∧
        Sem.Refines a.front.source (a.linked D) ∧
        ∀ (i : Nat × List Nat),
          (∀ k w, Lang.run (a.linked D) i k = .ok w →
            (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
              a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrong i) ∧
          (¬ a.front.GoesWrong i → ∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) ∧
          ((∀ k, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k = .timeout) →
            (∀ k, Lang.run (a.linked D) i k = .timeout) ∨
              ∃ k failure, Lang.run (a.linked D) i k = .resource failure) := by
  unfold verifyBytes at hver
  cases hing : Recheck.ingress envBytes equations (selectTargetRoots cfg equations c.target) typecheck with
  | error e => simp [hing] at hver
  | ok inp =>
    simp only [hing, Bool.and_eq_true] at hver
    obtain ⟨⟨henv_b, hcanonRel⟩, hprog⟩ := hver
    have henv : inp.env.root = c.env := eq_of_beq henv_b
    obtain ⟨hdec, htc, hres, hingProg⟩ := Recheck.ingress_parts hing
    obtain ⟨cert, a, rootId, root, sig, ty, hwf, hhead, hcert, hrunC, hrun, hfront,
      hrcPol, hcheckMap, hahead, hnatParams, hty, htyOk, hparams, hhash, hsem⟩ :=
      verifyProgram_zeroRc_sound hpol hprog
    simp only [checkCertCanonicalRelevance, hpol, hcert] at hcanonRel
    obtain ⟨table₀, htab₀, hann⟩ :=
      (Recheck.checkCanonicalRelevance_iff cfg inp cert.table cert.relevance).mp hcanonRel
    obtain ⟨table, installed, htab, hinst, hchk, hwa, hlaz⟩ :=
      Recheck.front_wellAnnotated hfront
    have htabEq : table₀ = table := by
      rw [htab₀] at htab
      cases htab
      rfl
    subst htabEq
    exact ⟨inp, cert, a, rootId, root, sig, ty, hwf, rfl, hdec, htc, hres, hingProg,
      henv, hhead, hcert, hrunC, hrun, hfront, ⟨table₀, installed, htab₀, hann, hinst, hchk, hwa, hlaz⟩,
      hrcPol, hcheckMap, hahead, hnatParams, hty, htyOk, hparams, hhash, hsem⟩

/-- End-to-end byte-level soundness of `CompileClaim.verifyBytes` under `.plainRc` policy,
exposing `Recheck.ingress`, `Ixon.V3.decodeAnonymousEnv`, `Ixon.V3.Tc.checkEnv` (when `typecheck = true`),
`Src.Resource.validate`, `Src.Ingress.ofEnv` (`Recheck.ingress_parts`), canonical relevance
(`Recheck.checkCanonicalRelevance_iff`), `Recheck.front` (`Src.Relevance.Proof.WellAnnotated`),
and `verifyProgram_plainRc_sound`. -/
theorem verifyBytes_plainRc_sound {cfg : Recheck.Config} {envBytes : ByteArray}
    {equations : Lean.Json} {c : CompileClaim} {certText : String} {typecheck : Bool}
    (hpol : c.policy = .plainRc)
    (hver : verifyBytes cfg envBytes equations c certText typecheck = true) :
    ∃ (inp : Recheck.Input) (cert : Recheck.RcReplay.Cert) (a : Recheck.RcReplay.Artifact)
      (rootId : Src.CId) (root : Recheck.Root) (sig : Rt.Sig) (ty : Rt.FoTy),
      c.WellFormed ∧
      Recheck.ingress envBytes equations (selectTargetRoots cfg equations c.target) typecheck = .ok inp ∧
      Ixon.V3.decodeAnonymousEnv envBytes = .ok inp.env ∧
      (typecheck = true → Ixon.V3.Tc.checkEnv inp.env = .ok ()) ∧
      Src.Resource.validate inp.program = .ok () ∧
      (∃ rawHints chosen rawProg,
        Src.Hints.ofK1Json equations = .ok rawHints ∧
        Recheck.selectRoots rawHints.roots (selectTargetRoots cfg equations c.target) = .ok chosen ∧
        chosen.isEmpty = false ∧
        Src.Ingress.ofEnv inp.env (chosen.map (·.1)) = .ok rawProg ∧
        inp.program = { rawProg with known := Src.Pinned.known rawProg, resource := inp.hints.resource }) ∧
      inp.env.root = c.env ∧
      inp.program.roots.head? = some (c.target, rootId) ∧
      Recheck.RcReplay.Cert.ofText certText = .ok cert ∧
      Recheck.RcReplay.run cfg inp.program cert = .ok a ∧
      Recheck.front cfg inp.program cert.base = .ok (a.front.src, a.front.checked) ∧
      (∃ table installed,
        Src.Table.ofCert cfg.table inp.program cert.base.table = .ok table ∧
        Src.Relevance.annotate inp.env { inp.program with table } = .ok cert.base.relevance ∧
        Src.Relevance.install { inp.program with table } cert.base.relevance = .ok installed ∧
        Src.Relevance.check installed cert.base.relevance = .ok a.front.checked ∧
        Src.Relevance.Proof.WellAnnotated installed cert.base.relevance a.front.checked ∧
        a.front.src = Src.Lazify.run installed a.front.checked.keys) ∧
      a.roots.head? = some root ∧
      rootParamsAllNat a.front.src root = true ∧
      root.ty = some (sig, ty) ∧
      root.params = c.abiArity ∧
      Ixon.Address.blake3Pure a.backend.object = c.elfHash ∧
      ∀ (D : X86.Driver), D.Ok a.backend.encoded.text.size →
        Sem.Refines a.front.source (a.linked D) ∧
        ∀ (i : Nat × List Nat),
          (∀ clock output, Lang.run (a.linked D) i clock = .ok output →
            (∃ sourceClock value,
              Lang.run (⟨a.front.src, a.front.checked⟩ : CheckedProgram)
                i sourceClock = .ok value ∧
              a.front.view i.1 (Lang.obs value) = some output) ∨ a.front.GoesWrong i) ∧
          (¬ a.front.GoesWrong i →
            ∀ clock, ¬ (Lang.run (a.linked D) i clock).GoesWrong) ∧
          ((∀ clock, Lang.run (⟨a.front.src, a.front.checked⟩ : CheckedProgram)
              i clock = .timeout) →
            (∀ clock, Lang.run (a.linked D) i clock = .timeout) ∨
              ∃ clock resource, Lang.run (a.linked D) i clock = .resource resource) := by
  unfold verifyBytes at hver
  cases hing : Recheck.ingress envBytes equations (selectTargetRoots cfg equations c.target) typecheck with
  | error e => simp [hing] at hver
  | ok inp =>
    simp only [hing, Bool.and_eq_true] at hver
    obtain ⟨⟨henv_b, hcanonRel⟩, hprog⟩ := hver
    have henv : inp.env.root = c.env := eq_of_beq henv_b
    obtain ⟨hdec, htc, hres, hingProg⟩ := Recheck.ingress_parts hing
    obtain ⟨cert, a, rootId, root, sig, ty, hwf, hhead, hcert, hrun, hfront, hahead,
      hnatParams, hty, hparams, hhash, hsem⟩ :=
      verifyProgram_plainRc_sound hpol hprog
    simp only [checkCertCanonicalRelevance, hpol, hcert] at hcanonRel
    obtain ⟨table₀, htab₀, hann⟩ :=
      (Recheck.checkCanonicalRelevance_iff cfg inp cert.base.table cert.base.relevance).mp hcanonRel
    obtain ⟨table, installed, htab, hinst, hchk, hwa, hlaz⟩ :=
      Recheck.front_wellAnnotated hfront
    have htabEq : table₀ = table := by
      rw [htab₀] at htab
      cases htab
      rfl
    subst htabEq
    exact ⟨inp, cert, a, rootId, root, sig, ty, hwf, rfl, hdec, htc, hres, hingProg,
      henv, hhead, hcert, hrun, hfront, ⟨table₀, installed, htab₀, hann, hinst, hchk, hwa, hlaz⟩,
      hahead, hnatParams, hty, hparams, hhash, hsem⟩


/-! ## The view's rejections at the claim's root

On the immortal and zero-RC paths the claim's root passes `checkImmortalRoot`,
so the last case of `a.front.GoesWrong` (the view rejects the result) happens
there only when the result is not of the root's result shape
(`Recheck.RootWrongOffShape`, `Recheck.Artifact.goesWrong_immortalRoot`). -/

/-- Under `.immortal`, `verifyProgram`'s artifact goes wrong at the claim's
root only off the root's result shape. -/
theorem verifyProgram_immortal_rootShape {cfg : Recheck.Config} {P : Src.Program}
    {c : CompileClaim} {certText : String}
    (hpol : c.policy = .immortal)
    (hver : verifyProgram cfg P c certText = true) :
    ∃ (cert : Recheck.Cert) (a : Recheck.Artifact) (root : Recheck.Root),
      Recheck.Cert.ofText certText = .ok cert ∧
      Recheck.run cfg P cert = .ok a ∧
      a.roots.head? = some root ∧
      checkImmortalRoot a.src root = true ∧
      Recheck.RootWrongOffShape a root := by
  obtain ⟨cert, a, _, root, sig, ty, _, _, hcert, hrun, _, hahead, hnat, hty, hview, -⟩ :=
    verifyProgram_immortal_sound hpol hver
  have hok : checkImmortalRoot a.src root = true := by
    simp [checkImmortalRoot, hnat, hty, hview]
  exact ⟨cert, a, root, hcert, hrun, hahead, hok,
    Recheck.Artifact.goesWrong_immortalRoot hrun hahead hok⟩

/-- Under `.zeroRc`, `verifyProgram`'s artifact goes wrong at the claim's
root only off the root's result shape. -/
theorem verifyProgram_zeroRc_rootShape {cfg : Recheck.Config} {P : Src.Program}
    {c : CompileClaim} {certText : String}
    (hpol : c.policy = .zeroRc)
    (hver : verifyProgram cfg P c certText = true) :
    ∃ (cert : Recheck.Cert) (a : Recheck.Artifact) (root : Recheck.Root),
      Recheck.Cert.ofText certText = .ok cert ∧
      Recheck.run cfg P cert = .ok a ∧
      a.roots.head? = some root ∧
      checkImmortalRoot a.src root = true ∧
      Recheck.RootWrongOffShape a root := by
  obtain ⟨cert, a, _, root, sig, ty, _, _, hcert, _, hrun, _, _, _, hahead, hnat, hty, hview, -⟩ :=
    verifyProgram_zeroRc_sound hpol hver
  have hok : checkImmortalRoot a.src root = true := by
    simp [checkImmortalRoot, hnat, hty, hview]
  exact ⟨cert, a, root, hcert, hrun, hahead, hok,
    Recheck.Artifact.goesWrong_immortalRoot hrun hahead hok⟩

/-- Under `.immortal`, `verifyBytes`'s artifact (on the ingested program) goes
wrong at the claim's root only off the root's result shape. -/
theorem verifyBytes_immortal_rootShape {cfg : Recheck.Config} {envBytes : ByteArray}
    {equations : Lean.Json} {c : CompileClaim} {certText : String} {typecheck : Bool}
    (hpol : c.policy = .immortal)
    (hver : verifyBytes cfg envBytes equations c certText typecheck = true) :
    ∃ (inp : Recheck.Input) (cert : Recheck.Cert) (a : Recheck.Artifact) (root : Recheck.Root),
      Recheck.ingress envBytes equations (selectTargetRoots cfg equations c.target) typecheck = .ok inp ∧
      Recheck.Cert.ofText certText = .ok cert ∧
      Recheck.run cfg inp.program cert = .ok a ∧
      a.roots.head? = some root ∧
      checkImmortalRoot a.src root = true ∧
      Recheck.RootWrongOffShape a root := by
  unfold verifyBytes at hver
  cases hing : Recheck.ingress envBytes equations (selectTargetRoots cfg equations c.target) typecheck with
  | error e => simp [hing] at hver
  | ok inp =>
    simp only [hing, Bool.and_eq_true] at hver
    obtain ⟨cert, a, root, h⟩ := verifyProgram_immortal_rootShape hpol hver.2
    exact ⟨inp, cert, a, root, rfl, h⟩

/-- Under `.zeroRc`, `verifyBytes`'s artifact (on the ingested program) goes
wrong at the claim's root only off the root's result shape. -/
theorem verifyBytes_zeroRc_rootShape {cfg : Recheck.Config} {envBytes : ByteArray}
    {equations : Lean.Json} {c : CompileClaim} {certText : String} {typecheck : Bool}
    (hpol : c.policy = .zeroRc)
    (hver : verifyBytes cfg envBytes equations c certText typecheck = true) :
    ∃ (inp : Recheck.Input) (cert : Recheck.Cert) (a : Recheck.Artifact) (root : Recheck.Root),
      Recheck.ingress envBytes equations (selectTargetRoots cfg equations c.target) typecheck = .ok inp ∧
      Recheck.Cert.ofText certText = .ok cert ∧
      Recheck.run cfg inp.program cert = .ok a ∧
      a.roots.head? = some root ∧
      checkImmortalRoot a.src root = true ∧
      Recheck.RootWrongOffShape a root := by
  unfold verifyBytes at hver
  cases hing : Recheck.ingress envBytes equations (selectTargetRoots cfg equations c.target) typecheck with
  | error e => simp [hing] at hver
  | ok inp =>
    simp only [hing, Bool.and_eq_true] at hver
    obtain ⟨cert, a, root, h⟩ := verifyProgram_zeroRc_rootShape hpol hver.2
    exact ⟨inp, cert, a, root, rfl, h⟩

end IxCC.CompileClaim
