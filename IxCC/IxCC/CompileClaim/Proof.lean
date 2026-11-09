import IxCC.CompileClaim
import IxCC.Compiler.Proof
import IxCC.Recheck.Proof.Soundness
import IxCC.Recheck.Rc.Proof.ObjectSound

/-! # `CompileClaim.Proof`: Wire Roundtrip & End-to-End Soundness Theorems

Proves canonical wire serialization roundtrip (`ofPayloadBytes_toPayloadBytes`,
`ofClaimBytes_toClaimBytes`) and end-to-end verification soundness across all
three policies (`.immortal`, `.zeroRc`, `.plainRc`):

- `verifyProgram_immortal_sound`, `verifyProgram_zeroRc_sound`, `verifyProgram_plainRc_sound`
- `verifyBytes_immortal_sound`, `verifyBytes_zeroRc_sound`, `verifyBytes_plainRc_sound`

## Scope and Trust Boundary Notes (`A1-1..A1-10`, `A6-2`, `A6-3`, `A6-8`)

1. **Ingress & Kernel Typechecking (`S4`, `A1-6`)**:
   - `verifyBytes` defaults to `typecheck := true`, and `verifyBytes_*_sound`
     explicitly exposes `Recheck.ingress envBytes equations (selectTargetRoots cfg equations c.target) typecheck = .ok inp`,
     `Ixon.V3.decodeAnonymousEnv envBytes = .ok inp.env`,
     `typecheck = true → Ixon.V3.Tc.checkEnv inp.env = .ok ()`, and
     `Src.Resource.validate inp.program = .ok ()`.

2. **Front-End Recheck Step (`S6`, `S8`, `A1-2`, `A6-2`)**:
   - Every soundness theorem exposes `Recheck.front cfg P cert = .ok (a.src, a.checked)`
     (or `Recheck.front cfg P cert.base = .ok (a.front.src, a.front.checked)` under
     `.plainRc`). `Recheck.front` runs `Src.Table.ofCert`, then
     `Src.Recheck.annotation` (which runs `Relevance.check` and `Lazify.run`), then
     `Relevance.checkCanonical`.
   - Note (stage S): `CheckedProgram` evaluates `a.src` after table installation,
     relevance annotation recheck, and `Lazify` under `SrcEval` (`Lam.Erase.Proof`).
     These theorems state that `front` ran, not what it preserves: connecting its
     result semantically back to raw `Ixon.V3` kernel reduction is stage K's
     obligation, not stage S's, and is open.

3. **Observable Roots & `Nat`-Parameter ABI (`S7`, `A1-3`, `A6-8`)**:
   - `verifyProgram` rejects roots with `root.ty = none`, non-`Nat` parameter domains
     (`rootParamsAllNat`), or non-scalar/non-enum return types on the immortal/`.zeroRc`
     paths (`isImmortalViewType`), preventing vacuous satisfaction via `Front.GoesWrong`. -/

set_option autoImplicit false

namespace IxCC.CompileClaim

open IxCC.Sem (Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)

theorem checkWellFormed_iff (c : CompileClaim) :
    c.checkWellFormed = true ↔ c.WellFormed := by
  simp [checkWellFormed, WellFormed]

/-- `getPayloadM` consumes `c.toPayloadBytes` and returns `c` for any well-formed `CompileClaim`. -/
theorem getPayloadM_spec {c : CompileClaim} (hwf : c.WellFormed) :
    Ixon.GetSpec getPayloadM c.toPayloadBytes c := by
  have henv : Ixon.GetSpec (Ixon.Serialize.get : Ixon.GetM Ixon.Address) c.env.hash c.env :=
    Ixon.Address.get_spec c.env
  have htarget : Ixon.GetSpec (Ixon.Serialize.get : Ixon.GetM Ixon.Address) c.target.hash c.target :=
    Ixon.Address.get_spec c.target
  have hpol : Ixon.GetSpec Ixon.getU8 (Ixon.u8Bytes c.policy.toUInt8) c.policy.toUInt8 :=
    Ixon.getU8_spec c.policy.toUInt8
  let arityTag : Ixon.Tag0 := ⟨UInt64.ofNat c.abiArity⟩
  have harity : Ixon.GetSpec Ixon.getTag0 (Ixon.tag0Bytes arityTag) arityTag :=
    Ixon.getTag0_encoded_spec arityTag
  have helf : Ixon.GetSpec (Ixon.Serialize.get : Ixon.GetM Ixon.Address) c.elfHash.hash c.elfHash :=
    Ixon.Address.get_spec c.elfHash
  have harity_toNat : arityTag.size.toNat = c.abiArity :=
    UInt64.toNat_ofNat_of_lt hwf
  have hstep4 : Ixon.GetSpec (do
      let elfHash ← (Ixon.Serialize.get : Ixon.GetM Ixon.Address)
      pure ({
        env := c.env
        target := c.target
        policy := c.policy
        abiArity := arityTag.size.toNat
        elfHash
      } : CompileClaim)) c.elfHash.hash c := by
    have hpure : Ixon.GetSpec (pure ({
      env := c.env
      target := c.target
      policy := c.policy
      abiArity := arityTag.size.toNat
      elfHash := c.elfHash
    } : CompileClaim)) ByteArray.empty ({
      env := c.env
      target := c.target
      policy := c.policy
      abiArity := arityTag.size.toNat
      elfHash := c.elfHash
    } : CompileClaim) := Ixon.GetSpec.pure _
    have h := Ixon.GetSpec.bind (next := fun elfHash => pure ({
      env := c.env
      target := c.target
      policy := c.policy
      abiArity := arityTag.size.toNat
      elfHash
    } : CompileClaim)) helf hpure
    rcases c with ⟨env, target, pol, arity, elfHash⟩
    simpa [ByteArray.append_empty, harity_toNat] using h
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

/-- Canonical payload serialization roundtrip (`A1-10`). -/
theorem ofPayloadBytes_toPayloadBytes {c : CompileClaim} (hwf : c.WellFormed) :
    ofPayloadBytes c.toPayloadBytes = some c := by
  unfold ofPayloadBytes
  rw [Ixon.runGet_eq_ok_of_spec (getPayloadM_spec hwf)]
  rfl

/-- Canonical full wire-envelope serialization roundtrip (`S12`, `A1-4`, `A1-10`). -/
theorem ofClaimBytes_toClaimBytes {c : CompileClaim} (hwf : c.WellFormed) :
    ofClaimBytes c.toClaimBytes = some c := by
  unfold ofClaimBytes
  rw [Ixon.runGet_eq_ok_of_spec (getClaimM_spec hwf)]
  rfl

/-- Soundness of `CompileClaim.verifyProgram` under `.immortal` policy, backed by
`Recheck.sound`, `Recheck.object_refines`, `Recheck.run_front`, and `checkImmortalRoot`. -/
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
      rootParamsAllNat a.src root.const = true ∧
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
`Recheck.recheckWithContracts_sound`, `Recheck.run_front`, and `checkImmortalRoot`. -/
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
      rootParamsAllNat a.src root.const = true ∧
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
and `checkPlainRcRoot`. -/
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
      rootParamsAllNat a.front.src root.const = true ∧
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
`Src.Resource.validate`, `Recheck.front`, and `verifyProgram_immortal_sound`. -/
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
      inp.env.root = c.env ∧
      inp.program.roots.head? = some (c.target, rootId) ∧
      Recheck.Cert.ofText certText = .ok cert ∧
      Recheck.run cfg inp.program cert = .ok a ∧
      Recheck.front cfg inp.program cert = .ok (a.src, a.checked) ∧
      a.roots.head? = some root ∧
      rootParamsAllNat a.src root.const = true ∧
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
    obtain ⟨henv_b, hprog⟩ := hver
    have henv : inp.env.root = c.env := eq_of_beq henv_b
    obtain ⟨hdec, htc, hres, _⟩ := Recheck.ingress_parts hing
    obtain ⟨cert, a, rootId, root, sig, ty, hwf, hhead, hcert, hrun, hfront, hahead,
      hnatParams, hty, htyOk, hparams, hhash, hsem⟩ :=
      verifyProgram_immortal_sound hpol hprog
    exact ⟨inp, cert, a, rootId, root, sig, ty, hwf, rfl, hdec, htc, hres,
      henv, hhead, hcert, hrun, hfront, hahead, hnatParams, hty, htyOk, hparams, hhash, hsem⟩

/-- End-to-end byte-level soundness of `CompileClaim.verifyBytes` under `.zeroRc` policy,
exposing `Recheck.ingress`, `Ixon.V3.decodeAnonymousEnv`, `Ixon.V3.Tc.checkEnv` (when `typecheck = true`),
`Src.Resource.validate`, `Recheck.front`, and `verifyProgram_zeroRc_sound`. -/
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
      inp.env.root = c.env ∧
      inp.program.roots.head? = some (c.target, rootId) ∧
      Recheck.Cert.ofText certText = .ok cert ∧
      Recheck.runWithContracts cfg inp.program cert = .ok a ∧
      Recheck.run cfg inp.program cert = .ok a ∧
      Recheck.front cfg inp.program cert = .ok (a.src, a.checked) ∧
      Own.Plain.selectRcPolicyForSrc a.src a.front.fir = .zeroRc ∧
      Own.Plain.checkContractPlainMap a.front.fir (Own.Plain.Program.canonical a.front.fir).bodies = true ∧
      a.roots.head? = some root ∧
      rootParamsAllNat a.src root.const = true ∧
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
    obtain ⟨henv_b, hprog⟩ := hver
    have henv : inp.env.root = c.env := eq_of_beq henv_b
    obtain ⟨hdec, htc, hres, _⟩ := Recheck.ingress_parts hing
    obtain ⟨cert, a, rootId, root, sig, ty, hwf, hhead, hcert, hrunC, hrun, hfront,
      hrcPol, hcheckMap, hahead, hnatParams, hty, htyOk, hparams, hhash, hsem⟩ :=
      verifyProgram_zeroRc_sound hpol hprog
    exact ⟨inp, cert, a, rootId, root, sig, ty, hwf, rfl, hdec, htc, hres,
      henv, hhead, hcert, hrunC, hrun, hfront, hrcPol, hcheckMap, hahead,
      hnatParams, hty, htyOk, hparams, hhash, hsem⟩

/-- End-to-end byte-level soundness of `CompileClaim.verifyBytes` under `.plainRc` policy,
exposing `Recheck.ingress`, `Ixon.V3.decodeAnonymousEnv`, `Ixon.V3.Tc.checkEnv` (when `typecheck = true`),
`Src.Resource.validate`, `Recheck.front`, and `verifyProgram_plainRc_sound`. -/
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
      inp.env.root = c.env ∧
      inp.program.roots.head? = some (c.target, rootId) ∧
      Recheck.RcReplay.Cert.ofText certText = .ok cert ∧
      Recheck.RcReplay.run cfg inp.program cert = .ok a ∧
      Recheck.front cfg inp.program cert.base = .ok (a.front.src, a.front.checked) ∧
      a.roots.head? = some root ∧
      rootParamsAllNat a.front.src root.const = true ∧
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
    obtain ⟨henv_b, hprog⟩ := hver
    have henv : inp.env.root = c.env := eq_of_beq henv_b
    obtain ⟨hdec, htc, hres, _⟩ := Recheck.ingress_parts hing
    obtain ⟨cert, a, rootId, root, sig, ty, hwf, hhead, hcert, hrun, hfront, hahead,
      hnatParams, hty, hparams, hhash, hsem⟩ :=
      verifyProgram_plainRc_sound hpol hprog
    exact ⟨inp, cert, a, rootId, root, sig, ty, hwf, rfl, hdec, htc, hres,
      henv, hhead, hcert, hrun, hfront, hahead, hnatParams, hty, hparams, hhash, hsem⟩

end IxCC.CompileClaim
