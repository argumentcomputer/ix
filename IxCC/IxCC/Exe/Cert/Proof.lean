import IxCC.Exe.Cert
import IxCC.CompileClaim.Proof

/-! # End-to-End Soundness of `IxCC.Exe.Cert.verifyExeBytes`

Connects `.ix.cert` v1 byte verification (`verifyExeBytes`) end-to-end to:
1. Full `Recheck.ingress`, `KF-4` pure logical seed-closure kernel acceptance
   (`Ix.Kernel.Admission.checkBytes` under committed `preludeFor` and committed
   `defaultBinding`, `tableRestrictsDefault`, and `N5` `checkClosureModes`),
   canonical relevance (`Stage A`), `Definition.asserts` (`EM-0`), and
   `CompileClaim.verifyProgram` (all `verifyProgram_*_sound` refinement guarantees).
2. Deterministic re-assembly of `expectedCore` via `Exe.build` (plain `--exe`)
   or `Exe.buildMachine` (`--exe --machine`), carrying `X86.Exe.Certified` /
   `X86.Exe.Machine.Certified` (`Shell.check` + `X86.Exe.checkFor`).
3. Hardened `.ix.cert` v1 ELF64 trailer invariants (`X86.Exe.Cert.checkTrailer`):
   exact core byte equality under `zeroShdr`, strict `0xCC` (`int3`) RX
   page-tail sled in `[coreSz .. alignUp coreSz 4096)`, page-aligned non-alloc
   `.ix.cert` payload, and flush 3-entry section header table at EOF. -/

set_option autoImplicit false

namespace IxCC.Exe.Cert

open IxCC.Recheck
open IxCC.X86.Exe.Cert

private theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem except_mapError_ok {ε₁ ε₂ α : Type} {f : ε₁ → ε₂} {x : Except ε₁ α} {a : α}
    (h : x.mapError f = .ok a) : x = .ok a := by
  cases x with
  | error e => cases h
  | ok a' => cases h; rfl

private theorem optionToExcept_ok {α : Type} {e : Err} {o : Option α} {a : α}
    (h : optionToExcept e o = .ok a) : o = some a := by
  cases o with
  | none => cases h
  | some a' => cases h; rfl

private theorem requireBool_ok {c : Bool} {e : Err}
    (h : requireBool c e = .ok ()) : c = true := by
  cases c with
  | false => cases h
  | true => rfl

/-- **End-to-end soundness of `verifyExeBytes`**: any certified executable
accepted by `verifyExeBytes` at default kernel limits deterministically
re-assembles its checked core `expectedCore` from a `KF-4` + `SP-0` + `N5`
logically-accepted `CompileClaim`, matches `expectedCore` byte-for-byte after
zeroing only the 12 ELF64 shdr pointer bytes, fills the entire RX page tail
`[coreSize .. alignUp coreSize 4096)` strictly with `0xCC` (`int3`), places
`.ix.cert` page-aligned at `pageEnd`, and ends flush at EOF. -/
theorem verifyExeBytes_sound {exeBytes : ByteArray} {extEnv? extEq? : Option ByteArray}
    {v : VerifiedExe}
    (h : verifyExeBytes exeBytes extEnv? extEq? Src.KernelFront.defaultLimits = .ok v) :
    ∃ (payloadBytes : ByteArray) (payload : Payload) (envBytes : ByteArray)
      (equations : Lean.Json) (certText : String) (inp : Recheck.Input)
      (tc : Src.Table.TableCert)
      (cl : CompileClaim.ClosureAccepted inp v.claim.target tc Src.KernelFront.defaultLimits)
      (a : Recheck.Artifact) (expectedCore : ByteArray),
      let selCfg : Recheck.Config := { names := v.rootNames }
      let cfg : Recheck.Config := Recheck.Config.forInput selCfg inp
      extractTrailer exeBytes = .ok (v.coreSize, payloadBytes) ∧
      Payload.decode payloadBytes = .ok payload ∧
      CompileClaim.ofClaimBytes payload.claimBytes = some v.claim ∧
      Recheck.ingress envBytes equations
        (CompileClaim.selectTargetRoots selCfg equations v.claim.target)
        Src.KernelFront.defaultLimits = .ok inp ∧
      inp.env.root = v.claim.env ∧
      inp.env.bindingAddress = v.claim.roleTable ∧
      CompileClaim.checkCertSeedClosure inp v.claim.target v.claim.policy certText
        Src.KernelFront.defaultLimits = .ok ⟨tc, cl⟩ ∧
      Ix.Kernel.Admission.checkBytes Src.KernelFront.hash cl.defBinding
        Src.KernelFront.defaultLimits cl.records cl.blobs cl.hints.lookup = .ok cl.env ∧
      CompileClaim.tableRestrictsDefault inp.kernel.acc.table cl.defTable = true ∧
      CompileClaim.checkClosureModes cl.defTable cl.pre cl.env cl.constants cl.blobs = .ok () ∧
      CompileClaim.checkCertCanonicalRelevance cfg inp v.claim.policy certText = true ∧
      CompileClaim.checkCertDefAsserts cfg inp v.claim.policy certText = true ∧
      CompileClaim.verifyProgram cfg inp.program v.claim certText = true ∧
      checkTrailer expectedCore payloadBytes exeBytes = true ∧
      zeroShdr (exeBytes.extract 0 expectedCore.size) = expectedCore ∧
      (∀ i, expectedCore.size ≤ i → i < X86.Exe.alignUp expectedCore.size certPageSize →
        exeBytes.data[i]? = some trapByte) ∧
      exeBytes.extract (X86.Exe.alignUp expectedCore.size certPageSize)
        (X86.Exe.alignUp expectedCore.size certPageSize + payloadBytes.size) = payloadBytes ∧
      exeBytes.size = X86.Exe.alignUp
        (X86.Exe.alignUp expectedCore.size certPageSize + payloadBytes.size + shstrtabBytes.size) 8 +
        shdrTableSize ∧
      (v.claim.policy = .immortal ∨ v.claim.policy = .zeroRc →
        ∃ cert, Recheck.Cert.ofText certText = .ok cert ∧ Recheck.run cfg inp.program cert = .ok a) ∧
      (v.claim.policy = .plainRc →
        ∃ cert rcArt, Recheck.RcReplay.Cert.ofText certText = .ok cert ∧
          Recheck.RcReplay.run cfg inp.program cert = .ok rcArt ∧
          rcArt.toRecheckArtifact cert = .ok a) ∧
      (v.exeKind = .plain →
        ∃ (i : X86.Exe.Input) (ce : X86.Exe.Certified i),
          Exe.build a v.layout = .ok ⟨i, ce⟩ ∧ ce.bytes = expectedCore) ∧
      (v.exeKind = .machine →
        let L : X86.Exe.Machine.Layout := { stack := v.layout.stack, region := v.layout.region }
        ∃ (root : Recheck.Root) (ce : X86.Exe.Machine.Certified L root.symbol a.object),
          Exe.buildMachine a L = .ok ⟨root, ce⟩ ∧ ce.checked.bytes = expectedCore) := by
  unfold verifyExeBytes at h
  obtain ⟨⟨coreSz, payloadBytes⟩, hextM, h⟩ := except_bind_ok h
  have hext := except_mapError_ok hextM
  obtain ⟨payload, hdecM, h⟩ := except_bind_ok h
  have hdec := except_mapError_ok hdecM
  obtain ⟨claim, hclmE, h⟩ := except_bind_ok h
  have hclm := optionToExcept_ok hclmE
  obtain ⟨envBytes, -, h⟩ := except_bind_ok h
  obtain ⟨eqRaw, -, h⟩ := except_bind_ok h
  obtain ⟨certText, -, h⟩ := except_bind_ok h
  obtain ⟨equations, -, h⟩ := except_bind_ok h
  obtain ⟨inp, hing, h⟩ := except_bind_ok h
  obtain ⟨_, hIdU, h⟩ := except_bind_ok h
  have hIdCheck := requireBool_ok hIdU
  simp only [Bool.and_eq_true, beq_iff_eq] at hIdCheck
  obtain ⟨henvRoot, hroleAddr⟩ := hIdCheck
  obtain ⟨⟨tc, cl⟩, hkf4M, h⟩ := except_bind_ok h
  have hkf4 := except_mapError_ok hkf4M
  obtain ⟨_, hrelU, h⟩ := except_bind_ok h
  have hrel := requireBool_ok hrelU
  obtain ⟨_, hassU, h⟩ := except_bind_ok h
  have hass := requireBool_ok hassU
  obtain ⟨a, ha, h⟩ := except_bind_ok h
  obtain ⟨_, hvpU, h⟩ := except_bind_ok h
  have hvp := requireBool_ok hvpU
  obtain ⟨expectedCore, hcore, h⟩ := except_bind_ok h
  obtain ⟨_, htrU, h⟩ := except_bind_ok h
  have htr := requireBool_ok htrU
  simp only [Bool.and_eq_true, beq_iff_eq] at htr
  obtain ⟨hcoreEq, hchk⟩ := htr
  cases h
  have hImmRun : claim.policy = .immortal ∨ claim.policy = .zeroRc →
      ∃ cert, Recheck.Cert.ofText certText = .ok cert ∧
        Recheck.run (Recheck.Config.forInput { names := payload.rootNames } inp) inp.program cert = .ok a := by
    intro hpol
    unfold replayArtifact at ha
    rcases hpol with hp | hp
    · rw [hp] at ha
      obtain ⟨cert, hcert, hrun⟩ := except_bind_ok ha
      exact ⟨cert, hcert, hrun⟩
    · rw [hp] at ha
      obtain ⟨cert, hcert, ha'⟩ := except_bind_ok ha
      obtain ⟨art, hrunW, ha''⟩ := except_bind_ok ha'
      cases hz : (Own.Plain.selectRcPolicyForSrc art.src art.front.fir == .zeroRc) with
      | false =>
        simp only [hz, Bool.false_eq_true, ↓reduceIte,
          bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at ha''
        cases ha''
      | true =>
        simp only [hz, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at ha''
        subst ha''
        exact ⟨cert, hcert, (Recheck.runWithContracts_parts hrunW).1⟩
  have hRcRun : claim.policy = .plainRc →
      ∃ cert rcArt, Recheck.RcReplay.Cert.ofText certText = .ok cert ∧
        Recheck.RcReplay.run (Recheck.Config.forInput { names := payload.rootNames } inp) inp.program cert = .ok rcArt ∧
        rcArt.toRecheckArtifact cert = .ok a := by
    intro hp
    unfold replayArtifact at ha
    rw [hp] at ha
    obtain ⟨cert, hcertM, ha'⟩ := except_bind_ok ha
    obtain ⟨rcArt, hrunR, hto⟩ := except_bind_ok ha'
    exact ⟨cert, rcArt, except_mapError_ok hcertM, hrunR, hto⟩
  have hPlain : payload.exeKind = .plain →
      ∃ (i : X86.Exe.Input) (ce : X86.Exe.Certified i),
        Exe.build a { stack := payload.stack, region := payload.region } = .ok ⟨i, ce⟩ ∧
        ce.bytes = expectedCore := by
    intro hk
    unfold rebuildExpectedCore at hcore
    rw [hk] at hcore
    obtain ⟨⟨i, ce⟩, hb, hpure⟩ := except_bind_ok hcore
    cases hpure
    exact ⟨i, ce, hb, rfl⟩
  have hMachine : payload.exeKind = .machine →
      let L : X86.Exe.Machine.Layout := { stack := payload.stack, region := payload.region }
      ∃ (root : Recheck.Root) (ce : X86.Exe.Machine.Certified L root.symbol a.object),
        Exe.buildMachine a L = .ok ⟨root, ce⟩ ∧ ce.checked.bytes = expectedCore := by
    intro hk
    unfold rebuildExpectedCore at hcore
    rw [hk] at hcore
    obtain ⟨⟨root, ce⟩, hb, hpure⟩ := except_bind_ok hcore
    cases hpure
    exact ⟨root, ce, hb, rfl⟩
  rw [hcoreEq] at hext
  exact ⟨payloadBytes, payload, envBytes, equations, certText, inp, tc, cl, a,
    expectedCore, hext, hdec, hclm, hing, henvRoot, hroleAddr, hkf4, cl.accepted,
    cl.tableRestricted, cl.modesOk, hrel, hass, hvp, hchk,
    checkTrailer_core_eq hchk, checkTrailer_sled_int3 hchk,
    (checkTrailer_payload_eq hchk).2.2, checkTrailer_flush_eof hchk,
    hImmRun, hRcRun, hPlain, hMachine⟩

end IxCC.Exe.Cert
