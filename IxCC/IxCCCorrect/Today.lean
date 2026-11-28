import IxCC.Exe.Plain.Exe
import IxCCCorrect.Process

/-!
# `CorrectToday`: what the existing theorems give (`IxCCCorrect.Today`)

The strongest proposition about a claim and a shipped file, in this library's
process vocabulary, that follows from theorems already proved
(`Exe.Cert.verifyExeBytes_sound`, `Exe.Plain.plain_exe_sound`,
`Exe.Plain.Rc.plain_exe_sound`), and the proof that it does
(`correctToday_of_accepts`). Every place where it says less than `Correct` is a
bound variable or a disjunct of the definition, named below.

| | Where it shows in `CorrectToday` | What `Correct` has instead |
| --- | --- | --- |
| W1 | `SourceToday`: the source semantics is IxCC's evaluator on a program made from a certificate, which is quantified existentially | the kernel meaning of `claim.target` (`Agrees`) |
| W2 | `equations`, `rootNames`: the hint sidecar and the root selection are quantified existentially; the claim binds neither | no such inputs |
| W3 | the `goesWrong` disjunct of `PlainExeOutcome`: where the source evaluator is stuck, traps or returns a value its root's type does not read back, the trace is unconstrained, including its system calls | no such case (`Tier1`, `Tier2`) |
| W4 | the resource disjuncts of `PlainExeOutcome` (heap, stack, `natOverflow`, and "nothing after confinement"), allowed on every input | `Tier3`: only limits the claim leaves open, and no silent stop |
| W5 | `core`: the traces are those of the core image from a loader state of the core image; the shipped file is related to it only by `zeroShdr` and the page-tail bytes | the traces of the shipped file (`LoadedFile exe`, `execImage exe`) |
| W6 | `arity`, `result`, `data`: the shell's parameters are quantified existentially, not read from the claim | `claim.abi` |
| W7 | the claim is the one the file carries, the kernel limits are the defaults, and `claim.elfHash` (the object's digest) does not occur | the claim is an input; `Claim.Binds` |

It is safety only: `PlainExeOutcome` holds of the empty trace.

Scope: plain executables (`v.exeKind = .plain`). The `--machine` kind has the same
shape over `X86.Exe.Process.Outcome`.
-/

set_option autoImplicit false

namespace IxCC.Correct

open IxCC.X86
open IxCC.X86.Exe
open IxCC.X86.Exe.Process

/-! ## The file-level loader state on a checked core -/

/-- **`LoadedFile` on a checked core is `Process.Loaded`.** The entry point and the
program headers `LoadedFile` reads from the bytes are the ones the check
established (`FieldsFor.header`), so the loader state of the file is a loader
state of the checked executable. -/
theorem LoadedFile.toLoaded {f : Frame} {object : ByteArray} (c : Checked f object)
    {args : List (List Nat)} {s : ByteEval.State} (h : LoadedFile c.bytes args s) :
    Loaded c args s := by
  obtain ⟨view, hparse, hrip, hbytes, hargs⟩ := h
  obtain ⟨parts, -, -, hf⟩ := c.valid
  obtain ⟨view', hparse', hhdr, hprog⟩ := hf.header
  have hv : view = view' := Option.some.inj (hparse.symm.trans hparse')
  subst hv
  have hentry : view.header.entry = fileBase + c.plan.placement.shellOffset :=
    congrArg ELFRead.Header.entry hhdr
  refine ⟨?_, ?_, ?_⟩
  · rw [hrip, hentry]
  · intro i hi
    have hi' : i < c.plan.placement.fileSize := by
      rw [← hf.size]
      exact hi
    have hmem : (⟨1, 5, 0, fileBase, fileBase, c.plan.placement.fileSize,
        c.plan.placement.fileSize, 0x1000⟩ : Read.ProgramHeader) ∈ view.programs := by
      rw [hprog]
      unfold expectedProgramsFor programHeadersFor
      exact List.mem_map.mpr ⟨(1, 5, 0, fileBase, c.plan.placement.fileSize,
        c.plan.placement.fileSize, 0x1000),
        List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (List.mem_singleton.mpr rfl)))), rfl⟩
    have hb : s.core.memory.bytes (UInt64.ofNat (fileBase + i)) = c.bytes[0 + i]! :=
      hbytes _ hmem rfl i hi'
    rwa [Nat.zero_add] at hb
  · refine ArgBlock.mono (fun a ha => ⟨?_, ha.2⟩) hargs
    intro seg hseg
    obtain ⟨address, size⟩ := seg
    have hmem : (⟨1, 6, 0, address, address, 0, size, 0x1000⟩ : Read.ProgramHeader) ∈
        view.programs := by
      rw [hprog]
      unfold expectedProgramsFor programHeadersFor
      exact List.mem_map.mpr ⟨(1, 6, 0, address, 0, size, 0x1000),
        List.mem_append.mpr (.inl (List.mem_append.mpr (.inr
          (List.mem_map.mpr ⟨(address, size), hseg, rfl⟩)))), rfl⟩
    exact ha.1 _ hmem rfl

/-! ## The claim's target is the program's first root -/

/-- `CompileClaim.verifyProgram` accepts only a program whose first root is the
claim's target. -/
theorem verifyProgram_target {cfg : Recheck.Config} {P : Src.Program} {c : CompileClaim}
    {certText : String} (h : CompileClaim.verifyProgram cfg P c certText = true) :
    ∃ rootId, P.roots.head? = some (c.target, rootId) := by
  unfold CompileClaim.verifyProgram at h
  rw [Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  cases hhead : P.roots.head? with
  | none => simp [hhead] at h
  | some pair =>
    obtain ⟨rootAddr, rootId⟩ := pair
    simp only [hhead] at h
    by_cases ht : (rootAddr == c.target) = true
    · exact ⟨rootId, by rw [eq_of_beq ht]⟩
    · simp [ht] at h

/-! ## `CorrectToday` -/

/-- **W1: today's source side.** The source semantics the existing theorems speak
about is IxCC's own evaluator (`Exe.Plain.srcPlainEval`) on the program the front
end makes from a certificate, with that program's "goes wrong" set. The
certificate is an argument of the constructor and so a free choice wherever
`SourceToday` is used under an existential: nothing here says the program means
what the kernel says the target means. -/
inductive SourceToday (cfg : Recheck.Config) (P : Src.Program) :
    (List Nat → Option Sem.Obs → Prop) → (List Nat → Prop) → Prop
  /-- The immortal and zero-RC replays. -/
  | replay {c : Recheck.Cert} {a : Recheck.Artifact} (h : Recheck.run cfg P c = .ok a) :
      SourceToday cfg P (IxCC.Exe.Plain.srcPlainEval a.src a.checked a.front.view)
        (fun ns => a.front.GoesWrong (0, ns))
  /-- The plain-RC replay. -/
  | rcReplay {c : Recheck.RcReplay.Cert} {a : Recheck.RcReplay.Artifact}
      (h : Recheck.RcReplay.run cfg P c = .ok a) :
      SourceToday cfg P (IxCC.Exe.Plain.srcPlainEval a.front.src a.front.checked a.front.view)
        (fun ns => a.front.GoesWrong (0, ns))

/-- **`CorrectToday claim exe`** (plain executables). There are an environment with
the claim's root and role table whose first selected root is the claim's target, a
source semantics of today's kind for it, and a core image that the shipped file
reproduces under `zeroShdr` with an `int3` page tail, such that every finite trace
of **the core image**, from every loader state of the core image, satisfies
`Exe.Plain.PlainExeOutcome` against that source semantics. The weaknesses W1 to W7
of the module note are the existential binders and the disjuncts of
`PlainExeOutcome`. -/
def CorrectToday (claim : CompileClaim) (exe : ByteArray) : Prop :=
  ∃ (envBytes : ByteArray) (equations : Lean.Json) (rootNames : List String)
    (inp : Recheck.Input)
    (srcEval : List Nat → Option Sem.Obs → Prop) (goesWrong : List Nat → Prop)
    (core : ByteArray) (arity : Nat) (result : ResultKind) (data : Nat),
    Recheck.ingress envBytes equations
      (CompileClaim.selectTargetRoots { names := rootNames } equations claim.target)
      Src.KernelFront.defaultLimits = .ok inp ∧
    inp.env.root = claim.env ∧
    inp.env.bindingAddress = claim.roleTable ∧
    (∃ rootId, inp.program.roots.head? = some (claim.target, rootId)) ∧
    SourceToday (Recheck.Config.forInput { names := rootNames } inp) inp.program srcEval goesWrong ∧
    X86.Exe.Cert.zeroShdr (exe.extract 0 core.size) = core ∧
    (∀ i, core.size ≤ i → i < X86.Exe.alignUp core.size X86.Exe.Cert.certPageSize →
      exe.data[i]? = some X86.Exe.Cert.trapByte) ∧
    ∀ args, ArgsOk args → ∀ s₀, LoadedFile core args s₀ → ∀ σ, Trace core s₀ σ →
      IxCC.Exe.Plain.PlainExeOutcome srcEval goesWrong arity result data args σ

/-- **Today's verifier accepts the file for the claim it carries.** The
certificate, and unless supplied beside the file the environment and the hint
sidecar, are read from the file's own trailer. -/
def AcceptsToday (claim : CompileClaim) (exe : ByteArray) : Prop :=
  ∃ (extEnv? extEq? : Option ByteArray) (v : IxCC.Exe.Cert.VerifiedExe),
    IxCC.Exe.Cert.verifyExeBytes exe extEnv? extEq? Src.KernelFront.defaultLimits = .ok v ∧
    v.exeKind = .plain ∧ v.claim = claim

/-- **What `ixcc verify-exe` establishes today**, from `verifyExeBytes_sound` and the
plain executable theorems. -/
theorem correctToday_of_verifyExeBytes {exe : ByteArray} {extEnv? extEq? : Option ByteArray}
    {v : IxCC.Exe.Cert.VerifiedExe}
    (h : IxCC.Exe.Cert.verifyExeBytes exe extEnv? extEq? Src.KernelFront.defaultLimits = .ok v)
    (hkind : v.exeKind = .plain) : CorrectToday v.claim exe := by
  obtain ⟨payloadBytes, payload, envBytes, equations, certText, inp, tc, cl, a, expectedCore,
    -, -, -, hing, henv, hrole, -, -, -, -, -, -, hvp, -, hcore, hsled, -, -,
    hImmRun, hRcRun, hPlain, -⟩ := IxCC.Exe.Cert.verifyExeBytes_sound h
  obtain ⟨inpExe, ce, hb, hceEq⟩ := hPlain hkind
  subst hceEq
  have htarget := verifyProgram_target hvp
  cases hpol : v.claim.policy with
  | immortal =>
    obtain ⟨cert, -, hrun⟩ := hImmRun (.inl hpol)
    exact ⟨envBytes, equations, v.rootNames, inp, _, _, ce.bytes, inpExe.arity, inpExe.result,
      fileBase + ce.plan.placement.dataOffset, hing, henv, hrole, htarget, .replay hrun, hcore,
      hsled, fun _ hargs _ hload _ hσ =>
        IxCC.Exe.Plain.plain_exe_sound hrun hb hargs
          (LoadedFile.toLoaded (IxCC.X86.Exe.Plain.Certified.checked ce) hload) hσ⟩
  | zeroRc =>
    obtain ⟨cert, -, hrun⟩ := hImmRun (.inr hpol)
    exact ⟨envBytes, equations, v.rootNames, inp, _, _, ce.bytes, inpExe.arity, inpExe.result,
      fileBase + ce.plan.placement.dataOffset, hing, henv, hrole, htarget, .replay hrun, hcore,
      hsled, fun _ hargs _ hload _ hσ =>
        IxCC.Exe.Plain.plain_exe_sound hrun hb hargs
          (LoadedFile.toLoaded (IxCC.X86.Exe.Plain.Certified.checked ce) hload) hσ⟩
  | plainRc =>
    obtain ⟨cert, rcArt, -, hrun, hto⟩ := hRcRun hpol
    exact ⟨envBytes, equations, v.rootNames, inp, _, _, ce.bytes, inpExe.arity, inpExe.result,
      fileBase + ce.plan.placement.dataOffset, hing, henv, hrole, htarget, .rcReplay hrun, hcore,
      hsled, fun _ hargs _ hload _ hσ =>
        IxCC.Exe.Plain.Rc.plain_exe_sound hrun hto hb hargs
          (LoadedFile.toLoaded (IxCC.X86.Exe.Plain.Certified.checked ce) hload) hσ⟩

/-- **The certifying route as it stands**: acceptance by today's verifier gives
`CorrectToday`, for the claim the file carries. -/
theorem correctToday_of_accepts {claim : CompileClaim} {exe : ByteArray}
    (h : AcceptsToday claim exe) : CorrectToday claim exe := by
  obtain ⟨extEnv?, extEq?, v, hv, hkind, rfl⟩ := h
  exact correctToday_of_verifyExeBytes hv hkind

end IxCC.Correct
