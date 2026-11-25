import IxCC.Compile.Proof
import IxCCCorrect.Today
import IxCCCorrect.Tiers

/-!
# The certified route, as it stands (`IxCCCorrect.Compile`)

`IxCC.Compile.compile` is a pure function of the committed environment's bytes, a
target address and options (`IxCC/IxCC/Compile.lean`). This module states and
proves what one theorem, proved once, says about every output of it today:

    compile_today : Compile.compile envBytes target opts = .ok out →
      out.claim.target = target ∧ out.claim.options = opts ∧
      Binds out.claim out.exe ∧ CompiledToday out.claim envBytes out.exe

`CompiledToday claim envBytes exe` has the shape of `Correct claim envBytes exe`
(`IxCCCorrect.Tiers`): three public arguments, and inside it only the bytes, the
claim's fields and existentially bound witnesses. It is at the strength of
`CorrectToday` (`IxCCCorrect.Today`): safety only, against IxCC's own source
evaluator, with the "source goes wrong" and resource disjuncts. Against the
weaknesses W1 to W7 listed there:

| | `CorrectToday` (the certifying route) | `CompiledToday` (this route) |
| --- | --- | --- |
| W1 | the source semantics is IxCC's evaluator on a program made from a certificate, which is quantified existentially | unchanged in the proposition (`SourceToday` still binds a certificate). On this route nobody supplies it: `Compile.check_sound` names it as the text `compile` returns, a function of the three arguments |
| W2 | the hint sidecar and the root selection are quantified existentially | gone: the hints are derived from the environment and the root is the target (`Compile.ingress` has no other argument) |
| W3 | the `goesWrong` disjunct | unchanged (hook (a) of `Compile.compile`) |
| W4 | the resource disjuncts | unchanged |
| W5 | traces of a core image, related to the shipped file by `zeroShdr` and a page tail | gone for the file `compile` returns: the traces are those of the file itself (`LoadedFile exe`, `FileTrace exe`; `execImage_checked`). It returns for a file with a trailer attached |
| W6 | `arity`, `result`, `data` existential | `arity` and `result` are the claim's; `data` (the address of the shell's data) is still existential |
| W7 | the claim is the one the file carries, the limits are the defaults, the object's digest does not occur | the claim is the function's output, the kernel ran at the claim's limits, and the claim's digest is that of the file (`Binds`) |

Not proved here, though the existing facts give it: that the file's zero-filled
segments are the options' stack and region (`LayoutIs`, the first conjunct of
`Correct`).

The theorem does not read a tier flag: `Compile.Claim` has none, and the corollary
`compile_admits` gives the admission conjunct of `Tier1` and `Tier3` (`Admits`) for
**every** `IxCC.Correct.Claim` that agrees with the output's claim on the root, the
role table and the kernel limits, whatever its `tiers`.

`CertifiedRouteToday` is the predicate on a compile function, as
`CertifiedRoute` is; `compileWith` is `compile` with two further refusals between
its stages (the shape decision and the grounding checks), and every instance of it
meets the predicate (`compileWith_route`), because a check that only refuses cannot
break a statement about what is accepted.
-/

set_option autoImplicit false

namespace IxCC.Correct

open IxCC.X86
open IxCC.X86.Exe
open IxCC.X86.Exe.Process

/-! ## The file the compiler returns is its own executable image -/

theorem extract_all (b : ByteArray) {n : Nat} (h : b.size ≤ n) : b.extract 0 n = b := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  apply Array.ext
  · rw [Array.size_extract]
    change b.data.size ≤ n at h
    omega
  · intro i h1 h2
    rw [Array.getElem_extract]
    simp only [Nat.zero_add]

/-- **A checked core is its own executable image.** Its first program header is the
file itself, mapped at `fileBase`, so what the processor can fetch (`execImage`: the
first `PT_LOAD` to the end of its last page) is the whole file and nothing else:
the file ends where the segment does. A statement about the traces of the checked
bytes is therefore a statement about the process of that file. -/
theorem execImage_checked {f : Frame} {object : ByteArray} (c : Checked f object) :
    execImage c.bytes = c.bytes := by
  obtain ⟨parts, -, -, hf⟩ := c.valid
  obtain ⟨view, hparse, -, hprog⟩ := hf.header
  have h0 : view.programs[0]? =
      some ⟨1, 5, 0, fileBase, fileBase, c.plan.placement.fileSize, c.plan.placement.fileSize, 0x1000⟩ := by
    rw [hprog]
    rfl
  have hle : c.bytes.size ≤ X86.Exe.alignUp c.plan.placement.fileSize 0x1000 := by
    rw [hf.size]
    unfold X86.Exe.alignUp
    omega
  unfold execImage
  simp only [hparse, h0, and_self, ↓reduceIte]
  exact extract_all c.bytes hle

/-! ## Today's source side, for a state machine -/

/-- `SourceToday` for a numeric state machine (`Options.kind = .machine`): the
source's calls are IxCC's evaluator on the two-argument root of a program made from
a certificate the checker accepted. -/
inductive SourceMachineToday (cfg : Recheck.Config) (P : Src.Program) :
    IxCC.Exe.Machine.Call → (Nat → Nat → Prop) → Prop
  /-- The immortal and zero-RC replays. -/
  | replay {c : Recheck.Cert} {a : Recheck.Artifact} (h : Recheck.run cfg P c = .ok a) :
      SourceMachineToday cfg P (IxCC.Exe.Machine.srcCall a) (fun s e => a.front.GoesWrong (0, [s, e]))
  /-- The plain-RC replay. -/
  | rcReplay {c : Recheck.RcReplay.Cert} {a : Recheck.RcReplay.Artifact}
      (h : Recheck.RcReplay.run cfg P c = .ok a) :
      SourceMachineToday cfg P (IxCC.Exe.Machine.Rc.srcCall a)
        (fun s e => a.front.GoesWrong (0, [s, e]))

/-! ## The statement -/

/-- **The claim names this file**: its digest is the BLAKE3 of the file's bytes.
Decidable, and checked by whoever is about to run the file. (For a file that
carries a trailer, `Claim.Binds` of `IxCCCorrect.Claim` reads the digest of the
core under the trailer instead; `binds_packaged` relates the two.) -/
def Binds (claim : Compile.Claim) (exe : ByteArray) : Prop :=
  Ixon.Address.blake3Pure exe = claim.exe

/-- **What the existing theorems establish of the process of a file**, for a
program `P` ingested at configuration `cfg`, by the executable's kind.

* `plain`: there is a source semantics of today's kind for `P` (`SourceToday`) such
  that every finite trace of the file, from every loader state of the file, on
  every invocation, satisfies `Exe.Plain.PlainExeOutcome` against it at the given
  arity and rendering.
* `machine`: the same with `SourceMachineToday` and `Process.Outcome`.

The traces are those of the file's own executable image (`FileTrace`), from the
loader's post-state read off the file's own headers (`LoadedFile`). -/
def ExecutableToday (kind : X86.Exe.Cert.ExeKind) (cfg : Recheck.Config) (P : Src.Program)
    (exe : ByteArray) (arity : Nat) (result : ResultKind) : Prop :=
  match kind with
  | .plain =>
    ∃ (srcEval : List Nat → Option Sem.Obs → Prop) (goesWrong : List Nat → Prop) (data : Nat),
      SourceToday cfg P srcEval goesWrong ∧
      ∀ args, ArgsOk args → ∀ s₀, LoadedFile exe args s₀ → ∀ σ, FileTrace exe s₀ σ →
        IxCC.Exe.Plain.PlainExeOutcome srcEval goesWrong arity result data args σ
  | .machine =>
    ∃ (srcCall : IxCC.Exe.Machine.Call) (goesWrong : Nat → Nat → Prop) (data : Nat),
      SourceMachineToday cfg P srcCall goesWrong ∧
      ∀ args, ArgsOk args → ∀ s₀, LoadedFile exe args s₀ → ∀ σ, FileTrace exe s₀ σ →
        Outcome srcCall goesWrong data args σ

/-- **The source side of every statement about a compiled claim**, with what is
said of the executable left as `X`.

There is an input `inp` that is the compiler's ingress of `envBytes` for the
claim's target at the claim's kernel limits (`Compile.ingress`: no sidecar, no root
selection), such that:

* `envBytes` decodes to an environment with the claim's root and role table that
  the certified kernel accepts at the claim's limits (the body of `Admits`);
* the first root of the ingested program is the claim's target;
* `X cfg inp.program` holds, at the input's configuration or that without the
  producer's inline-round retry (the two differ in the producer's budgets, which
  the checker does not read). -/
def CompiledAs (claim : Compile.Claim) (envBytes : ByteArray)
    (X : Recheck.Config → Src.Program → Prop) : Prop :=
  ∃ (inp : Recheck.Input) (cfg : Recheck.Config),
    Compile.ingress envBytes claim.target claim.options.kernelLimits = .ok inp ∧
    Ixon.V3.decodeAnonymousEnv envBytes = .ok inp.env ∧
    inp.env.root = claim.env ∧
    inp.env.bindingAddress = some claim.roleTable ∧
    Src.KernelFront.accept inp.env claim.options.kernelLimits = .ok inp.kernel.acc ∧
    (∃ rootId, inp.program.roots.head? = some (claim.target, rootId)) ∧
    (cfg = Recheck.Config.forInput {} inp ∨ cfg = (Recheck.Config.forInput {} inp).noRetry) ∧
    X cfg inp.program

/-- **`CompiledToday claim envBytes exe`**: what the existing theorems establish
of a file the compiler returned for a claim, in this library's vocabulary:
`CompiledAs` with `ExecutableToday` of the file at the claim's kind, arity and
rendering. **Every finite trace of the file itself**, from every loader state of
the file, on every invocation, satisfies `Exe.Plain.PlainExeOutcome` (or, for a
state machine, `Process.Outcome`) against a source semantics of today's kind for
the program ingested from `envBytes`.

What it does not say is in the module note (W1, W3, W4, and `data` of W6). -/
def CompiledToday (claim : Compile.Claim) (envBytes exe : ByteArray) : Prop :=
  CompiledAs claim envBytes fun cfg P =>
    ExecutableToday claim.options.kind cfg P exe claim.arity claim.result

/-- **The certified route at today's strength**, as a predicate on a compile
function (compare `CertifiedRoute`): whenever it succeeds, the claim is about that
target and that file, and `CompiledToday` holds. -/
def CertifiedRouteToday {ε : Type}
    (compile : ByteArray → Ixon.Address → Compile.Options → Except ε Compile.Output) : Prop :=
  ∀ envBytes target options out, compile envBytes target options = .ok out →
    out.claim.target = target ∧ out.claim.options = options ∧
    Binds out.claim out.exe ∧ CompiledToday out.claim envBytes out.exe

/-! ## The proof -/

theorem machine_of_build {a : Recheck.Artifact} {L : X86.Exe.Machine.Layout}
    {root : Recheck.Root} {ce : X86.Exe.Machine.Certified L root.symbol a.object}
    (hb : IxCC.Exe.buildMachine a L = .ok ⟨root, ce⟩) : IxCC.Exe.machine a = .ok root := by
  unfold IxCC.Exe.buildMachine at hb
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hb
  cases hmr : IxCC.Exe.machine a with
  | error e => simp [hmr] at hb
  | ok r0 =>
    simp only [hmr] at hb
    split at hb
    · split at hb
      · simp only [Except.ok.injEq, Sigma.mk.injEq] at hb
        rcases hb with ⟨rfl, _⟩
        rfl
      · cases hb
    · cases hb

/-- The plain executable of an artifact the immortal replay made, as a file. -/
theorem plain_file_sound {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {a : Recheck.Artifact} (h : Recheck.run cfg P c = .ok a)
    {layout : Layout} {i : X86.Exe.Input} {ce : X86.Exe.Certified i}
    (hb : IxCC.Exe.build a layout = .ok ⟨i, ce⟩)
    {args : List (List Nat)} (hargs : ArgsOk args) {s₀ : ByteEval.State}
    (hload : LoadedFile ce.bytes args s₀) {σ : List Sys} (hσ : FileTrace ce.bytes s₀ σ) :
    IxCC.Exe.Plain.PlainExeOutcome (IxCC.Exe.Plain.srcPlainEval a.src a.checked a.front.view)
      (fun ns => a.front.GoesWrong (0, ns)) i.arity i.result
      (fileBase + ce.plan.placement.dataOffset) args σ := by
  have he : execImage ce.bytes = ce.bytes := execImage_checked (IxCC.X86.Exe.Plain.Certified.checked ce)
  unfold FileTrace at hσ
  rw [he] at hσ
  exact IxCC.Exe.Plain.plain_exe_sound h hb hargs
    (LoadedFile.toLoaded (IxCC.X86.Exe.Plain.Certified.checked ce) hload) hσ

/-- The plain executable of an artifact the plain-RC replay made, as a file. -/
theorem plain_file_sound_rc {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.RcReplay.Cert} {rc : Recheck.RcReplay.Artifact}
    (h : Recheck.RcReplay.run cfg P c = .ok rc) {a : Recheck.Artifact}
    (hto : rc.toRecheckArtifact c = .ok a)
    {layout : Layout} {i : X86.Exe.Input} {ce : X86.Exe.Certified i}
    (hb : IxCC.Exe.build a layout = .ok ⟨i, ce⟩)
    {args : List (List Nat)} (hargs : ArgsOk args) {s₀ : ByteEval.State}
    (hload : LoadedFile ce.bytes args s₀) {σ : List Sys} (hσ : FileTrace ce.bytes s₀ σ) :
    IxCC.Exe.Plain.PlainExeOutcome
      (IxCC.Exe.Plain.srcPlainEval rc.front.src rc.front.checked rc.front.view)
      (fun ns => rc.front.GoesWrong (0, ns)) i.arity i.result
      (fileBase + ce.plan.placement.dataOffset) args σ := by
  have he : execImage ce.bytes = ce.bytes := execImage_checked (IxCC.X86.Exe.Plain.Certified.checked ce)
  unfold FileTrace at hσ
  rw [he] at hσ
  exact IxCC.Exe.Plain.Rc.plain_exe_sound h hto hb hargs
    (LoadedFile.toLoaded (IxCC.X86.Exe.Plain.Certified.checked ce) hload) hσ

/-- The machine executable of an artifact the immortal replay made, as a file. -/
theorem machine_file_sound {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {a : Recheck.Artifact} (h : Recheck.run cfg P c = .ok a)
    {L : X86.Exe.Machine.Layout} {root : Recheck.Root}
    {ce : X86.Exe.Machine.Certified L root.symbol a.object}
    (hb : IxCC.Exe.buildMachine a L = .ok ⟨root, ce⟩)
    {args : List (List Nat)} (hargs : ArgsOk args) {s₀ : ByteEval.State}
    (hload : LoadedFile ce.checked.bytes args s₀) {σ : List Sys}
    (hσ : FileTrace ce.checked.bytes s₀ σ) :
    Outcome (IxCC.Exe.Machine.srcCall a) (fun s e => a.front.GoesWrong (0, [s, e]))
      (fileBase + ce.checked.plan.placement.dataOffset) args σ := by
  have he : execImage ce.checked.bytes = ce.checked.bytes := execImage_checked ce.checked
  unfold FileTrace at hσ
  rw [he] at hσ
  exact machine_exe_sound h (machine_of_build hb) ce hargs (LoadedFile.toLoaded ce.checked hload) hσ

/-- The machine executable of an artifact the plain-RC replay made, as a file. -/
theorem machine_file_sound_rc {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.RcReplay.Cert} {rc : Recheck.RcReplay.Artifact}
    (h : Recheck.RcReplay.run cfg P c = .ok rc) {a : Recheck.Artifact}
    (hto : rc.toRecheckArtifact c = .ok a)
    {L : X86.Exe.Machine.Layout} {root : Recheck.Root}
    {ce : X86.Exe.Machine.Certified L root.symbol a.object}
    (hb : IxCC.Exe.buildMachine a L = .ok ⟨root, ce⟩)
    {args : List (List Nat)} (hargs : ArgsOk args) {s₀ : ByteEval.State}
    (hload : LoadedFile ce.checked.bytes args s₀) {σ : List Sys}
    (hσ : FileTrace ce.checked.bytes s₀ σ) :
    Outcome (IxCC.Exe.Machine.Rc.srcCall rc) (fun s e => rc.front.GoesWrong (0, [s, e]))
      (fileBase + ce.checked.plan.placement.dataOffset) args σ := by
  have he : execImage ce.checked.bytes = ce.checked.bytes := execImage_checked ce.checked
  unfold FileTrace at hσ
  rw [he] at hσ
  exact Rc.machine_exe_sound h hto (machine_of_build hb) ce hargs
    (LoadedFile.toLoaded ce.checked hload) hσ

/-- **What a checked compile's executable satisfies**: the last conjunct of
`CompiledToday`, from what the checker accepted and the executable `build` wrote. -/
theorem executable_today {cfg : Recheck.Config} {P : Src.Program} {text : String}
    {policy : CompilePolicy} {replay : Compile.Replay}
    (hacc : replay.Accepted cfg P text policy)
    {kind : X86.Exe.Cert.ExeKind} {layout : Layout} {x : Compile.Executable}
    (hx : Compile.executable kind layout replay.artifact = .ok x) :
    ExecutableToday kind cfg P x.bytes x.arity x.result := by
  cases kind with
  | plain =>
    show ∃ (srcEval : List Nat → Option Sem.Obs → Prop) (goesWrong : List Nat → Prop) (data : Nat),
      SourceToday cfg P srcEval goesWrong ∧
      ∀ args, ArgsOk args → ∀ s₀, LoadedFile x.bytes args s₀ → ∀ σ, FileTrace x.bytes s₀ σ →
        IxCC.Exe.Plain.PlainExeOutcome srcEval goesWrong x.arity x.result data args σ
    cases replay with
    | zero cert a =>
      obtain ⟨-, hrun, -⟩ := hacc
      obtain ⟨i, ce, hb, hbytes, harity, hresult⟩ := Compile.executable_plain hx
      refine ⟨_, _, fileBase + ce.plan.placement.dataOffset, .replay hrun, ?_⟩
      intro args hargs s₀ hload σ hσ
      rw [hbytes] at hload hσ
      rw [harity, hresult]
      exact plain_file_sound hrun hb hargs hload hσ
    | plain cert rc a =>
      obtain ⟨-, hrun, hto, -⟩ := hacc
      obtain ⟨i, ce, hb, hbytes, harity, hresult⟩ := Compile.executable_plain hx
      refine ⟨_, _, fileBase + ce.plan.placement.dataOffset, .rcReplay hrun, ?_⟩
      intro args hargs s₀ hload σ hσ
      rw [hbytes] at hload hσ
      rw [harity, hresult]
      exact plain_file_sound_rc hrun hto hb hargs hload hσ
  | machine =>
    show ∃ (srcCall : IxCC.Exe.Machine.Call) (goesWrong : Nat → Nat → Prop) (data : Nat),
      SourceMachineToday cfg P srcCall goesWrong ∧
      ∀ args, ArgsOk args → ∀ s₀, LoadedFile x.bytes args s₀ → ∀ σ, FileTrace x.bytes s₀ σ →
        Outcome srcCall goesWrong data args σ
    cases replay with
    | zero cert a =>
      obtain ⟨-, hrun, -⟩ := hacc
      obtain ⟨root, ce, hb, hbytes, -, -⟩ := Compile.executable_machine hx
      refine ⟨_, _, fileBase + ce.checked.plan.placement.dataOffset, .replay hrun, ?_⟩
      intro args hargs s₀ hload σ hσ
      rw [hbytes] at hload hσ
      exact machine_file_sound hrun hb hargs hload hσ
    | plain cert rc a =>
      obtain ⟨-, hrun, hto, -⟩ := hacc
      obtain ⟨root, ce, hb, hbytes, -, -⟩ := Compile.executable_machine hx
      refine ⟨_, _, fileBase + ce.checked.plan.placement.dataOffset, .rcReplay hrun, ?_⟩
      intro args hargs s₀ hload σ hσ
      rw [hbytes] at hload hσ
      exact machine_file_sound_rc hrun hto hb hargs hload hσ

/-- **From the two stages to a statement about the claim.** If `check` returned `c`
and `build` returned `out` from it, then the claim names the target and the options,
its digest is the returned file's, and `CompiledAs` holds with any `X` that follows,
for the configuration and program of `c`, from what the checker accepted
(`Replay.Accepted`) and the executable `build` wrote for it. Every theorem about a
function made of these two stages goes through here. -/
theorem compiledAs_of_stages {envBytes : ByteArray} {target : Ixon.Address}
    {opts : Compile.Options} {c : Compile.Checked} {out : Compile.Output}
    {X : Recheck.Config → Src.Program → Prop}
    (hcheck : Compile.check envBytes target opts = .ok c)
    (hbuild : Compile.build target opts c = .ok out)
    (hX : ∀ x : Compile.Executable,
      c.replay.Accepted c.cfg c.inp.program c.cert c.policy →
      Compile.executable opts.kind opts.layout c.replay.artifact = .ok x →
      out.exe = x.bytes → out.claim.arity = x.arity → out.claim.result = x.result →
      X c.cfg c.inp.program) :
    out.claim.target = target ∧ out.claim.options = opts ∧
    Binds out.claim out.exe ∧ CompiledAs out.claim envBytes X := by
  obtain ⟨hing, htarget, hrole, hcfg, hacc⟩ := Compile.check_sound hcheck
  obtain ⟨ht, ho, henv, hrt, -, hexe, -, -, x, hx, hbytes, harity, hresult⟩ :=
    Compile.build_spec hbuild
  obtain ⟨hdec, -, haccept, -, -, -⟩ := Compile.ingress_parts hing
  refine ⟨ht, ho, hexe.symm, c.inp, c.cfg, ?_, hdec, henv.symm, ?_, ?_, ?_, hcfg,
    hX x hacc hx hbytes harity hresult⟩
  · rw [ht, ho]; exact hing
  · rw [hrt]; exact hrole
  · rw [ho]; exact haccept
  · rw [ht]; exact htarget

/-- **The theorem of the certified route, at today's strength.** If
`Compile.compile envBytes target opts` returns `out`, then the claim names `target`
and `opts`, the claim's digest is that of the returned file, and `CompiledToday`
holds of the claim, the environment's bytes and the file.

Its proof uses the checker's soundness (`Recheck.sound`, `RcReplay.sound`, through
the executable theorems) and nothing about the producer: `compile` builds the file
from the artifact the checker made for the producer's certificate. -/
theorem compile_today {envBytes : ByteArray} {target : Ixon.Address} {opts : Compile.Options}
    {out : Compile.Output} (h : Compile.compile envBytes target opts = .ok out) :
    out.claim.target = target ∧ out.claim.options = opts ∧
    Binds out.claim out.exe ∧ CompiledToday out.claim envBytes out.exe := by
  obtain ⟨c, hcheck, hbuild⟩ := Compile.compile_parts h
  refine compiledAs_of_stages hcheck hbuild fun x hacc hx hbytes harity hresult => ?_
  show ExecutableToday out.claim.options.kind c.cfg c.inp.program out.exe out.claim.arity
    out.claim.result
  rw [(Compile.build_spec hbuild).2.1, hbytes, harity, hresult]
  exact executable_today hacc hx

/-- `Compile.compile` meets the certified route's predicate at today's strength. -/
theorem compile_route : CertifiedRouteToday Compile.compile :=
  fun _ _ _ _ h => compile_today h

/-! ## Consequences in the target vocabulary -/

/-- **The kernel admits the committed environment, in the sense `Tier1` and `Tier3`
ask** (`Admits`): for every claim of this library that agrees with the compiler's
on the environment's root, the role table and the kernel limits. No tier flag is
read. -/
theorem compile_admits {envBytes : ByteArray} {target : Ixon.Address} {opts : Compile.Options}
    {out : Compile.Output} (h : Compile.compile envBytes target opts = .ok out) (claim : Claim)
    (henv : claim.env = out.claim.env) (hrole : claim.roleTable = out.claim.roleTable)
    (hlimits : claim.kernelLimits = out.claim.options.kernelLimits) :
    ∃ acc, Admits claim envBytes acc := by
  obtain ⟨-, -, -, inp, cfg, -, hdec, hroot, hbind, hacc, -⟩ := compile_today h
  exact ⟨inp.kernel.acc, inp.env, hdec, by rw [henv]; exact hroot, by rw [hrole]; exact hbind,
    by rw [hlimits]; exact hacc⟩

/-- **The digest of the returned file is the digest `Claim.Binds` reads from any
packaging of it.** If `file` is the returned executable with a trailer attached
(`X86.Exe.Cert.checkTrailer`: the certificate of the developer path, or a proof)
and the strict parser reads the returned executable's size as the core's
(`X86.Exe.Cert.extractTrailer`, as `verify-exe` requires), then the core under the
trailer is the returned executable, so its digest is the claim's. -/
theorem binds_packaged {claim : Compile.Claim} {exe : ByteArray} (hb : Binds claim exe)
    {payload file : ByteArray} (hchk : X86.Exe.Cert.checkTrailer exe payload file = true)
    {payload' : ByteArray} (hext : X86.Exe.Cert.extractTrailer file = .ok (exe.size, payload')) :
    (coreOf file).map Ixon.Address.blake3Pure = some claim.exe := by
  unfold coreOf
  rw [hext]
  simp only [Option.map_some]
  rw [X86.Exe.Cert.checkTrailer_core_eq hchk, hb]

/-! ## The function with the two further checks -/

/-- **`compile` with two further checks between its stages**: the shape decision
(hook (a)) and the grounding checks (hook (b)) of `Compile.compile`, each a function
of what `Compile.check` returned that only refuses. The certified route's final
function is this at the two libraries' deciders; it has `compile`'s signature. -/
def compileWith (shape ground : Compile.Checked → Except Recheck.Err Unit)
    (envBytes : ByteArray) (target : Ixon.Address) (opts : Compile.Options) :
    Except Recheck.Err Compile.Output := do
  let c ← Compile.check envBytes target opts
  let () ← shape c
  let () ← ground c
  Compile.build target opts c

/-- A compile `compileWith` accepts is one `compile` accepts, with the same output:
the checks only refuse. -/
theorem compileWith_refines {shape ground : Compile.Checked → Except Recheck.Err Unit}
    {envBytes : ByteArray} {target : Ixon.Address} {opts : Compile.Options} {out : Compile.Output}
    (h : compileWith shape ground envBytes target opts = .ok out) :
    ∃ c, Compile.check envBytes target opts = .ok c ∧ shape c = .ok () ∧ ground c = .ok () ∧
      Compile.compile envBytes target opts = .ok out := by
  unfold compileWith at h
  obtain ⟨c, hc, h⟩ := Compile.bind_ok h
  obtain ⟨_, hs, h⟩ := Compile.bind_ok h
  obtain ⟨_, hg, h⟩ := Compile.bind_ok h
  refine ⟨c, hc, hs, hg, ?_⟩
  unfold Compile.compile
  rw [hc]
  exact h

/-- Every instance of `compileWith` meets the certified route's predicate at today's
strength. A proof lane strengthens the conclusion from what its check establishes
(`compileWith_refines` hands it `shape c = .ok ()` and `ground c = .ok ()`). -/
theorem compileWith_route (shape ground : Compile.Checked → Except Recheck.Err Unit) :
    CertifiedRouteToday (compileWith shape ground) :=
  fun _ _ _ _ h => by
    obtain ⟨_, -, -, -, hc⟩ := compileWith_refines h
    exact compile_today hc

end IxCC.Correct
