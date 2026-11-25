import IxCCCorrect.Compose
import IxCCCorrect.Today

/-!
# What the executable prints agrees with the kernel meaning (`IxCCCorrect.ComposeExe`)

The first clause of `Tier1` (standard output is empty, or a prefix of the rendering of an answer
that agrees with the kernel meaning of the claimed address), for the executable image the
existing theorems speak about: the checked core `ce.bytes`, from a loader state of that image.

```lean
plain_exe_tier1Stdout : Recheck.run cfg P c = .ok a → Exe.build a layout = .ok ⟨inp, ce⟩ →
  GroundOk acc a.src (Input.ofProgram a.src a.checked) (a.front.view 0) claim.target claim.abi →
  claim.abi.arity = inp.arity →
  (∀ ns, ns.length = inp.arity → NeverWrong a.front.source (0, ns)) →
  (∀ ns, ns.length = inp.arity → ReturnsCanon a.src ns) →
  Tier1Stdout claim acc ce.bytes
```

and `rc_plain_exe_tier1Stdout` for plain-RC objects.

## How it is made

* **Link O, output shape** (`stdout_of_outcome`): a trace that satisfies `PlainExeOutcome` with no
  escape has written nothing to standard output, or is the confinement followed by a prefix of
  the write of `renderPlain result v` for a `v` the source evaluates to. Every report goes to
  descriptor 2 (`ReportsMsg`), so only the result reaches descriptor 1.
* **The source side** (`agrees_of_srcPlainEval`, `IxCCCorrect.Compose`): that `v` is an answer that
  agrees with the kernel meaning.
* **The image-independent statement** (`tier1Stdout_of_outcome`): the two together, from
  `PlainExeOutcome` alone. Nothing in it mentions an image, a loader state or the processor.

## What the shipped-file link must supply

`Tier1` quantifies over `LoadedFile exe` and `FileTrace exe` (the traces of `execImage exe`); the
theorems here are about `Trace ce.bytes` from `LoadedFile ce.bytes`. The other lane's link is
exactly:

> for the shipped file `exe` whose core is `ce.bytes`: every trace of `execImage exe` from a state
> `LoadedFile exe args s₀` satisfies `PlainExeOutcome srcEval goesWrong inp.arity inp.result D
> args σ` (for the same `srcEval`, `goesWrong`, and any `D`).

With that, `tier1Stdout_of_outcome` gives the first clause of `Tier1 claim envBytes exe` word for
word (after `plainExeOutcome_mono` removes the escape under `NeverWrong`), and `admits_of_ingress`
gives its `Admits`. Nothing about the file is used on this side.

## What is decided, not proved

`claim.abi.arity = inp.arity` is a hypothesis: the claim's parameter count (the root's declared
count, `groundCheck`) is the executable's (`Exe.build`'s root). Both are numbers the caller holds;
`recheck_arity` proves the equation on the immortal and zero-RC path.

The second clause of `Tier1` (a trace that ends with `exit 0` has written the whole rendering) is
not here: it is a further walk of `WriteSeq` (the report statuses are nonzero), of the same kind.
-/

set_option autoImplicit false

namespace IxCC.Correct

open IxCC.X86
open IxCC.X86.Exe
open IxCC.X86.Exe.Process
open IxCC.X86.Exe.Plain
open IxCC.Src (Value Slot Term CId Program Levels)
open IxCC.Sem (Obs Lang Result)
open IxCC.Lam.Erase.Proof (CheckedProgram)

universe u

/-! ## What a trace wrote: prefixes, the confinement, the write loop -/

theorem written_append (fd : Word) : ∀ σ τ : List Sys,
    written fd (σ ++ τ) = written fd σ ++ written fd τ
  | [], τ => rfl
  | e :: σ, τ => by
    cases e <;> simp [written, written_append fd σ τ, List.append_assoc]

theorem written_prefix {fd : Word} {σ τ : List Sys} (h : σ <+: τ) :
    written fd σ <+: written fd τ := by
  obtain ⟨t, rfl⟩ := h
  rw [written_append]
  exact List.prefix_append _ _

/-- The confinement writes nothing. -/
theorem stdout_started (D : Nat) : stdout (started D) = [] := rfl

/-- What a `write` accepted is a prefix of what it was given. -/
theorem accepted_prefix (bytes : List UInt8) (r : Word) : accepted bytes r <+: bytes := by
  unfold accepted
  split
  · exact List.take_prefix _ _
  · exact List.nil_prefix

/-- A write loop on one descriptor writes nothing to another. -/
theorem writeSeq_written_other {fd fd' : Word} (hne : fd ≠ fd') {status : Nat} :
    ∀ {m : List UInt8} {ok : Bool} {ρ : List Sys}, WriteSeq fd status m ok ρ → written fd' ρ = []
  | _, _, _, .done => rfl
  | _, _, _, .step _ _ _ hrest => by
    simp [written, hne, writeSeq_written_other hne hrest]
  | _, _, _, .refused _ _ => by simp [written, hne]

/-- **A write loop writes a prefix of its message** to its descriptor, for a message shorter than
`2 ^ 63` bytes (a `write` result at or above `2 ^ 63` is an error in `accepted`, and a count in
`WriteSeq`: the two readings agree below it). -/
theorem writeSeq_written_prefix {fd : Word} {status : Nat} :
    ∀ {m : List UInt8} {ok : Bool} {ρ : List Sys}, WriteSeq fd status m ok ρ →
      m.length < 2 ^ 63 → written fd ρ <+: m
  | _, _, _, .done, _ => by simp [written]
  | m, _, _, @WriteSeq.step _ _ _ r _ ρ _ _ hle hrest, hlen => by
    have hr : r.toNat < 2 ^ 63 := Nat.lt_of_le_of_lt hle hlen
    have ih := writeSeq_written_prefix hrest (by rw [List.length_drop]; omega)
    have e : written fd (Sys.write fd m r :: ρ) = m.take r.toNat ++ written fd ρ := by
      simp only [written, accepted, hr, ite_true]
    rw [e]
    have h1 := (List.prefix_append_right_inj (m.take r.toNat)).mpr ih
    rwa [List.take_append_drop] at h1
  | m, _, _, @WriteSeq.refused _ _ _ r _ _, _ => by
    have e : written fd [Sys.write fd m r, Sys.exit (UInt64.ofNat writeFailed)] = accepted m r := by
      simp [written]
    rw [e]
    exact accepted_prefix m r

/-- A report goes to descriptor 2: nothing reaches standard output. -/
theorem stdout_reportsMsg {arity : Nat} {m : Message} {ρ : List Sys}
    (h : ReportsMsg arity m ρ) : stdout ρ = [] := by
  obtain ⟨ok, full, hw, hp⟩ := h
  have h1 : written 1 ρ <+: written 1 full := written_prefix hp
  rw [writeSeq_written_other (fd := 2) (fd' := 1) (by decide) hw] at h1
  exact List.prefix_nil.mp h1

/-- A printed result is a prefix of its rendering on standard output. -/
theorem stdout_printsResult {kind : ResultKind} {v : Nat} {ρ : List Sys}
    (h : PrintsResult kind v ρ) (hlen : (renderPlain kind v).length < 2 ^ 63) :
    stdout ρ <+: renderPlain kind v := by
  obtain ⟨ok, full, hw, hp⟩ := h
  exact (written_prefix (fd := 1) hp).trans (writeSeq_written_prefix hw hlen)

/-- A refused confinement writes nothing to standard output. -/
theorem stdout_plainRefused {arity D : Nat} {σ : List Sys} (h : PlainRefused arity D σ) :
    stdout σ = [] := by
  rcases h with ⟨r, ρ, -, hrep, hp⟩ | ⟨r, ρ, -, hrep, hp⟩
  · have h1 : written 1 σ <+: written 1 (Sys.prctl prSetNoNewPrivs 1 r :: ρ) := written_prefix hp
    have e : written 1 (Sys.prctl prSetNoNewPrivs 1 r :: ρ) = stdout ρ := rfl
    rw [e, stdout_reportsMsg hrep] at h1
    exact List.prefix_nil.mp h1
  · have h1 : written 1 σ <+: written 1 (Sys.prctl prSetNoNewPrivs 1 0 ::
        Sys.seccomp seccompSetModeFilter 0 (UInt64.ofNat (fprogAddr D)) r :: ρ) := written_prefix hp
    have e : written 1 (Sys.prctl prSetNoNewPrivs 1 0 ::
        Sys.seccomp seccompSetModeFilter 0 (UInt64.ofNat (fprogAddr D)) r :: ρ) = stdout ρ := rfl
    rw [e, stdout_reportsMsg hrep] at h1
    exact List.prefix_nil.mp h1

/-! ## Link O: the output shape of an outcome with no escape -/

/-- **A trace with no escape wrote nothing to standard output, or printed a source result.**
From `PlainExeOutcome` with the escape removed: standard output is empty, or the arguments parse
at the root's arity, the source evaluates to the observation of some `v`, and the trace is the
confinement followed by a prefix of the write of `v`'s rendering. -/
theorem stdout_of_outcome {srcEval : List Nat → Option Obs → Prop} {arity : Nat}
    {result : ResultKind} {D : Nat} {args : List (List Nat)} {σ : List Sys}
    (h : IxCC.Exe.Plain.PlainExeOutcome srcEval (fun _ => False) arity result D args σ) :
    stdout σ = [] ∨ ∃ ns v ρ, args.length = arity ∧ parseArgsList args = .ok ns ∧
      PlainCallMatches result (.ok (some (IxCC.Exe.Plain.resultObs result v))) (.value v) ∧
      srcEval ns (some (IxCC.Exe.Plain.resultObs result v)) ∧
      σ = started D ++ ρ ∧ PrintsResult result v ρ := by
  have hrep : ∀ {m : Message} {ρ : List Sys}, σ = started D ++ ρ → ReportsMsg arity m ρ →
      stdout σ = [] := by
    intro m ρ heq hr
    have h1 : stdout (started D ++ ρ) = stdout ρ := (written_append 1 (started D) ρ).trans rfl
    rw [heq, h1]
    exact stdout_reportsMsg hr
  rcases h with href | hpre | ⟨ρ, heq, hbody⟩
  · exact .inl (stdout_plainRefused href)
  · refine .inl (List.prefix_nil.mp ?_)
    have h1 : written 1 σ <+: written 1 (started D) := written_prefix hpre
    exact h1
  · rcases hbody with ⟨-, hr⟩ | ⟨hlen, hparse⟩
    · exact .inl (hrep heq hr)
    · cases hp : parseArgsList args with
      | overflow => rw [hp] at hparse; exact .inl (hrep heq hparse)
      | bad => rw [hp] at hparse; exact .inl (hrep heq hparse)
      | ok ns =>
        rw [hp] at hparse
        rcases hparse with ⟨v, hm, hs, hpr⟩ | ⟨o, -, -, hr⟩ | ⟨m, -, hr⟩ | hnil | hfalse
        · exact .inr ⟨ns, v, ρ, hlen, rfl, hm, hs, heq, hpr⟩
        · exact .inl (hrep heq hr)
        · exact .inl (hrep heq hr)
        · refine .inl ?_
          rw [heq, hnil, List.append_nil]
          exact stdout_started D
        · exact hfalse.elim

/-! ## The invocation's arguments -/

theorem parseArg_of_parseArgBytes {a : List Nat} {n : Nat} (h : parseArgBytes a = .ok n) :
    Abi.parseArg a = some n := by
  cases a with
  | nil => simp [parseArgBytes] at h
  | cons b rest =>
    simp only [parseArgBytes] at h
    cases hd : parseDigitsAux 0 (b :: rest) with
    | none => rw [hd] at h; cases h
    | some m =>
      rw [hd] at h
      simp only at h
      split at h
      · cases h
        simp [Abi.parseArg, hd]
      · cases h

/-- Arguments the shell parses are the arguments the claim's convention denotes. -/
theorem mapM_parseArg_of_parseArgsList : ∀ {args : List (List Nat)} {ns : List Nat},
    parseArgsList args = .ok ns → args.mapM Abi.parseArg = some ns
  | [], ns, h => by
    simp only [parseArgsList, ParseArgsResult.ok.injEq] at h
    subst h
    simp
  | a :: rest, ns, h => by
    simp only [parseArgsList] at h
    cases ha : parseArgBytes a with
    | overflow => rw [ha] at h; cases h
    | bad => rw [ha] at h; cases h
    | ok n =>
      rw [ha] at h
      simp only at h
      cases hr : parseArgsList rest with
      | overflow => rw [hr] at h; cases h
      | bad => rw [hr] at h; cases h
      | ok ms =>
        rw [hr] at h
        simp only [ParseArgsResult.ok.injEq] at h
        subst h
        simp [List.mapM_cons, parseArg_of_parseArgBytes ha, mapM_parseArg_of_parseArgsList hr]

theorem abi_parse_of_parseArgsList {abi : Abi} {args : List (List Nat)} {ns : List Nat}
    (hlen : args.length = abi.arity) (h : parseArgsList args = .ok ns) :
    abi.parse args = some ns := by
  simp [Abi.parse, hlen, mapM_parseArg_of_parseArgsList h]

/-! ## The answer's index is small -/

/-- An answer that agrees at an enumeration result is an index into the claim's list, which the
check bounds. -/
theorem answer_lt_of_agrees {claim : Claim} {acc : Src.KernelFront.Accepted} {src : Src.Program}
    {I : Lam.Erase.Input} {view : View}
    (hok : GroundOk acc src I view claim.target claim.abi) {xs : List Nat} {answer : Nat}
    (hag : Agrees.{u} claim acc xs answer) {cs : List Ixon.Address}
    (hr : claim.abi.result = ResTy.enum cs) : answer < 2 ^ 63 := by
  obtain ⟨κ, lpsOf, ann, Sl, Inst, root, res, -, -, -, -, -, hRes⟩ := hok
  cases res with
  | nat =>
    have h1 : claim.abi.result = ResTy.nat := hRes
    rw [hr] at h1
    cases h1
  | enum D =>
    obtain ⟨addrs, hr', hlt, -⟩ := hRes
    rw [hr] at hr'
    have hcs : addrs = cs := by cases hr'; rfl
    rw [hcs] at hlt
    unfold Agrees at hag
    obtain ⟨target, out, -, hterm, -⟩ := hag
    simp only [answerTerm, hr] at hterm
    cases hget : cs[answer]? with
    | none => rw [hget] at hterm; cases hterm
    | some a =>
      obtain ⟨h2, -⟩ := List.getElem?_eq_some_iff.mp hget
      omega

/-! ## The first clause of `Tier1`, from an outcome -/

/-- **The first clause of `Tier1` at one invocation and one trace**: standard output is empty, or a
prefix of the rendering of an answer to the arguments the invocation denotes, which agrees with
the kernel meaning of the claim's target. -/
def Tier1StdoutAt.{w} (claim : Claim) (acc : Src.KernelFront.Accepted) (args : List (List Nat))
    (σ : List Sys) : Prop :=
  stdout σ = [] ∨
    ∃ xs answer, claim.abi.parse args = some xs ∧
      stdout σ <+: claim.abi.render answer ∧ Agrees.{w} claim acc xs answer

/-- **The first clause of `Tier1` over an image**: at every invocation, every loader state of the
image and every finite trace of it. -/
def Tier1Stdout.{w} (claim : Claim) (acc : Src.KernelFront.Accepted) (image : ByteArray) : Prop :=
  ∀ args, ArgsOk args → ∀ s₀, LoadedFile image args s₀ → ∀ σ, Trace image s₀ σ →
    Tier1StdoutAt.{w} claim acc args σ

/-- **From an outcome to the first clause of `Tier1`** (image-independent). A trace that satisfies
`PlainExeOutcome` with no escape against the checked source of a program `groundCheck` accepted,
at the claim's arity, with SrcEval returning canonical forms: what it wrote to standard output is
empty or a prefix of the rendering of an agreeing answer. This is the statement the shipped-file
link feeds: it mentions no image. -/
theorem tier1Stdout_of_outcome {claim : Claim} {acc : Src.KernelFront.Accepted} {src : Src.Program}
    {checked : Src.Relevance.Checked} {view : Nat → Option Obs → Option (Option Obs)}
    (hok : GroundOk acc src (Lam.Erase.Input.ofProgram src checked) (view 0) claim.target
      claim.abi)
    (hnat : ViewNat (view 0)) {arity : Nat} (harity : claim.abi.arity = arity)
    (hcanon : ∀ ns : List Nat, ns.length = arity → ReturnsCanon src ns)
    {result : ResultKind} {D : Nat} {args : List (List Nat)} {σ : List Sys}
    (h : IxCC.Exe.Plain.PlainExeOutcome (IxCC.Exe.Plain.srcPlainEval src checked view)
      (fun _ => False) arity result D args σ) :
    Tier1StdoutAt.{u} claim acc args σ := by
  unfold Tier1StdoutAt
  rcases stdout_of_outcome h with h0 | ⟨ns, v, ρ, hlen, hparse, hmatch, hsrc, rfl, hprint⟩
  · exact Or.inl h0
  · have hns : ns.length = arity := (parseArgsList_ok_length hparse).trans hlen
    obtain ⟨answer, hobs, hag⟩ :=
      agrees_of_srcPlainEval.{u} hok hnat (hns.trans harity.symm) (hcanon ns hns) hsrc
    refine Or.inr ⟨ns, answer, abi_parse_of_parseArgsList (hlen.trans harity.symm) hparse, ?_, hag⟩
    have hout : stdout (started D ++ ρ) = stdout ρ := (written_append 1 (started D) ρ).trans rfl
    rw [hout]
    cases result with
    | nat =>
      cases hr : claim.abi.result with
      | nat =>
        simp only [IxCC.Exe.Plain.resultObs, abiObs, hr, Obs.nat.injEq] at hobs
        subst hobs
        have hv : v < 2 ^ 63 := (show _ ∧ v < 2 ^ 63 from hmatch).2
        have hl := (natDecimal_length_le v hv).2
        have e : claim.abi.render v = renderPlain .nat v := by
          simp [Abi.render, Abi.resultKind, hr]
        rw [e]
        exact stdout_printsResult hprint (by simp [renderPlain]; omega)
      | enum cs =>
        simp [IxCC.Exe.Plain.resultObs, abiObs, hr] at hobs
    | enum n =>
      cases hr : claim.abi.result with
      | nat =>
        simp [IxCC.Exe.Plain.resultObs, abiObs, hr] at hobs
      | enum cs =>
        have hlt := answer_lt_of_agrees hok hag hr
        simp only [IxCC.Exe.Plain.resultObs, abiObs, hr, Obs.ctor.injEq, and_true] at hobs
        subst hobs
        have hl := (natDecimal_length_le v hlt).2
        have e : claim.abi.render v = renderPlain (.enum n) v := by
          simp [Abi.render, Abi.resultKind, hr, renderPlain]
        rw [e]
        exact stdout_printsResult hprint (by simp [renderPlain]; omega)

/-! ## The claim's arity is the executable's -/

/-- **The claim's parameter count is the executable's** (immortal and zero-RC objects): the root
`Exe.build` takes its arity from is the artifact's first root, whose constant is the one
`groundCheck` read the declared count of, and `rootParamsAllNat` compares the two counts. -/
theorem recheck_arity {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {a : Recheck.Artifact} (h : Recheck.run cfg P c = .ok a)
    {layout : X86.Exe.Layout} {inp : X86.Exe.Input} {ce : X86.Exe.Certified inp}
    (hb : IxCC.Exe.build a layout = .ok ⟨inp, ce⟩)
    {claim : Claim} {acc : Src.KernelFront.Accepted} {I : Lam.Erase.Input} {view : View}
    (hok : GroundOk acc a.src I view claim.target claim.abi) :
    claim.abi.arity = inp.arity := by
  obtain ⟨r, hf, hinp⟩ := IxCC.Exe.Plain.build_spec hb
  obtain ⟨hahead, -, hnat, -⟩ := IxCC.Exe.Plain.fragment_spec hf
  obtain ⟨f, -, hsrc, -, -, -, -, -, -, -, hroots⟩ := Recheck.run_runLir h
  rw [hroots, List.head?_eq_getElem?] at hahead
  obtain ⟨j, addr, fx, fn, sym, hrow, -⟩ := Recheck.rootsOf_get_const hahead
  simp only [List.getElem?_zip_eq_some] at hrow
  obtain ⟨-, hsrc0, -⟩ := hrow
  obtain ⟨κ, lpsOf, ann, Sl, Inst, root, res, hroot, -, -, hparams, -, -⟩ := hok
  rw [hsrc, List.head?_eq_getElem?, hsrc0] at hroot
  simp only [Option.some.injEq, Prod.mk.injEq] at hroot
  obtain ⟨-, hrc⟩ := hroot
  subst hrc
  have harity : inp.arity = r.params := by rw [hinp]
  rw [harity]
  unfold CompileClaim.rootParamsAllNat at hnat
  cases hd : a.src.decl? r.const with
  | none => rw [hd] at hnat; cases hnat
  | some d =>
    rw [hd] at hnat
    simp only [Bool.and_eq_true, beq_iff_eq] at hnat
    simp [Abi.arity, hparams, arityOf, hd, hnat.1.2]

/-! ## The executable theorems -/

/-- **What the plain executable prints agrees with the kernel meaning** (immortal and zero-RC
objects), at one invocation and one trace of the checked core. -/
theorem plain_exe_agrees {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {a : Recheck.Artifact} (h : Recheck.run cfg P c = .ok a)
    {layout : X86.Exe.Layout} {inp : X86.Exe.Input} {ce : X86.Exe.Certified inp}
    (hb : IxCC.Exe.build a layout = .ok ⟨inp, ce⟩)
    {claim : Claim} {acc : Src.KernelFront.Accepted}
    (hok : GroundOk acc a.src (Lam.Erase.Input.ofProgram a.src a.checked) (a.front.view 0)
      claim.target claim.abi)
    (harity : claim.abi.arity = inp.arity)
    (hp : ∀ ns : List Nat, ns.length = inp.arity → NeverWrong a.front.source (0, ns))
    (hcanon : ∀ ns : List Nat, ns.length = inp.arity → ReturnsCanon a.src ns)
    {args : List (List Nat)} (hargs : ArgsOk args)
    {s₀ : ByteEval.State} (hload : Loaded (IxCC.X86.Exe.Plain.Certified.checked ce) args s₀)
    {σ : List Sys} (hσ : Trace ce.bytes s₀ σ) :
    Tier1StdoutAt.{u} claim acc args σ :=
  tier1Stdout_of_outcome (view := a.front.view) hok (viewNat_viewOf _ _ 0) harity hcanon
    (plain_exe_sound_of_neverWrong h hb hp hargs hload hσ)

/-- **The first clause of `Tier1` for the checked core** (immortal and zero-RC objects): over every
invocation, every loader state of the core image read off its own headers, and every finite
trace. -/
theorem plain_exe_tier1Stdout {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {a : Recheck.Artifact} (h : Recheck.run cfg P c = .ok a)
    {layout : X86.Exe.Layout} {inp : X86.Exe.Input} {ce : X86.Exe.Certified inp}
    (hb : IxCC.Exe.build a layout = .ok ⟨inp, ce⟩)
    {claim : Claim} {acc : Src.KernelFront.Accepted}
    (hok : GroundOk acc a.src (Lam.Erase.Input.ofProgram a.src a.checked) (a.front.view 0)
      claim.target claim.abi)
    (harity : claim.abi.arity = inp.arity)
    (hp : ∀ ns : List Nat, ns.length = inp.arity → NeverWrong a.front.source (0, ns))
    (hcanon : ∀ ns : List Nat, ns.length = inp.arity → ReturnsCanon a.src ns) :
    Tier1Stdout.{u} claim acc ce.bytes :=
  fun _ hargs _ hload _ hσ =>
    plain_exe_agrees h hb hok harity hp hcanon hargs
      (LoadedFile.toLoaded (IxCC.X86.Exe.Plain.Certified.checked ce) hload) hσ

/-- **What the plain executable prints agrees with the kernel meaning** (plain-RC objects). -/
theorem rc_plain_exe_agrees {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.RcReplay.Cert} {a : Recheck.RcReplay.Artifact}
    (h : Recheck.RcReplay.run cfg P c = .ok a)
    {a' : Recheck.Artifact} (h' : a.toRecheckArtifact c = .ok a')
    {layout : X86.Exe.Layout} {inp : X86.Exe.Input} {ce : X86.Exe.Certified inp}
    (hb : IxCC.Exe.build a' layout = .ok ⟨inp, ce⟩)
    {claim : Claim} {acc : Src.KernelFront.Accepted}
    (hok : GroundOk acc a.front.src (Lam.Erase.Input.ofProgram a.front.src a.front.checked)
      (a.front.view 0) claim.target claim.abi)
    (harity : claim.abi.arity = inp.arity)
    (hp : ∀ ns : List Nat, ns.length = inp.arity → NeverWrong a.front.source (0, ns))
    (hcanon : ∀ ns : List Nat, ns.length = inp.arity → ReturnsCanon a.front.src ns)
    {args : List (List Nat)} (hargs : ArgsOk args)
    {s₀ : ByteEval.State} (hload : Loaded (IxCC.X86.Exe.Plain.Certified.checked ce) args s₀)
    {σ : List Sys} (hσ : Trace ce.bytes s₀ σ) :
    Tier1StdoutAt.{u} claim acc args σ :=
  tier1Stdout_of_outcome (view := a.front.view) hok (viewNat_treeViewOf _ _ 0) harity hcanon
    (rc_plain_exe_sound_of_neverWrong h h' hb hp hargs hload hσ)

/-- **The first clause of `Tier1` for the checked core** (plain-RC objects). -/
theorem rc_plain_exe_tier1Stdout {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.RcReplay.Cert} {a : Recheck.RcReplay.Artifact}
    (h : Recheck.RcReplay.run cfg P c = .ok a)
    {a' : Recheck.Artifact} (h' : a.toRecheckArtifact c = .ok a')
    {layout : X86.Exe.Layout} {inp : X86.Exe.Input} {ce : X86.Exe.Certified inp}
    (hb : IxCC.Exe.build a' layout = .ok ⟨inp, ce⟩)
    {claim : Claim} {acc : Src.KernelFront.Accepted}
    (hok : GroundOk acc a.front.src (Lam.Erase.Input.ofProgram a.front.src a.front.checked)
      (a.front.view 0) claim.target claim.abi)
    (harity : claim.abi.arity = inp.arity)
    (hp : ∀ ns : List Nat, ns.length = inp.arity → NeverWrong a.front.source (0, ns))
    (hcanon : ∀ ns : List Nat, ns.length = inp.arity → ReturnsCanon a.front.src ns) :
    Tier1Stdout.{u} claim acc ce.bytes :=
  fun _ hargs _ hload _ hσ =>
    rc_plain_exe_agrees h h' hb hok harity hp hcanon hargs
      (LoadedFile.toLoaded (IxCC.X86.Exe.Plain.Certified.checked ce) hload) hσ

end IxCC.Correct
