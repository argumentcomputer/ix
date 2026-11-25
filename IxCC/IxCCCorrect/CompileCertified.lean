import IxCCCorrect.Compile
import IxCCCorrect.ShapeHook
import IxCCCorrect.ShapeTree
import IxCCCorrect.Shape2Produce

/-!
# The certified route's compiler (`IxCCCorrect.CompileCertified`)

```text
compileCertified : (envBytes : ByteArray) → (target : Ixon.Address) → (opts : Compile.Options)
    → Except Decline Compile.Output
```

The final function of the certified route: `IxCC.Compile.compile` (ingress with the
kernel's acceptance, the derived hints, the deterministic producer, the certificate
checker, the seed-closure check, the executable), then the **untrusted shape
producer** (`Shape2.Produce.produceAll`) on the checked source the replay made, then
the **shape decision** of the hook (`IxCCCorrect.ShapeHook`: `certOk` and `rootOk`,
or `natRootOk` on the reference-counted path). Production may not import this library,
so the function is assembled here. It has `compile`'s arguments and output; it only
refuses more (`compileCertified_refines`).

```text
envBytes, target, opts ─Compile.check─→ Checked ─Compile.build─→ Output
  ─Shape2.Produce.produceAll (untrusted) on c.replay.artifact.src─→ shape certificate
  ─certOk, rootOk at the executable's parameter count (proved decision)─→ Output
```

**The theorem** (`compileCertified_sound`): a successful run names the target and the
options, the claim's digest is the returned file's, and `CompiledSound` holds:
`CompiledToday` (`IxCCCorrect.Compile`) **without the "source goes wrong" escape**.
Every finite trace of the returned file, from every loader state of the file, on
every invocation, satisfies `Exe.Plain.PlainExeOutcome` (or, for a state machine,
`Process.Outcome`) with the escape set to `False`: the process prints the value the
source evaluator returns, or reports the shell's own refusals, a resource exhaustion
or a value the view does not read, or stops before printing; it never traps, never
makes a system call outside the shell's four, and never does anything else the
source's "goes wrong" case used to license. That case is empty because the shape
decision accepted: `NeverWrong` of the checked source at every input of the root's
arity (`Shape2.neverWrong_of_check`, `neverWrong_of_enumRoot`,
`rc_neverWrong_of_check`), which is the negation of the front half's `GoesWrong`
(`not_goesWrong_iff`).

**Where the shape decision refuses, the function declines with a typed reason**
(`Decline`): the producer's certificate is larger than `maxShapeInsts` instances, the
certificate does not check (`certOk`), or the root is not a `Nat` root (or, on the
zero-RC-format path, an enumeration root) of the certificate at the executable's
parameter count. A program `compile` refuses is declined with `compile`'s reason.

What is still as in `CompiledToday`: the source semantics is IxCC's evaluator on a
program made from a certificate the checker accepted (W1), the resource disjuncts
(W4), and the address of the shell's data (`data` of W6).

The decision is the hook's own condition: on the zero-RC-format path,
`shapeZero a n = .ok ()` with `Recheck.run cfg P cert = .ok a` is exactly
`ShapeHook.runShaped cfg P cert sc [n] = .ok a` (`runShaped_of_shapeZero`), so
`runShaped_sound` (the object with no escape) holds too; on the plain-RC path, likewise
`rcRunShaped` (`rcRunShaped_of_shapeRc`).
-/

set_option autoImplicit false

namespace IxCC.Correct

open IxCC.X86
open IxCC.X86.Exe
open IxCC.X86.Exe.Process
open IxCC.Correct.Shape2

/-! ## The function -/

/-- The largest shape certificate the decision checks. -/
def maxShapeInsts : Nat := 4000

/-- **Why the certified route declines.** -/
inductive Decline where
  /-- `Compile.compile` refused (ingress, the producer, the certificate checker, the
  seed-closure check, the executable): its reason. -/
  | compile (e : Recheck.Err)
  /-- The shape producer's certificate has more than `maxShapeInsts` instances (the
  producer did not converge on some root); not checked. -/
  | shapeLarge (instances : Nat)
  /-- The shape certificate does not check (`Shape2.certOk` is false). -/
  | shapeCert
  /-- The certificate checks, but root 0 is not a root of it with `params` `Nat`
  parameters and a `Nat` result (or, on the zero-RC-format path, an enumeration
  result every constructor of which the root's view reads back). -/
  | shapeRoot (params : Nat)
  deriving DecidableEq

def Decline.render : Decline → String
  | .compile e => e.render
  | .shapeLarge n => s!"shape: shape.large: the shape producer proposed {n} instances (at most {maxShapeInsts})"
  | .shapeCert => "shape: shape.cert: the shape certificate does not check"
  | .shapeRoot n => s!"shape: shape.root: the root is not a Nat or enumeration root of the shape certificate at {n} parameters"

instance : ToString Decline := ⟨Decline.render⟩

/-- **The shape certificate the untrusted producer proposes** for a checked source's
roots (one table of entries for all of them). Nothing is proved of it. -/
def shapeCertOf (src : Src.Program) : Shape2.Cert :=
  Produce.produceAll src (src.roots.map (·.2))

/-- **The shape decision on what the zero-RC-format replay made**, at `n` parameters:
the producer's certificate checks and root 0 is a `Nat` or enumeration root of it at
`n` parameters (`ShapeHook.rootOk`). -/
def shapeZero (a : Recheck.Artifact) (n : Nat) : Except Decline Unit :=
  let sc := shapeCertOf a.src
  if maxShapeInsts < sc.insts.length then .error (.shapeLarge sc.insts.length)
  else if certOk a.src sc then
    if rootOk a.front sc 0 n then .ok () else .error (.shapeRoot n)
  else .error .shapeCert

/-- **The shape decision on what the plain-RC replay made**, at `n` parameters: the
producer's certificate checks and root 0 is a `Nat` root of it at `n` parameters
(`ShapeHook.natRootOk`; the reference-counted corollaries cover `Nat` results). -/
def shapeRc (a : Recheck.RcReplay.Artifact) (n : Nat) : Except Decline Unit :=
  let sc := shapeCertOf a.front.src
  if maxShapeInsts < sc.insts.length then .error (.shapeLarge sc.insts.length)
  else if certOk a.front.src sc then
    if natRootOk a.front.src sc 0 n then .ok () else .error (.shapeRoot n)
  else .error .shapeCert

/-- The shape decision on what the checker accepted. -/
def shapeDecide : Compile.Replay → Nat → Except Decline Unit
  | .zero _ a, n => shapeZero a n
  | .plain _ rc _, n => shapeRc rc n

/-- The root's parameter count the executable passes it: the root's arity for a plain
executable, two (a state and an event) for a state machine. -/
def paramsOf (kind : X86.Exe.Cert.ExeKind) (arity : Nat) : Nat :=
  match kind with
  | .plain => arity
  | .machine => 2

/-- **The certified route's compiler.** `Compile.check`, `Compile.build`, then the
shape decision on the checked source at the executable's parameter count. -/
def compileCertified (envBytes : ByteArray) (target : Ixon.Address) (opts : Compile.Options) :
    Except Decline Compile.Output := do
  let c ← (Compile.check envBytes target opts).mapError Decline.compile
  let out ← (Compile.build target opts c).mapError Decline.compile
  let () ← shapeDecide c.replay (paramsOf opts.kind out.claim.arity)
  pure out

/-! ## What it computed -/

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem except_mapError_ok {ε ε' α : Type} {f : ε → ε'} {x : Except ε α} {a : α}
    (h : x.mapError f = .ok a) : x = .ok a := by
  cases x with
  | error e => cases h
  | ok a' => cases h; rfl

/-- **A successful run is a successful `check`, `build` and shape decision.** -/
theorem compileCertified_parts {envBytes : ByteArray} {target : Ixon.Address}
    {opts : Compile.Options} {out : Compile.Output}
    (h : compileCertified envBytes target opts = .ok out) :
    ∃ c, Compile.check envBytes target opts = .ok c ∧ Compile.build target opts c = .ok out ∧
      shapeDecide c.replay (paramsOf opts.kind out.claim.arity) = .ok () := by
  unfold compileCertified at h
  obtain ⟨c, hc, h⟩ := except_bind_ok h
  obtain ⟨out', hb, h⟩ := except_bind_ok h
  obtain ⟨⟨⟩, hs, h⟩ := except_bind_ok h
  cases h
  exact ⟨c, except_mapError_ok hc, except_mapError_ok hb, hs⟩

/-- **It only refuses more**: what it returns, `Compile.compile` returns. -/
theorem compileCertified_refines {envBytes : ByteArray} {target : Ixon.Address}
    {opts : Compile.Options} {out : Compile.Output}
    (h : compileCertified envBytes target opts = .ok out) :
    Compile.compile envBytes target opts = .ok out := by
  obtain ⟨c, hc, hb, -⟩ := compileCertified_parts h
  unfold Compile.compile
  rw [hc]
  exact hb

/-- `compile_today` holds of its outputs too. -/
theorem compileCertified_today {envBytes : ByteArray} {target : Ixon.Address}
    {opts : Compile.Options} {out : Compile.Output}
    (h : compileCertified envBytes target opts = .ok out) :
    out.claim.target = target ∧ out.claim.options = opts ∧
    Binds out.claim out.exe ∧ CompiledToday out.claim envBytes out.exe :=
  compile_today (compileCertified_refines h)

/-! ## The shape decision empties the escape -/

/-- What `shapeZero` checked. -/
theorem shapeZero_checks {a : Recheck.Artifact} {n : Nat} (h : shapeZero a n = .ok ()) :
    certOk a.src (shapeCertOf a.src) = true ∧ rootOk a.front (shapeCertOf a.src) 0 n = true := by
  unfold shapeZero at h
  try simp only at h
  split at h
  · cases h
  · split at h
    · rename_i hc
      split at h
      · rename_i hr
        exact ⟨hc, hr⟩
      · cases h
    · cases h

/-- What `shapeRc` checked. -/
theorem shapeRc_checks {a : Recheck.RcReplay.Artifact} {n : Nat} (h : shapeRc a n = .ok ()) :
    certOk a.front.src (shapeCertOf a.front.src) = true ∧
      natRootOk a.front.src (shapeCertOf a.front.src) 0 n = true := by
  unfold shapeRc at h
  try simp only at h
  split at h
  · cases h
  · split at h
    · rename_i hc
      split at h
      · rename_i hr
        exact ⟨hc, hr⟩
      · cases h
    · cases h

/-- **No input of the root's arity goes wrong** (zero-RC-format path): `NeverWrong` of
the front half's source at every `(0, ns)` with `n` arguments, from the hook's two
checks, so the front half's `GoesWrong` is empty there. -/
theorem shapeZero_notWrong {a : Recheck.Artifact} {n : Nat} (h : shapeZero a n = .ok ())
    (ns : List Nat) (hns : ns.length = n) : ¬ a.front.GoesWrong (0, ns) := by
  obtain ⟨hc, hr⟩ := shapeZero_checks h
  rw [← hns] at hr
  apply not_goesWrong_iff.2
  unfold rootOk at hr
  simp only [Bool.or_eq_true] at hr
  rcases hr with hn | hn
  · exact neverWrong_of_check (f := a.front) hc ns hn
  · exact neverWrong_of_enumRoot (f := a.front) hc ns hn

/-- **No input of the root's arity goes wrong** (plain-RC path). -/
theorem shapeRc_notWrong {a : Recheck.RcReplay.Artifact} {n : Nat} (h : shapeRc a n = .ok ())
    (ns : List Nat) (hns : ns.length = n) : ¬ a.front.GoesWrong (0, ns) := by
  obtain ⟨hc, hr⟩ := shapeRc_checks h
  rw [← hns] at hr
  exact rc_not_goesWrong_iff.2 (rc_neverWrong_of_check hc ns hr)

/-- **The decision is the hook's acceptance** (zero-RC-format path): with the replay's
acceptance, `shapeZero` accepting is `ShapeHook.runShaped` accepting at the arities
`[n]`, so `runShaped_sound` holds of the object. -/
theorem runShaped_of_shapeZero {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {a : Recheck.Artifact} (hrun : Recheck.run cfg P c = .ok a) {n : Nat}
    (h : shapeZero a n = .ok ()) : runShaped cfg P c (shapeCertOf a.src) [n] = .ok a := by
  obtain ⟨hc, hr⟩ := shapeZero_checks h
  have hb : (certOk a.src (shapeCertOf a.src) && frontRootsOk a.front (shapeCertOf a.src) 0 [n]) = true := by
    simp only [frontRootsOk, hc, hr, Bool.and_self]
  unfold runShaped
  rw [hrun]
  simp only [hb, ↓reduceIte]

/-- **The decision is the hook's acceptance** (plain-RC path), under any entry map: the
decision admits `Nat` roots only, which the hook's root check accepts whatever the map
(`rcRootOk`'s first disjunct, `natRootOk`). -/
theorem rcRunShaped_of_shapeRc {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.RcReplay.Cert} {a : Recheck.RcReplay.Artifact}
    (hrun : Recheck.RcReplay.run cfg P c = .ok a) {n : Nat} (h : shapeRc a n = .ok ())
    (ms : List (List (Nat × Nat))) :
    rcRunShaped cfg P c (shapeCertOf a.front.src) ms [n] = .ok a := by
  obtain ⟨hc, hr⟩ := shapeRc_checks h
  have hb : rcCheckShaped a (shapeCertOf a.front.src) ms [n] = true := by
    simp only [rcCheckShaped, rcRootsOk, rcRootOk, hc, hr, Bool.true_or, Bool.and_self]
  unfold rcRunShaped
  rw [hrun]
  simp only [hb, ↓reduceIte]

/-! ## The statement -/

/-- `Process.Outcome` without its escape, where the escape is empty. -/
theorem outcome_noWrong {src : IxCC.Exe.Machine.Call} {bad : Nat → Nat → Prop} {data : Nat}
    {args : List (List Nat)} {σ : List Sys} (hb : ∀ s e, ¬ bad s e)
    (h : Outcome src bad data args σ) : Outcome src (fun _ _ => False) data args σ := by
  rcases h with h | h | ⟨_, _, _, _, hbad, _, _⟩ | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact absurd hbad (hb _ _)
  · exact .inr (.inr (.inr h))

/-- **What the certified route establishes of the process of a file**, for a program
`P` ingested at configuration `cfg`, by the executable's kind: `ExecutableToday` with
the source's "goes wrong" set empty at the root's arity, and the outcome stated with
the escape `False`.

* `plain`: a source semantics of today's kind (`SourceToday`) whose "goes wrong" set
  holds of no input of `arity` arguments, and every finite trace of the file, from
  every loader state of the file, on every invocation, satisfies
  `PlainExeOutcome srcEval (fun _ => False)`.
* `machine`: the same with `SourceMachineToday`, no state and event going wrong, and
  `Process.Outcome srcCall (fun _ _ => False)`. -/
def ExecutableSound (kind : X86.Exe.Cert.ExeKind) (cfg : Recheck.Config) (P : Src.Program)
    (exe : ByteArray) (arity : Nat) (result : ResultKind) : Prop :=
  match kind with
  | .plain =>
    ∃ (srcEval : List Nat → Option Sem.Obs → Prop) (goesWrong : List Nat → Prop) (data : Nat),
      SourceToday cfg P srcEval goesWrong ∧ (∀ ns : List Nat, ns.length = arity → ¬ goesWrong ns) ∧
      ∀ args, ArgsOk args → ∀ s₀, LoadedFile exe args s₀ → ∀ σ, FileTrace exe s₀ σ →
        IxCC.Exe.Plain.PlainExeOutcome srcEval (fun _ => False) arity result data args σ
  | .machine =>
    ∃ (srcCall : IxCC.Exe.Machine.Call) (goesWrong : Nat → Nat → Prop) (data : Nat),
      SourceMachineToday cfg P srcCall goesWrong ∧ (∀ s e, ¬ goesWrong s e) ∧
      ∀ args, ArgsOk args → ∀ s₀, LoadedFile exe args s₀ → ∀ σ, FileTrace exe s₀ σ →
        Outcome srcCall (fun _ _ => False) data args σ

/-- **`CompiledSound claim envBytes exe`**: `CompiledAs` (the input is `compile`'s
ingress of `envBytes` for the claim's target at the claim's limits, the kernel accepted
the environment with the claim's root and role table, the program's first root is the
target) with `ExecutableSound` of the file at the claim's kind, arity and rendering. -/
def CompiledSound (claim : Compile.Claim) (envBytes exe : ByteArray) : Prop :=
  CompiledAs claim envBytes fun cfg P =>
    ExecutableSound claim.options.kind cfg P exe claim.arity claim.result

/-- **The certified route's predicate on a compile function, with no escape**:
whenever it succeeds, the claim is about that target and that file, and
`CompiledSound` holds. -/
def CertifiedRouteSound {ε : Type}
    (compile : ByteArray → Ixon.Address → Compile.Options → Except ε Compile.Output) : Prop :=
  ∀ envBytes target options out, compile envBytes target options = .ok out →
    out.claim.target = target ∧ out.claim.options = options ∧
    Binds out.claim out.exe ∧ CompiledSound out.claim envBytes out.exe

/-! ## The proof -/

/-- **What a checked, shaped compile's executable satisfies**: the last conjunct of
`CompiledSound`, from what the checker accepted, the executable `build` wrote, and the
shape decision at the executable's parameter count. -/
theorem executable_sound {cfg : Recheck.Config} {P : Src.Program} {text : String}
    {policy : CompilePolicy} {replay : Compile.Replay}
    (hacc : replay.Accepted cfg P text policy)
    {kind : X86.Exe.Cert.ExeKind} {layout : Layout} {x : Compile.Executable}
    (hx : Compile.executable kind layout replay.artifact = .ok x)
    (hs : shapeDecide replay (paramsOf kind x.arity) = .ok ()) :
    ExecutableSound kind cfg P x.bytes x.arity x.result := by
  cases kind with
  | plain =>
    show ∃ (srcEval : List Nat → Option Sem.Obs → Prop) (goesWrong : List Nat → Prop) (data : Nat),
      SourceToday cfg P srcEval goesWrong ∧ (∀ ns : List Nat, ns.length = x.arity → ¬ goesWrong ns) ∧
      ∀ args, ArgsOk args → ∀ s₀, LoadedFile x.bytes args s₀ → ∀ σ, FileTrace x.bytes s₀ σ →
        IxCC.Exe.Plain.PlainExeOutcome srcEval (fun _ => False) x.arity x.result data args σ
    cases replay with
    | zero cert a =>
      obtain ⟨-, hrun, -⟩ := hacc
      have hw := shapeZero_notWrong (a := a) (n := x.arity) hs
      obtain ⟨i, ce, hb, hbytes, harity, hresult⟩ := Compile.executable_plain hx
      refine ⟨_, _, fileBase + ce.plan.placement.dataOffset, .replay hrun, hw, ?_⟩
      intro args hargs s₀ hload σ hσ
      rw [hbytes] at hload hσ
      rw [harity, hresult]
      rw [harity] at hw
      exact plainExeOutcome_mono (fun ns hlen hg => hw ns hlen hg)
        (plain_file_sound hrun hb hargs hload hσ)
    | plain cert rc a =>
      obtain ⟨-, hrun, hto, -⟩ := hacc
      have hw := shapeRc_notWrong (a := rc) (n := x.arity) hs
      obtain ⟨i, ce, hb, hbytes, harity, hresult⟩ := Compile.executable_plain hx
      refine ⟨_, _, fileBase + ce.plan.placement.dataOffset, .rcReplay hrun, hw, ?_⟩
      intro args hargs s₀ hload σ hσ
      rw [hbytes] at hload hσ
      rw [harity, hresult]
      rw [harity] at hw
      exact plainExeOutcome_mono (fun ns hlen hg => hw ns hlen hg)
        (plain_file_sound_rc hrun hto hb hargs hload hσ)
  | machine =>
    show ∃ (srcCall : IxCC.Exe.Machine.Call) (goesWrong : Nat → Nat → Prop) (data : Nat),
      SourceMachineToday cfg P srcCall goesWrong ∧ (∀ s e, ¬ goesWrong s e) ∧
      ∀ args, ArgsOk args → ∀ s₀, LoadedFile x.bytes args s₀ → ∀ σ, FileTrace x.bytes s₀ σ →
        Outcome srcCall (fun _ _ => False) data args σ
    cases replay with
    | zero cert a =>
      obtain ⟨-, hrun, -⟩ := hacc
      have hw : ∀ s e, ¬ a.front.GoesWrong (0, [s, e]) := fun s e =>
        shapeZero_notWrong (a := a) (n := 2) hs [s, e] rfl
      obtain ⟨root, ce, hb, hbytes, -, -⟩ := Compile.executable_machine hx
      refine ⟨_, _, fileBase + ce.checked.plan.placement.dataOffset, .replay hrun, hw, ?_⟩
      intro args hargs s₀ hload σ hσ
      rw [hbytes] at hload hσ
      exact outcome_noWrong hw (machine_file_sound hrun hb hargs hload hσ)
    | plain cert rc a =>
      obtain ⟨-, hrun, hto, -⟩ := hacc
      have hw : ∀ s e, ¬ rc.front.GoesWrong (0, [s, e]) := fun s e =>
        shapeRc_notWrong (a := rc) (n := 2) hs [s, e] rfl
      obtain ⟨root, ce, hb, hbytes, -, -⟩ := Compile.executable_machine hx
      refine ⟨_, _, fileBase + ce.checked.plan.placement.dataOffset, .rcReplay hrun, hw, ?_⟩
      intro args hargs s₀ hload σ hσ
      rw [hbytes] at hload hσ
      exact outcome_noWrong hw (machine_file_sound_rc hrun hto hb hargs hload hσ)

/-- **The theorem of the certified route, with no escape.** If
`compileCertified envBytes target opts` returns `out`, then the claim names `target`
and `opts`, the claim's digest is that of the returned file, and `CompiledSound`
holds of the claim, the environment's bytes and the file: every finite trace of the
file satisfies the executable's outcome against IxCC's source evaluator on the
program ingested from `envBytes`, with the "source goes wrong" case empty.

Its proof uses the checker's soundness (through the executable theorems), the shape
decision's soundness (`IxCCCorrect.ShapeHook`, `IxCCCorrect.Shape2Check`) and nothing
about either producer. -/
theorem compileCertified_sound {envBytes : ByteArray} {target : Ixon.Address}
    {opts : Compile.Options} {out : Compile.Output}
    (h : compileCertified envBytes target opts = .ok out) :
    out.claim.target = target ∧ out.claim.options = opts ∧
    Binds out.claim out.exe ∧ CompiledSound out.claim envBytes out.exe := by
  obtain ⟨c, hcheck, hbuild, hshape⟩ := compileCertified_parts h
  refine compiledAs_of_stages hcheck hbuild fun x hacc hx hbytes harity hresult => ?_
  show ExecutableSound out.claim.options.kind c.cfg c.inp.program out.exe out.claim.arity
    out.claim.result
  rw [(Compile.build_spec hbuild).2.1, hbytes, harity, hresult]
  rw [harity] at hshape
  exact executable_sound hacc hx hshape

/-- `compileCertified` meets the certified route's predicate with no escape. -/
theorem compileCertified_route : CertifiedRouteSound compileCertified :=
  fun _ _ _ _ h => compileCertified_sound h

/-- **The seed closure was checked** (`KF-4` + `SP-0`): the records the target and the
accepted certificate's table reach are admitted by the certified kernel's logical
entry, under the committed prelude and the committed default role table. -/
theorem compileCertified_seedClosure {envBytes : ByteArray} {target : Ixon.Address}
    {opts : Compile.Options} {out : Compile.Output}
    (h : compileCertified envBytes target opts = .ok out) :
    ∃ c acc, Compile.check envBytes target opts = .ok c ∧
      CompileClaim.checkSeedClosure c.inp target c.replay.table opts.kernelLimits = .ok acc := by
  obtain ⟨c, hcheck, -, -⟩ := compileCertified_parts h
  obtain ⟨acc, hacc⟩ := Compile.check_seedClosure hcheck
  exact ⟨c, acc, hcheck, hacc⟩

end IxCC.Correct
