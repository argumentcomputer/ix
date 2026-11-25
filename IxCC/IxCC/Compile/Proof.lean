import IxCC.Compile
import IxCC.Compiler.Proof

/-! # What `compile` computed (`IxCC.Compile.Proof`)

The structural theorems about `Compile.compile`: a successful compile is a
successful `check` and `build` (`compile_parts`); `check` returned an input that
is the ingress of the bytes for the target, whose first root is the target, and
a certificate that the proved checker accepted for that input's program, with the
policy it was accepted under (`check_sound`); and `build` returned the executable
`Exe.build` or `Exe.buildMachine` wrote and checked for the artifact the checker
made, with a claim that names the target, the options, the environment's root and
role table, and the digest of exactly those bytes (`build_spec`).

Nothing here is about the producer: every statement is about what the checker
accepted. The semantic theorem, which composes these with the checker's and the
executables' soundness theorems, is `IxCCCorrect.Compile`. -/

set_option autoImplicit false

namespace IxCC.Compile

open IxCC.Recheck

/-! ## Steps -/

theorem bind_ok {α β : Type} {x : Except Err α} {f : α → Except Err β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem mapError_ok {ε α : Type} {f : ε → Err} {x : Except ε α} {a : α}
    (h : x.mapError f = .ok a) : x = .ok a := by
  cases x with
  | error e => cases h
  | ok a' => cases h; rfl

theorem require_ok {c : Bool} {e : Err} (h : require c e = .ok ()) : c = true := by
  cases c with
  | false => cases h
  | true => rfl

theorem orRefuse_ok {α : Type} {e : Err} {o : Option α} {a : α}
    (h : orRefuse e o = .ok a) : o = some a := by
  cases o with
  | none => cases h
  | some a' => cases h; rfl

/-! ## Ingress -/

/-- **What `ingressRoots` computed**: the kernel accepted the environment at the
limits, the mode check passed, the proposals are the ones discovered from the
environment under the admitted table's pins (no other source of hints), and the
program is read against the kernel's reading. -/
theorem ingressRoots_parts {env : Ixon.V3.Env} {chosen : Array (Ixon.Address × Option String)}
    {limits : Ix.Kernel.Admission.Limits} {inp : Input}
    (h : ingressRoots env chosen limits = .ok inp) :
    inp.env = env ∧
    Src.KernelFront.accept env limits = .ok inp.kernel.acc ∧
    Src.KernelFront.defaultModeCheck inp.kernel.acc = .ok () ∧
    inp.hints.proposals =
      Src.AutoHints.discover env (Src.KernelFront.pinsOfTable inp.kernel.acc.table) ∧
    Src.KernelFront.Reading.build inp.kernel.acc inp.program = .ok inp.kernel.rd ∧
    inp.kernel.fe = Ix.Kernel.mkFEnv inp.kernel.acc.env := by
  unfold ingressRoots at h
  obtain ⟨acc, hacc, h⟩ := bind_ok h
  obtain ⟨_, hmode, h⟩ := bind_ok h
  obtain ⟨records, -, h⟩ := bind_ok h
  obtain ⟨p, -, h⟩ := bind_ok h
  obtain ⟨rd, hrd, h⟩ := bind_ok h
  cases h
  exact ⟨rfl, mapError_ok hacc, mapError_ok hmode, rfl, mapError_ok hrd, rfl⟩

/-- **What `ingress` computed**: the bytes decode to the input's environment, the
target is a constant of it, and the rest is `ingressRoots_parts`. -/
theorem ingress_parts {envBytes : ByteArray} {target : Ixon.Address}
    {limits : Ix.Kernel.Admission.Limits} {inp : Input}
    (h : ingress envBytes target limits = .ok inp) :
    Ixon.V3.decodeAnonymousEnv envBytes = .ok inp.env ∧
    inp.env.consts.contains target = true ∧
    Src.KernelFront.accept inp.env limits = .ok inp.kernel.acc ∧
    Src.KernelFront.defaultModeCheck inp.kernel.acc = .ok () ∧
    inp.hints.proposals =
      Src.AutoHints.discover inp.env (Src.KernelFront.pinsOfTable inp.kernel.acc.table) ∧
    Src.KernelFront.Reading.build inp.kernel.acc inp.program = .ok inp.kernel.rd := by
  unfold ingress at h
  obtain ⟨env, henv, h⟩ := bind_ok h
  obtain ⟨_, hmem, h⟩ := bind_ok h
  obtain ⟨he, hacc, hmode, hprop, hrd, -⟩ := ingressRoots_parts h
  subst he
  exact ⟨mapError_ok henv, require_ok hmem, hacc, hmode, hprop, hrd⟩

/-! ## The certificate checker -/

/-- **What the checker accepted, as a proposition.** The certificate is what the
verifier's reader reads from the certificate's file text; its replay at `cfg`
accepted the program `P` and made the artifact; and the policy is one the artifact
supports: a zero-RC-format certificate is claimed `.immortal`, or `.zeroRc` when
the checked program selects zero RC and passes the contract-aware ownership check
(`zeroRcOk`); a plain-RC certificate is claimed `.plainRc`. -/
def Replay.Accepted (cfg : Config) (P : Src.Program) (text : String) (policy : CompilePolicy) :
    Replay → Prop
  | .zero cert a =>
    Recheck.Cert.ofText text = .ok cert ∧ Recheck.run cfg P cert = .ok a ∧
      (policy = .immortal ∨ policy = .zeroRc ∧ zeroRcOk a = true)
  | .plain cert rc a =>
    RcReplay.Cert.ofText text = .ok cert ∧ RcReplay.run cfg P cert = .ok rc ∧
      rc.toRecheckArtifact cert = .ok a ∧ policy = .plainRc

/-- What `certify` guarantees of its result at configuration `cfg`. -/
structure Certified.Sound (cfg : Config) (inp : Input) (c : Certified) : Prop where
  cfg_eq : c.cfg = cfg
  accepted : c.replay.Accepted cfg inp.program c.cert c.policy

theorem checkZero_ok {cfg : Config} {inp : Input} {cert : Recheck.Cert} {a : Recheck.Artifact}
    (h : checkZero cfg inp cert = .ok a) :
    checkCanonicalRelevance cfg inp cert.table cert.relevance = true ∧
    Recheck.run cfg inp.program cert = .ok a ∧
    DefAsserts.checkWithReading inp.kernel.rd a cert = .ok () := by
  unfold checkZero at h
  obtain ⟨_, hrel, h⟩ := bind_ok h
  exact ⟨require_ok hrel, DefAsserts.runWithReading_ok h⟩

theorem checkPlain_ok {cfg : Config} {inp : Input} {cert : RcReplay.Cert}
    {rc : RcReplay.Artifact} {a : Recheck.Artifact}
    (h : checkPlain cfg inp cert = .ok (rc, a)) :
    checkCanonicalRelevance cfg inp cert.base.table cert.base.relevance = true ∧
    RcReplay.run cfg inp.program cert = .ok rc ∧
    DefAsserts.checkRcWithReading inp.kernel.rd rc cert = .ok () ∧
    rc.toRecheckArtifact cert = .ok a := by
  unfold checkPlain at h
  obtain ⟨_, hrel, h⟩ := bind_ok h
  obtain ⟨rc', hrun, h⟩ := bind_ok h
  obtain ⟨a', hto, h⟩ := bind_ok h
  cases h
  obtain ⟨hr, hd⟩ := DefAsserts.runRcWithReading_ok hrun
  exact ⟨require_ok hrel, hr, hd, hto⟩

theorem certifyZero_sound {cfg : Config} {inp : Input} {p : Recheck.Produced}
    {note : Option String} {c : Certified} (h : certifyZero cfg inp p note = .ok c) :
    c.Sound cfg inp := by
  unfold certifyZero at h
  obtain ⟨a, ha, h⟩ := bind_ok h
  cases h
  refine ⟨rfl, p.read, (checkZero_ok ha).2.1, ?_⟩
  show (if zeroRcOk a then CompilePolicy.zeroRc else CompilePolicy.immortal) = .immortal ∨
    (if zeroRcOk a then CompilePolicy.zeroRc else CompilePolicy.immortal) = .zeroRc ∧ zeroRcOk a = true
  cases hz : zeroRcOk a with
  | false => exact .inl rfl
  | true => exact .inr ⟨rfl, rfl⟩

theorem certifyPlain_sound {cfg : Config} {inp : Input} {p : RcReplay.Produced}
    {rc : RcReplay.Artifact} {c : Certified}
    (hrun : RcReplay.run cfg inp.program p.cert = .ok rc)
    (h : certifyPlain cfg inp p rc = .ok c) : c.Sound cfg inp := by
  unfold certifyPlain at h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨a, hto, h⟩ := bind_ok h
  cases h
  exact ⟨rfl, mapError_ok p.read, hrun, hto, rfl⟩

theorem certifyOn_sound {cfg : Config} {inp : Input} {c : Certified}
    (h : certifyOn cfg inp = .ok c) : c.Sound cfg inp := by
  unfold certifyOn at h
  obtain ⟨p, -, h⟩ := bind_ok h
  obtain ⟨⟨rc, a⟩, hchk, h⟩ := bind_ok h
  cases h
  obtain ⟨-, hrun, -, hto⟩ := checkPlain_ok hchk
  exact ⟨rfl, mapError_ok p.read, hrun, hto, rfl⟩

theorem certifyAuto_sound {cfg : Config} {inp : Input} {front : RcReplay.ProducedFir}
    {c : Certified} (h : certifyAuto cfg inp front = .ok c) : c.Sound cfg inp := by
  unfold certifyAuto at h
  split at h
  · obtain ⟨p, -, h⟩ := bind_ok h
    exact certifyZero_sound h
  · split at h
    · rename_i p rc hp
      exact certifyPlain_sound (IxCC.Compiler.producePlain_text hp).2 h
    · obtain ⟨p, -, h⟩ := bind_ok h
      exact certifyZero_sound h

/-- **`certify` returns what the checker accepted**, at the configuration it was
given, under every policy request. -/
theorem certify_sound {rc : Rc} {cfg : Config} {inp : Input} {c : Certified}
    (h : certify rc cfg inp = .ok c) : c.Sound cfg inp := by
  unfold certify at h
  cases rc with
  | off =>
    obtain ⟨p, -, h⟩ := bind_ok h
    exact certifyZero_sound h
  | on => exact certifyOn_sound h
  | auto =>
    obtain ⟨front, -, h⟩ := bind_ok h
    exact certifyAuto_sound h

theorem withRetry_ok {α : Type} {cfg : Config} {attempt : Config → Except Err α} {a : α}
    (h : withRetry cfg attempt = .ok a) : attempt cfg = .ok a ∨ attempt cfg.noRetry = .ok a := by
  unfold withRetry at h
  split at h
  · split at h
    · rename_i a' ha
      cases h
      exact .inl ha
    · exact .inr h
  · exact .inl h

/-! ## The two stages -/

theorem targetIsRoot_ok {inp : Input} {target : Ixon.Address} (h : targetIsRoot inp target = true) :
    ∃ rootId, inp.program.roots.head? = some (target, rootId) := by
  unfold targetIsRoot at h
  cases hhead : inp.program.roots.head? with
  | none => simp [hhead] at h
  | some pair =>
    obtain ⟨a, rootId⟩ := pair
    simp only [hhead] at h
    exact ⟨rootId, by rw [eq_of_beq h]⟩

/-- **What `check` returned.** The input is the ingress of the bytes for the
target at the options' kernel limits; the program's first root is the target; the
environment is role-bound with the returned role table; and the proved checker
accepted the returned certificate text for that input's program, at the input's
configuration or that without the inline-round retry (which differ in the
producer's budgets only), under the returned policy. -/
theorem check_sound {envBytes : ByteArray} {target : Ixon.Address} {opts : Options} {c : Checked}
    (h : check envBytes target opts = .ok c) :
    ingress envBytes target opts.kernelLimits = .ok c.inp ∧
    (∃ rootId, c.inp.program.roots.head? = some (target, rootId)) ∧
    c.inp.env.bindingAddress = some c.roleTable ∧
    (c.cfg = Config.forInput {} c.inp ∨ c.cfg = (Config.forInput {} c.inp).noRetry) ∧
    c.replay.Accepted c.cfg c.inp.program c.cert c.policy := by
  unfold check at h
  obtain ⟨inp, hing, h⟩ := bind_ok h
  obtain ⟨_, htarget, h⟩ := bind_ok h
  obtain ⟨roleTable, hrole, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨cert, hcert, h⟩ := bind_ok h
  cases h
  refine ⟨hing, targetIsRoot_ok (require_ok htarget), orRefuse_ok hrole, ?_⟩
  rcases withRetry_ok hcert with hc | hc
  · have hs := certify_sound hc
    exact ⟨.inl hs.cfg_eq, by rw [hs.cfg_eq]; exact hs.accepted⟩
  · have hs := certify_sound hc
    exact ⟨.inr hs.cfg_eq, by rw [hs.cfg_eq]; exact hs.accepted⟩

theorem executable_plain {layout : X86.Exe.Layout} {a : Recheck.Artifact} {x : Executable}
    (h : executable .plain layout a = .ok x) :
    ∃ (i : X86.Exe.Input) (ce : X86.Exe.Certified i),
      Exe.build a layout = .ok ⟨i, ce⟩ ∧ x.bytes = ce.bytes ∧ x.arity = i.arity ∧ x.result = i.result := by
  unfold executable at h
  simp only at h
  split at h
  · rename_i b hb
    cases h
    obtain ⟨i, ce⟩ := b
    exact ⟨i, ce, hb, rfl, rfl, rfl⟩
  · cases h

theorem executable_machine {layout : X86.Exe.Layout} {a : Recheck.Artifact} {x : Executable}
    (h : executable .machine layout a = .ok x) :
    ∃ (root : Recheck.Root)
      (ce : X86.Exe.Machine.Certified { stack := layout.stack, region := layout.region } root.symbol a.object),
      Exe.buildMachine a { stack := layout.stack, region := layout.region } = .ok ⟨root, ce⟩ ∧
      x.bytes = ce.checked.bytes ∧ x.arity = root.params ∧ x.result = .nat := by
  unfold executable at h
  simp only at h
  split at h
  · rename_i b hb
    cases h
    obtain ⟨root, ce⟩ := b
    exact ⟨root, ce, hb, rfl, rfl, rfl⟩
  · cases h

/-- **What `build` returned.** The claim names the target, the options, the input's
environment root and role table and the checker's policy; its `exe` is the BLAKE3
digest of exactly the returned bytes and its `object` that of the artifact's object;
the certificate text is the one the checker accepted; and the bytes, with the
claim's arity and rendering, are those of the executable written and checked for
the artifact the checker made. -/
theorem build_spec {target : Ixon.Address} {opts : Options} {c : Checked} {out : Output}
    (h : build target opts c = .ok out) :
    out.claim.target = target ∧
    out.claim.options = opts ∧
    out.claim.env = c.inp.env.root ∧
    out.claim.roleTable = c.roleTable ∧
    out.claim.policy = c.policy ∧
    out.claim.exe = Ixon.Address.blake3Pure out.exe ∧
    out.claim.object = Ixon.Address.blake3Pure c.replay.artifact.object ∧
    out.cert = c.cert ∧
    ∃ x, executable opts.kind opts.layout c.replay.artifact = .ok x ∧
      out.exe = x.bytes ∧ out.claim.arity = x.arity ∧ out.claim.result = x.result := by
  unfold build at h
  obtain ⟨x, hx, h⟩ := bind_ok h
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, x, hx, rfl, rfl, rfl⟩

/-- **A successful compile is a successful `check` and `build`.** -/
theorem compile_parts {envBytes : ByteArray} {target : Ixon.Address} {opts : Options} {out : Output}
    (h : compile envBytes target opts = .ok out) :
    ∃ c, check envBytes target opts = .ok c ∧ build target opts c = .ok out := by
  unfold compile at h
  exact bind_ok h

/-- **`compile` is a function**: one output per environment, target and options.
(Every Lean function is; stated because it is the property the claim rests on: the
executable's digest is determined by the other fields of the claim.) -/
theorem compile_deterministic {envBytes : ByteArray} {target : Ixon.Address} {opts : Options}
    {out out' : Output} (h : compile envBytes target opts = .ok out)
    (h' : compile envBytes target opts = .ok out') : out = out' :=
  Except.ok.inj (h.symm.trans h')

end IxCC.Compile
