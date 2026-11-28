import IxCC.Exe.Machine.Sound
import IxCC.X86.Exe.Machine.Proof.Shell
import IxCC.Backend.Proof.Emit
import IxCC.Recheck.Proof.Parts
import IxCC.Recheck.Proof.Front
import IxCC.Recheck.Rc.Proof.Parts
import IxCC.Recheck.Rc.Proof.Roots
import IxCC.Recheck.Rc.Proof.Exports
import IxCC.Recheck.Rc.Proof.FrontParts

/-!
# The executable theorems (X0-P)

For an object `Recheck.run` (or `RcReplay.run`) made, whose first root
`Exe.machine` accepts, and the executable `Machine.writeChecked` wrote of it,
every finite trace of the process from the loader's post-state, under the
platform's system calls, is one `Process.Outcome` allows for the source's
calls: a prefix of what the source step's iteration does on the same answers,
or of that followed by a resource failure's report; or past the point where
the source step, iterated on the same answers, goes wrong; or the
confinement's refusal.

They compose the shell theorem (`shell_sound`, over the object's calls) with
the session theorem's per-call refinement (`callRefines_at`,
`Rc.callRefines_at`), through two facts about the compiler's output:

- `textSize_eq`: the text the file holds is the object's encoded text (the
  ELF writer's `ELF.Valid`, `Backend.emit_parts`);
- `machine_linkedRoot`: the root `Exe.machine` accepts is the linked object's
  root 0, called with two parameters and read back as a `Nat` (`Rt.lower`
  exports the Cfg exports in order, `lower_roots_fst`).

`machine_exe_unspecified` and `Rc.machine_exe_unspecified` are corollaries of
the statements: the process reaches a state where `Process.Step` promises
nothing (bytes the decoder does not decode that are not a `syscall`, `rip`
outside the file, a condition on an undefined flag) only past the point where
the source step goes wrong.
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process

open IxCC.Exe.Machine (objCallAtOf objCallAt srcCall)

theorem map_fst_zipIdx {α : Type} : ∀ (l : List α) (n : Nat), (l.zipIdx n).map Prod.fst = l
  | [], _ => rfl
  | x :: xs, n => by
    rw [List.zipIdx_cons, List.map_cons, map_fst_zipIdx xs (n + 1)]

/-- `Rt.lower` exports the Cfg program's exports, in order. -/
theorem lower_roots_fst {rc : Rt.Config} {C : Cfg.Program} {l : Rt.Lowered} (h : Rt.lower rc C = .ok l) :
    l.roots.map Prod.fst = C.exports := by
  unfold Rt.lower at h
  cases hm : C.exports.head? with
  | none => simp [hm, throw, throwThe, MonadExceptOf.throw] at h
  | some main =>
    simp only [hm, bind, Except.bind] at h
    cases hr : C.funs.toList.find? (C.size ≤ ·.1) with
    | some p => simp [hr, throw, throwThe, MonadExceptOf.throw] at h
    | none =>
      simp only [hr] at h
      split at h
      · cases h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          simp [List.getElem_zipIdx]

/-- What `Exe.machine` accepts: the first root, of two parameters and a `Nat` result. -/
theorem machine_spec {a : Recheck.Artifact} {r : Recheck.Root} (hm : IxCC.Exe.machine a = .ok r) :
    a.roots.head? = some r ∧ r.params = 2 ∧ ∃ sig, r.ty = some (sig, .nat) := by
  unfold IxCC.Exe.machine at hm
  cases hr : a.roots.head? with
  | none => simp [hr] at hm <;> cases hm
  | some root =>
    simp only [hr] at hm
    by_cases hc : (root.params == 2 && CompileClaim.rootParamsAllNat a.src root && IxCC.Exe.declaredTwo a.src) = true
    · have hp : root.params = 2 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact hc.1.1
      simp only [hc] at hm
      cases hty : root.ty with
      | none => simp [hty] at hm <;> cases hm
      | some st =>
        obtain ⟨sig, ty⟩ := st
        cases ty with
        | nat =>
          simp [hty, pure, Except.pure] at hm
          subst hm
          exact ⟨rfl, hp, sig, hty⟩
        | ind i => simp [hty] at hm <;> cases hm
    · simp [hc] at hm <;> cases hm

/-- The first root of `rootsOf` over the standard rows is the linked object's root 0. -/
theorem head_linkedRoot {rcfg : Recheck.Config} {src : Src.Program} {C : Cfg.Program} {l : Rt.Lowered}
    (hfst : l.roots.map Prod.fst = C.exports) {r : Recheck.Root}
    (hr : (Recheck.rootsOf rcfg src C l
      ((List.range src.roots.length).zip (src.roots.zip (C.exports.zip l.roots)))).head? = some r) :
    (l.roots.zipIdx.map fun (p, i) =>
      ({ symbol := p.2, params := Recheck.cfgParams C p.1,
         ty := (src.roots[i]?).bind fun entry => Recheck.rootTy src C entry.2 } : X86.Linked.Root))[0]? =
      some { symbol := r.symbol, params := r.params, ty := r.ty } := by
  cases hs : src.roots with
  | nil => simp [hs, Recheck.rootsOf] at hr
  | cons s0 srest =>
    cases hl : l.roots with
    | nil => simp [hs, hl, Recheck.rootsOf] at hr
    | cons l0 lrest =>
      cases he : C.exports with
      | nil => rw [hl, he] at hfst; simp at hfst
      | cons e0 erest =>
        rw [hl, he] at hfst
        have h0 : l0.1 = e0 := (List.cons.inj hfst).1
        obtain ⟨addr, cst⟩ := s0
        obtain ⟨fn, sym⟩ := l0
        rw [hs, he, hl, List.length_cons, List.range_succ_eq_map] at hr
        simp only [List.zip_cons_cons, Recheck.rootsOf, List.head?_cons, Option.some.injEq] at hr
        subst hr
        simp only at h0
        subst h0
        rfl

section Immortal
variable {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert} {a : Recheck.Artifact}

/-- The text a machine executable holds is the encoded text of the object it was written for. -/
theorem textSize_of_emit {xl : Xv.LProgram} {bcfg : Backend.Config} {b : Backend.Artifact}
    (hemit : Backend.emit xl bcfg = .ok b) {L : Machine.Layout} {step : String}
    (ce : Machine.Certified L step b.object) : ce.checked.plan.placement.textSize = b.encoded.text.size := by
  obtain ⟨input, he⟩ := Backend.emit_parts hemit
  have ht := he.object.text
  rw [he.encoded] at ht
  obtain ⟨parsed, hp, hsize, -⟩ := (Machine.fileFacts ce.checked).text
  have hpt : ELFRead.text? b.object = some parsed.text := by simp [ELFRead.text?, hp]
  rw [ht] at hpt
  rw [← hsize, ← Option.some.inj hpt]

/-- The file's text is the object's. -/
theorem textSize_eq (h : Recheck.run cfg P c = .ok a) {L : Machine.Layout} {step : String}
    (ce : Machine.Certified L step a.object) :
    ce.checked.plan.placement.textSize = a.backend.encoded.text.size := by
  obtain ⟨-, xv, -, -, hemit, -⟩ := Recheck.run_parts h
  exact textSize_of_emit hemit ce

/-- The root `Exe.machine` accepts is the linked object's root 0. -/
theorem machine_linkedRoot (h : Recheck.run cfg P c = .ok a) {r : Recheck.Root} (hm : IxCC.Exe.machine a = .ok r) :
    ∃ sig, a.linkedRoots[0]? = some { symbol := r.symbol, params := 2, ty := some (sig, .nat) } := by
  obtain ⟨hhead, hp, sig, hty⟩ := machine_spec hm
  obtain ⟨f, hf, hsrc, -, -, -, -, -, hcfg, hlow, hroots⟩ := Recheck.run_runLir h
  have hfst : f.lowered.roots.map Prod.fst = f.cfg.exports := lower_roots_fst (Recheck.runLir_spec hf).2.2.2.2.2.2.2
  rw [hroots] at hhead
  have h0 := head_linkedRoot hfst hhead
  refine ⟨sig, ?_⟩
  rw [← hp, ← hty]
  show (a.lowered.roots.zipIdx.map fun (p, i) =>
    ({ symbol := p.2, params := Recheck.cfgParams a.cfg p.1,
       ty := (a.src.roots[i]?).bind fun entry => Recheck.rootTy a.src a.cfg entry.2 } : X86.Linked.Root))[0]? = _
  rw [hsrc, hcfg, hlow]
  exact h0

/-- **The executable theorem** (immortal and zero-RC objects): for an object
`Recheck.run` made, whose first root `Exe.machine` accepts, and the executable
`Machine.writeChecked` wrote of it, every finite trace of the process from the
loader's post-state, under the platform's system calls, is a prefix of what the
source step's iteration does on the same answers, or of that followed by a
resource failure's report; or it has passed the point where the source step,
iterated on the same answers, goes wrong; or the confinement was refused. -/
theorem machine_exe_sound (h : Recheck.run cfg P c = .ok a) {r : Recheck.Root} (hm : IxCC.Exe.machine a = .ok r)
    {L : Machine.Layout} (ce : Machine.Certified L r.symbol a.object) {args : List (List Nat)} (hargs : ArgsOk args)
    {s₀ : ByteEval.State} (hload : Loaded ce.checked args s₀) {σ : List Sys} (hσ : Trace ce.checked.bytes s₀ σ) :
    Outcome (srcCall a) (fun s e => a.front.GoesWrong (0, [s, e]))
      (fileBase + ce.checked.plan.placement.dataOffset) args σ := by
  obtain ⟨sig, hroot⟩ := machine_linkedRoot h hm
  have hs := shell_sound ce hroot hargs hload hσ
  have hcall : objCallAtOf (linkedOf a.object a.linkedRoots) ce.checked.plan.placement.textSize =
      objCallAt a := by
    rw [textSize_eq h ce]; rfl
  rw [hcall] at hs
  exact Shows.refines (IxCC.Exe.Machine.callRefines_at h (IxCC.Exe.Machine.machine_root hm)) hs

/-- **The process reaches a state where `Process.Step` promises nothing only
past the point where the source goes wrong**: if the process runs from the
loader's post-state, making the system calls `σ`, to a state `Unspecified`
covers (bytes the decoder does not decode that are not a `syscall`, `rip`
outside the file, or a condition on an undefined flag), then `σ` has passed
the system calls of a trace along which the source step's iteration reaches a
call where it goes wrong. A corollary of `machine_exe_sound`: from such a
state the process may make any system call (`Run.other_of_unspecified`), and
`Outcome` allows one the shell never makes only there
(`Outcome.wrong_of_other`). -/
theorem machine_exe_unspecified (h : Recheck.run cfg P c = .ok a) {r : Recheck.Root}
    (hm : IxCC.Exe.machine a = .ok r) {L : Machine.Layout} (ce : Machine.Certified L r.symbol a.object)
    {args : List (List Nat)} (hargs : ArgsOk args) {s₀ : ByteEval.State} (hload : Loaded ce.checked args s₀)
    {σ : List Sys} {s : ByteEval.State} (hr : Run ce.checked.bytes s₀ σ s) (hu : Unspecified ce.checked.bytes s) :
    ∃ t₀ c' ρ₀, IxCC.Exe.Machine.Reaches (srcCall a) (IxCC.Exe.Machine.Config.initial args) t₀ c' ∧
      a.front.GoesWrong (0, [c'.state, c'.event]) ∧ DenotesAll t₀ ρ₀ ∧
      started (fileBase + ce.checked.plan.placement.dataOffset) ++ ρ₀ <+: σ :=
  Outcome.wrong_of_other (machine_exe_sound h hm ce hargs hload (Run.other_of_unspecified hr hu 0))

end Immortal

/-- `toRecheckArtifact`'s artifact: `RcReplay.run`'s levels, object and roots. -/
theorem toRecheck_spec {c : Recheck.RcReplay.Cert} {a : Recheck.RcReplay.Artifact} {a' : Recheck.Artifact}
    (h' : a.toRecheckArtifact c = .ok a') :
    ∃ xv xl, a' =
      { src := a.front.src, checked := a.front.checked, lam := a.front.lam, anf := a.front.anf,
        fir := a.front.fir, own := Own.immortal a.front.fir, cfg := a.front.cfg.base, lowered := a.front.lowered,
        xv, xl, backend := a.backend, roots := a.roots } := by
  unfold Recheck.RcReplay.Artifact.toRecheckArtifact at h'
  simp only [bind, Except.bind, Except.mapError] at h'
  split at h'
  · cases h'
  · split at h'
    · cases h'
    · simp only [pure, Except.pure, Except.ok.injEq] at h'
      exact ⟨_, _, h'.symm⟩

/-- **The executable theorem for plain-RC objects**: the CLI writes the
executable of `RcReplay.run`'s artifact through its `toRecheckArtifact`
projection (same object bytes and roots); the guarantee is the RC session
theorem's. -/
theorem Rc.machine_exe_sound {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.RcReplay.Cert}
    {a : Recheck.RcReplay.Artifact} (h : Recheck.RcReplay.run cfg P c = .ok a) {a' : Recheck.Artifact}
    (h' : a.toRecheckArtifact c = .ok a') {r : Recheck.Root} (hm : IxCC.Exe.machine a' = .ok r)
    {L : Machine.Layout} (ce : Machine.Certified L r.symbol a'.object) {args : List (List Nat)} (hargs : ArgsOk args)
    {s₀ : ByteEval.State} (hload : Loaded ce.checked args s₀) {σ : List Sys} (hσ : Trace ce.checked.bytes s₀ σ) :
    Outcome (IxCC.Exe.Machine.Rc.srcCall a) (fun s e => a.front.GoesWrong (0, [s, e]))
      (fileBase + ce.checked.plan.placement.dataOffset) args σ := by
  obtain ⟨xv', xl', rfl⟩ := toRecheck_spec h'
  obtain ⟨hhead, hp, sig, hty⟩ := machine_spec hm
  have hhead' : a.roots.head? = some r := hhead
  rw [Recheck.RcReplay.run_roots h] at hhead'
  have hfst : a.front.lowered.roots.map Prod.fst = a.front.cfg.base.exports :=
    Recheck.RcReplay.public_roots (Recheck.RcReplay.runFront_native (Recheck.RcReplay.run_parts h).1).2
  have h0 := head_linkedRoot hfst hhead'
  have hroot : a.linkedRoots[0]? = some { symbol := r.symbol, params := 2, ty := some (sig, .nat) } := by
    rw [← hp, ← hty]
    exact h0
  have hs := shell_sound ce hroot hargs hload hσ
  obtain ⟨-, xv, xl, -, -, hemit, -⟩ := Recheck.RcReplay.run_parts h
  have hcall : objCallAtOf (linkedOf a.backend.object a.linkedRoots) ce.checked.plan.placement.textSize =
      IxCC.Exe.Machine.Rc.objCallAt a := by
    rw [textSize_of_emit hemit ce]; rfl
  have hs' : Shows (IxCC.Exe.Machine.Rc.objCallAt a) (fileBase + ce.checked.plan.placement.dataOffset) args σ := by
    rw [← hcall]; exact hs
  have hmr : IxCC.Exe.Machine.MachineRoot a.front.src := IxCC.Exe.Machine.machine_root hm
  exact Shows.refines (IxCC.Exe.Machine.Rc.callRefines_at h hmr) hs'

/-- `machine_exe_unspecified` for plain-RC objects. -/
theorem Rc.machine_exe_unspecified {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.RcReplay.Cert}
    {a : Recheck.RcReplay.Artifact} (h : Recheck.RcReplay.run cfg P c = .ok a) {a' : Recheck.Artifact}
    (h' : a.toRecheckArtifact c = .ok a') {r : Recheck.Root} (hm : IxCC.Exe.machine a' = .ok r)
    {L : Machine.Layout} (ce : Machine.Certified L r.symbol a'.object) {args : List (List Nat)} (hargs : ArgsOk args)
    {s₀ : ByteEval.State} (hload : Loaded ce.checked args s₀) {σ : List Sys} {s : ByteEval.State}
    (hr : Run ce.checked.bytes s₀ σ s) (hu : Unspecified ce.checked.bytes s) :
    ∃ t₀ c' ρ₀, IxCC.Exe.Machine.Reaches (IxCC.Exe.Machine.Rc.srcCall a) (IxCC.Exe.Machine.Config.initial args) t₀ c' ∧
      a.front.GoesWrong (0, [c'.state, c'.event]) ∧ DenotesAll t₀ ρ₀ ∧
      started (fileBase + ce.checked.plan.placement.dataOffset) ++ ρ₀ <+: σ :=
  Outcome.wrong_of_other (Rc.machine_exe_sound h h' hm ce hargs hload (Run.other_of_unspecified hr hu 0))

end IxCC.X86.Exe.Process
