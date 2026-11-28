import IxCC.Exe.Machine.Exe
import IxCC.Exe.Cert.Proof
import IxCC.X86.Exe.Plain.Proof.Shell

/-! # End-to-End Plain Executable & Certified-Executable Theorems

Composes the plain `--exe` shell theorem (`X86.Exe.Plain.plain_shell_sound` /
`plain_shell_unspecified`) with the per-call compiler refinement theorems
(`Recheck.sound_at` for immortal & zero-RC, `Recheck.RcReplay.sound_at` for
plain RC), and lifts `Exe.Cert.verifyExeBytes_sound` all the way to x86-64
process execution for BOTH plain `--exe` (`verifyExeBytes_plain_sound`) and
`--exe --machine` (`verifyExeBytes_machine_sound`):

- `plain_exe_sound`, `plain_exe_unspecified`
- `Rc.plain_exe_sound`, `Rc.plain_exe_unspecified`
- `verifyExeBytes_plain_sound`, `verifyExeBytes_machine_sound`

This retires the unproved `x86-linux-exe-shell` trust entry and bridges the
`.o` vs. runnable certified `f.x86` gap (`BE-1`, `BE-2`, `BE-3`, `KF-4`, `N5`). -/

set_option autoImplicit false

namespace IxCC.Exe.Plain

open IxCC.X86
open IxCC.X86.Exe
open IxCC.X86.Exe.Process
open IxCC.X86.Exe.Plain
open IxCC.Sem (Result Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)

/-! ## Fragment & Builder Specs -/

/-- What `Exe.fragment` ensures about the first root and its result kind. -/
theorem fragment_spec {a : Recheck.Artifact} {r : Recheck.Root} {result : ResultKind}
    (hf : Exe.fragment a = .ok (r, result)) :
    a.roots.head? = some r ∧
    r.params ≤ Recheck.maxParams ∧
    CompileClaim.rootParamsAllNat a.src r = true ∧
    match (generalizing := false) result with
    | .nat => ∃ sig, r.ty = some (sig, .nat)
    | .enum n => ∃ sig idx ctors, r.ty = some (sig, .ind idx) ∧
        sig.inds[idx]? = some ctors ∧ ctors.length = n ∧ ctors.all List.isEmpty = true := by
  unfold Exe.fragment at hf
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hf
  cases hr : a.roots.head? with
  | none => simp [hr] at hf
  | some root =>
    simp only [hr] at hf
    split at hf
    · rename_i hpar
      split at hf
      · rename_i hnat
        cases hty : root.ty with
        | none => simp [hty] at hf
        | some st =>
          rcases st with ⟨sig, ty⟩
          cases ty with
          | nat =>
            simp only [hty, Except.ok.injEq, Prod.mk.injEq] at hf
            rcases hf with ⟨rfl, rfl⟩
            exact ⟨rfl, hpar, hnat, sig, hty⟩
          | ind idx =>
            simp only [hty] at hf
            split at hf
            · rename_i himm
              simp only [Except.ok.injEq, Prod.mk.injEq] at hf
              rcases hf with ⟨rfl, rfl⟩
              unfold CompileClaim.isImmortalViewType at himm
              cases hind : sig.inds[idx]? with
              | none => simp [hind] at himm
              | some ctors =>
                simp only [hind, Bool.and_eq_true] at himm
                exact ⟨rfl, hpar, hnat, sig, idx, ctors, hty, hind, by simp, himm.2⟩
            · cases hf
      · cases hf
    · cases hf

/-- What `Exe.build` ensures about `input` and `ce`. -/
theorem build_spec {a : Recheck.Artifact} {layout : Layout}
    {inp : X86.Exe.Input} {ce : X86.Exe.Certified inp}
    (hb : Exe.build a layout = .ok ⟨inp, ce⟩) :
    ∃ r, Exe.fragment a = .ok (r, inp.result) ∧
      inp = { object := a.object, root := r.symbol, arity := r.params, result := inp.result, layout } := by
  unfold Exe.build Exe.input at hb
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hb
  cases hf : Exe.fragment a with
  | error e => simp [hf] at hb
  | ok pair =>
    rcases pair with ⟨r, res⟩
    simp only [hf] at hb
    cases hchk : layout.check with
    | false => simp [hchk] at hb
    | true =>
      simp only [hchk, ↓reduceIte] at hb
      split at hb
      · simp only [Except.ok.injEq, Sigma.mk.injEq] at hb
        rcases hb with ⟨h1, _⟩
        subst h1
        exact ⟨r, rfl, rfl⟩
      · cases hb

/-- The text size embedded in a plain `Certified` executable equals the encoded
text size of the backend artifact. -/
theorem plain_textSize_of_emit {xl : Xv.LProgram} {bcfg : Backend.Config} {b : Backend.Artifact}
    (hemit : Backend.emit xl bcfg = .ok b) {inp : X86.Exe.Input}
    (hobj : inp.object = b.object) (ce : X86.Exe.Certified inp) :
    ce.plan.placement.textSize = b.encoded.text.size := by
  obtain ⟨input, he⟩ := Backend.emit_parts hemit
  have ht := he.object.text
  rw [he.encoded] at ht
  obtain ⟨parsed, hp, hsize, -⟩ := (plainFileFacts ce).text
  have hpt : ELFRead.text? b.object = some parsed.text := by simp [ELFRead.text?, ← hobj, hp]
  rw [ht] at hpt
  rw [← hsize, ← Option.some.inj hpt]

/-- The first root accepted by `Exe.fragment` is root 0 of `a.linkedRoots`. -/
theorem plain_linkedRoot {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {a : Recheck.Artifact} (h : Recheck.run cfg P c = .ok a)
    {r : Recheck.Root} {result : ResultKind} (hf : Exe.fragment a = .ok (r, result)) :
    a.linkedRoots[0]? = some { symbol := r.symbol, params := r.params, ty := r.ty } := by
  obtain ⟨hhead, -, -, -⟩ := fragment_spec hf
  obtain ⟨f, hfl, hsrc, -, -, -, -, -, hcfg, hlow, hroots⟩ := Recheck.run_runLir h
  have hfst : f.lowered.roots.map Prod.fst = f.cfg.exports :=
    lower_roots_fst (Recheck.runLir_spec hfl).2.2.2.2.2.2.2
  rw [hroots] at hhead
  have h0 := head_linkedRoot hfst hhead
  show (a.lowered.roots.zipIdx.map fun (p, i) =>
    ({ symbol := p.2, params := Recheck.cfgParams a.cfg p.1,
       ty := (a.src.roots[i]?).bind fun entry => Recheck.rootTy a.src a.cfg entry.2 } : X86.Linked.Root))[0]? = _
  rw [hsrc, hcfg, hlow]
  exact h0

/-! ## Source-level observable outcome for plain `--exe` -/

/-- Source evaluation of root 0 on `ns`, viewed through `view`. -/
def srcPlainEval (src : Src.Program) (checked : Src.Relevance.Checked)
    (view : Nat → Option Obs → Option (Option Obs))
    (ns : List Nat) (o : Option Obs) : Prop :=
  ∃ k v, Lang.run (⟨src, checked⟩ : CheckedProgram) (0, ns) k = .ok v ∧
    view 0 (Lang.obs v) = some o

/-- The observation printed for `(result, v)`. -/
def resultObs (result : ResultKind) (v : Nat) : Obs :=
  match result with
  | .nat => .nat v
  | .enum _ => .ctor v []

/-- **Source-level observable outcome of a plain `--exe` process**:
every finite system-call trace `σ` from `Process.Loaded` is either:
- a confinement refusal (`PlainRefused`),
- a prefix of `started D` (stopped during confinement), or
- `started D ++ ρ` where:
  - wrong argument count (`args.length ≠ arity ∨ args = []`) → `ReportsMsg arity .count ρ`;
  - valid count & `parseArgsList args = .overflow` → `ReportsMsg arity .natOverflow ρ`;
  - valid count & `parseArgsList args = .bad` → `ReportsMsg arity .numeral ρ`;
  - valid count & `parseArgsList args = .ok ns` → either:
    - source evaluates to `some (resultObs result v)` and `PrintsResult result v ρ`,
    - source evaluates to a non-matching observation `o` and `ReportsMsg arity .notValue ρ`,
    - a resource exhaustion report (`.heap`, `.stack`, or `.natOverflow`),
    - `ρ = []` (timeout / stopped before output), or
    - `goesWrong ns` (the ONLY case allowing `.trap`, `.stuck`, or arbitrary syscalls). -/
def PlainExeOutcome (srcEval : List Nat → Option Obs → Prop) (goesWrong : List Nat → Prop)
    (arity : Nat) (result : ResultKind) (D : Nat) (args : List (List Nat)) (σ : List Sys) : Prop :=
  PlainRefused arity D σ ∨
  σ <+: started D ∨
  ∃ ρ, σ = started D ++ ρ ∧
    ((args.length ≠ arity ∨ args = []) ∧ ReportsMsg arity .count ρ ∨
     args.length = arity ∧
      match parseArgsList args with
      | .overflow => ReportsMsg arity .natOverflow ρ
      | .bad => ReportsMsg arity .numeral ρ
      | .ok ns =>
        (∃ v, PlainCallMatches result (.ok (some (resultObs result v))) (.value v) ∧
              srcEval ns (some (resultObs result v)) ∧ PrintsResult result v ρ) ∨
        (∃ o, PlainCallMatches result (.ok o) .notValue ∧ srcEval ns o ∧ ReportsMsg arity .notValue ρ) ∨
        (∃ m, (m = .heap ∨ m = .stack ∨ m = .natOverflow) ∧ ReportsMsg arity m ρ) ∨
        ρ = [] ∨
        goesWrong ns)

private theorem no_other_writeSeq' {fd : Word} {status : Nat} {m : List UInt8} {ok : Bool}
    {ρ : List Sys} (h : WriteSeq fd status m ok ρ) : ∀ w, .other w ∉ ρ := by
  induction h with
  | done => intro w hm; simp at hm
  | step _ _ _ _ ih =>
    intro w hm
    rcases List.mem_cons.mp hm with h1 | h2
    · cases h1
    · exact ih w h2
  | refused _ _ => intro w hm; simp at hm

private theorem no_other_prefix' {p q : List Sys} (hp : p <+: q) {w : Word}
    (hq : .other w ∉ q) : .other w ∉ p := by
  obtain ⟨t, rfl⟩ := hp
  intro hm
  exact hq (List.mem_append_left t hm)

/-- An undocumented system call (`Sys.other`) occurs in `PlainExeOutcome` ONLY when
argument count & decimal parsing succeeded and `goesWrong ns` holds. -/
theorem PlainExeOutcome.goesWrong_of_other {srcEval : List Nat → Option Obs → Prop}
    {goesWrong : List Nat → Prop} {arity : Nat} {result : ResultKind} {D : Nat}
    {args : List (List Nat)} {σ : List Sys} {w : Word}
    (h : PlainExeOutcome srcEval goesWrong arity result D args (σ ++ [.other w])) :
    args.length = arity ∧
    ∃ ns, parseArgsList args = .ok ns ∧ goesWrong ns ∧ started D <+: σ := by
  have hmem : .other w ∈ σ ++ [.other w] := by simp
  have hns : .other w ∉ started D := by simp [started]
  rcases h with href | hpre | ⟨ρ, heq, hbody⟩
  · rcases href with ⟨r, ρ, _, ⟨ok, full, hw, hp⟩, hpre⟩ | ⟨r, ρ, _, ⟨ok, full, hw, hp⟩, hpre⟩
    · exact absurd hmem (no_other_prefix' hpre fun hm => by
        rcases List.mem_cons.mp hm with h0 | h0
        · cases h0
        · exact no_other_prefix' hp (no_other_writeSeq' hw w) h0)
    · exact absurd hmem (no_other_prefix' hpre fun hm => by
        rcases List.mem_cons.mp hm with h0 | h0
        · cases h0
        · rcases List.mem_cons.mp h0 with h0 | h0
          · cases h0
          · exact no_other_prefix' hp (no_other_writeSeq' hw w) h0)
  · exact absurd hmem (no_other_prefix' hpre hns)
  · have hmemρ : .other w ∈ ρ := by
      rw [heq] at hmem
      rcases List.mem_append.mp hmem with hs | hr
      · exact absurd hs hns
      · exact hr
    have hstPre : started D <+: σ := by
      have hlen : (started D).length ≤ σ.length := by
        by_cases hle : (started D).length ≤ σ.length
        · exact hle
        · have hlt' : σ.length < (started D).length := by omega
          have hmemS : .other w ∈ started D := by
            have hi : σ.length < (started D ++ ρ).length := by rw [← heq]; simp
            have hg : (started D ++ ρ)[σ.length] = .other w := by
              have := congrArg (fun l => l[σ.length]?) heq
              simp at this
              rw [List.getElem?_eq_getElem hi] at this
              exact Option.some.inj this.symm
            rw [List.getElem_append_left hlt'] at hg
            rw [← hg]
            exact List.getElem_mem hlt'
          exact absurd hmemS hns
      have htk := congrArg (List.take (started D).length) heq
      rw [List.take_append_of_le_length hlen, List.take_left] at htk
      exact ⟨σ.drop (started D).length, by
        have htd := List.take_append_drop (started D).length σ
        rw [htk] at htd
        exact htd⟩
    rcases hbody with ⟨_, ⟨ok, full, hw, hp⟩⟩ | ⟨hlen, hparse⟩
    · exact absurd hmemρ (no_other_prefix' hp (no_other_writeSeq' hw w))
    · cases hp : parseArgsList args with
      | overflow =>
        rw [hp] at hparse
        obtain ⟨ok, full, hw, hpr⟩ := hparse
        exact absurd hmemρ (no_other_prefix' hpr (no_other_writeSeq' hw w))
      | bad =>
        rw [hp] at hparse
        obtain ⟨ok, full, hw, hpr⟩ := hparse
        exact absurd hmemρ (no_other_prefix' hpr (no_other_writeSeq' hw w))
      | ok ns =>
        rw [hp] at hparse
        rcases hparse with ⟨v, _, _, ⟨ok, full, hw, hpr⟩⟩ | ⟨o, _, _, ⟨ok, full, hw, hpr⟩⟩ |
          ⟨m, _, ⟨ok, full, hw, hpr⟩⟩ | rfl | hgw
        · exact absurd hmemρ (no_other_prefix' hpr (no_other_writeSeq' hw w))
        · exact absurd hmemρ (no_other_prefix' hpr (no_other_writeSeq' hw w))
        · exact absurd hmemρ (no_other_prefix' hpr (no_other_writeSeq' hw w))
        · simp at hmemρ
        · exact ⟨hlen, ns, rfl, hgw, hstPre⟩

/-- Lift `PlainShows` over `objPlainCall` to `PlainExeOutcome` via any per-call
two-site refinement theorem (`Recheck.sound_at` or `RcReplay.sound_at`). -/
theorem PlainShows.refines_exe
    {obj : ByteArray} {roots : List Linked.Root} {r0 : Linked.Root}
    {textSize arity : Nat} {result : ResultKind} {D : Nat}
    {args : List (List Nat)} {σ : List Sys}
    {srcEval : List Nat → Option Obs → Prop} {goesWrong : List Nat → Prop}
    (hroot0 : roots[0]? = some r0) (hrp : r0.params = arity)
    (hRefOk : ∀ (ns : List Nat) (Drv : X86.Driver) (site : X86.Driver.Site) (k : Nat) (o : Option Obs),
      ns.length = arity → Drv.Ok textSize → (Drv.withSite site).Ok textSize →
      Lang.run (linkedOf obj roots Drv site) (0, ns) k = .ok o →
      srcEval ns o ∨ goesWrong ns)
    (hRefWrong : ∀ (ns : List Nat) (Drv : X86.Driver) (site : X86.Driver.Site) (k : Nat),
      ns.length = arity → Drv.Ok textSize → (Drv.withSite site).Ok textSize →
      ¬ goesWrong ns →
      ¬ (Lang.run (linkedOf obj roots Drv site) (0, ns) k).GoesWrong)
    (hs : PlainShows (linkedOf obj roots) textSize arity result D args σ) :
    PlainExeOutcome srcEval goesWrong arity result D args σ := by
  have call_eq : ∀ {Drv : X86.Driver} {site : X86.Driver.Site} {r : Linked.Root} {ns : List Nat} {k : Nat},
      (linkedOf obj roots Drv site).linked.roots[0]? = some r →
      ns.length = arity →
      Lang.run (linkedOf obj roots Drv site) (0, ns) k =
      (linkedOf obj roots Drv site).call r ns k := by
    intro Drv site r ns k hr0 hlen
    have hrEq : r = r0 := Option.some.inj (hr0.symm.trans hroot0)
    subst hrEq
    show LinkedAt.run (linkedOf obj roots Drv site) (0, ns) k = _
    unfold LinkedAt.run
    rw [hr0]
    exact Sem.entryRun_exact (hlen.trans hrp.symm) k
  rcases hs with href | hpre | ⟨ρ, heq, hbody⟩
  · exact .inl href
  · exact .inr (.inl hpre)
  · refine .inr (.inr ⟨ρ, heq, ?_⟩)
    rcases hbody with hwrong | ⟨hlen, hparse⟩
    · exact .inl hwrong
    · refine .inr ⟨hlen, ?_⟩
      cases hp : parseArgsList args with
      | overflow => rw [hp] at hparse; exact hparse
      | bad => rw [hp] at hparse; exact hparse
      | ok ns =>
        rw [hp] at hparse
        have hnsLen : ns.length = arity := (parseArgsList_ok_length hp).trans hlen
        rcases hparse with ⟨v, hobj, hpr⟩ | ⟨hobj, hrep⟩ | ⟨m, hobj, hrep⟩ | ⟨_, rfl⟩ | hstuck
        · obtain ⟨Drv, site, r, k, hr0, hD, hR, hcm⟩ := hobj
          have hcall := call_eq hr0 hnsLen (k := k)
          cases result with
          | nat =>
            rcases hcm with ⟨hres, hvlt⟩
            rw [← hcall] at hres
            rcases hRefOk ns Drv site k (some (.nat v)) hnsLen hD hR hres with hse | hgw
            · exact .inl ⟨v, ⟨rfl, hvlt⟩, hse, hpr⟩
            · exact .inr (.inr (.inr (.inr hgw)))
          | enum n =>
            rcases hcm with ⟨hres, hvlt⟩
            rw [← hcall] at hres
            rcases hRefOk ns Drv site k (some (.ctor v [])) hnsLen hD hR hres with hse | hgw
            · exact .inl ⟨v, ⟨rfl, hvlt⟩, hse, hpr⟩
            · exact .inr (.inr (.inr (.inr hgw)))
        · obtain ⟨Drv, site, r, k, hr0, hD, hR, hcm⟩ := hobj
          have hcall := call_eq hr0 hnsLen (k := k)
          cases result with
          | nat =>
            rcases hcm with hres | ⟨o, hres, hne⟩
            · rw [← hcall] at hres
              rcases hRefOk ns Drv site k none hnsLen hD hR hres with hse | hgw
              · exact .inr (.inl ⟨none, .inl rfl, hse, hrep⟩)
              · exact .inr (.inr (.inr (.inr hgw)))
            · rw [← hcall] at hres
              rcases hRefOk ns Drv site k (some o) hnsLen hD hR hres with hse | hgw
              · exact .inr (.inl ⟨some o, .inr ⟨o, rfl, hne⟩, hse, hrep⟩)
              · exact .inr (.inr (.inr (.inr hgw)))
          | enum n =>
            rcases hcm with hres | ⟨o, hres, hne⟩
            · rw [← hcall] at hres
              rcases hRefOk ns Drv site k none hnsLen hD hR hres with hse | hgw
              · exact .inr (.inl ⟨none, .inl rfl, hse, hrep⟩)
              · exact .inr (.inr (.inr (.inr hgw)))
            · rw [← hcall] at hres
              rcases hRefOk ns Drv site k (some o) hnsLen hD hR hres with hse | hgw
              · exact .inr (.inl ⟨some o, .inr ⟨o, rfl, hne⟩, hse, hrep⟩)
              · exact .inr (.inr (.inr (.inr hgw)))
        · obtain ⟨Drv, site, r, k, hr0, hD, hR, hcm⟩ := hobj
          cases m with
          | heap => exact .inr (.inr (.inl ⟨.heap, .inl rfl, hrep⟩))
          | stack => exact .inr (.inr (.inl ⟨.stack, .inr (.inl rfl), hrep⟩))
          | natOverflow => exact .inr (.inr (.inl ⟨.natOverflow, .inr (.inr rfl), hrep⟩))
          | trap =>
            have hcall := call_eq hr0 hnsLen (k := k)
            have hgw : goesWrong ns := Classical.byContradiction fun hngw =>
              hRefWrong ns Drv site k hnsLen hD hR hngw (by
                rw [hcall, hcm]; exact Result.goesWrong_trap)
            exact .inr (.inr (.inr (.inr hgw)))
          | _ => cases hcm
        · exact .inr (.inr (.inr (.inl rfl)))
        · obtain ⟨Drv, site, r, k, hr0, hD, hR, hcm⟩ := hstuck
          have hcall := call_eq hr0 hnsLen (k := k)
          have hgw : goesWrong ns := Classical.byContradiction fun hngw =>
            hRefWrong ns Drv site k hnsLen hD hR hngw (by
              rw [hcall, hcm]; exact Result.goesWrong_stuck)
          exact .inr (.inr (.inr (.inr hgw)))

/-! ## Top-Level Plain `--exe` Theorems -/

/-- **Plain standalone executable theorem** (immortal and zero-RC objects): for an
object `Recheck.run` made and its checked plain executable `Exe.build a layout`,
every finite trace from `Process.Loaded` satisfies `PlainExeOutcome` against
`a.src` and `a.front.view`. -/
theorem plain_exe_sound {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {a : Recheck.Artifact} (h : Recheck.run cfg P c = .ok a)
    {layout : Layout} {inp : X86.Exe.Input} {ce : X86.Exe.Certified inp}
    (hb : Exe.build a layout = .ok ⟨inp, ce⟩)
    {args : List (List Nat)} (hargs : ArgsOk args)
    {s₀ : ByteEval.State} (hload : Loaded (Certified.checked ce) args s₀)
    {σ : List Sys} (hσ : Trace ce.bytes s₀ σ) :
    PlainExeOutcome (srcPlainEval a.src a.checked a.front.view)
      (fun ns => a.front.GoesWrong (0, ns))
      inp.arity inp.result (fileBase + ce.plan.placement.dataOffset) args σ := by
  obtain ⟨r, hf, hinp⟩ := build_spec hb
  obtain ⟨hahead, _, hnatParams, htySpec⟩ := fragment_spec hf
  have hroot0 := plain_linkedRoot h hf
  have hrm : PlainRootMatches inp { symbol := r.symbol, params := r.params, ty := r.ty } := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hinp]
    · rw [hinp]
    · exact htySpec
  have hs := plain_shell_sound ce hroot0 hrm hargs hload hσ
  obtain ⟨-, xv, -, -, hemit, -⟩ := Recheck.run_parts h
  have hts : ce.plan.placement.textSize = a.backend.encoded.text.size :=
    plain_textSize_of_emit hemit (by rw [hinp]; rfl) ce
  have hobjEq : inp.object = a.object := by rw [hinp]
  have hrp : ({ symbol := r.symbol, params := r.params, ty := r.ty } : Linked.Root).params = inp.arity := by
    rw [hinp]
  rw [hobjEq, hts] at hs
  exact PlainShows.refines_exe hroot0 hrp
    (fun ns D site k o hlen hD hR hrun => by
      have hcov : a.front.Covered c (0, ns) :=
        Recheck.Artifact.covered_head h hahead hnatParams (hlen.trans hrp.symm)
      exact (Recheck.sound_at h D hD site hR (0, ns) hcov).1 k o hrun)
    (fun ns D site k hlen hD hR hngw => by
      have hcov : a.front.Covered c (0, ns) :=
        Recheck.Artifact.covered_head h hahead hnatParams (hlen.trans hrp.symm)
      exact (Recheck.sound_at h D hD site hR (0, ns) hcov).2.1 hngw k)
    hs

/-- **Plain standalone executable `Unspecified` exclusion** (immortal & zero-RC):
the process reaches an `Unspecified` state ONLY when argument parsing succeeded
and `a.front.GoesWrong (0, ns)` holds. -/
theorem plain_exe_unspecified {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {a : Recheck.Artifact} (h : Recheck.run cfg P c = .ok a)
    {layout : Layout} {inp : X86.Exe.Input} {ce : X86.Exe.Certified inp}
    (hb : Exe.build a layout = .ok ⟨inp, ce⟩)
    {args : List (List Nat)} (hargs : ArgsOk args)
    {s₀ : ByteEval.State} (hload : Loaded (Certified.checked ce) args s₀)
    {σ : List Sys} {s : ByteEval.State}
    (hr : Run ce.bytes s₀ σ s) (hu : Unspecified ce.bytes s) :
    args.length = inp.arity ∧
    ∃ ns, parseArgsList args = .ok ns ∧ a.front.GoesWrong (0, ns) ∧
      started (fileBase + ce.plan.placement.dataOffset) <+: σ :=
  PlainExeOutcome.goesWrong_of_other
    (plain_exe_sound h hb hargs hload (Run.other_of_unspecified hr hu 0))

/-- **Plain standalone executable theorem** (plain-RC objects via `toRecheckArtifact`). -/
theorem Rc.plain_exe_sound {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.RcReplay.Cert}
    {a : Recheck.RcReplay.Artifact} (h : Recheck.RcReplay.run cfg P c = .ok a)
    {a' : Recheck.Artifact} (h' : a.toRecheckArtifact c = .ok a')
    {layout : Layout} {inp : X86.Exe.Input} {ce : X86.Exe.Certified inp}
    (hb : Exe.build a' layout = .ok ⟨inp, ce⟩)
    {args : List (List Nat)} (hargs : ArgsOk args)
    {s₀ : ByteEval.State} (hload : Loaded (Certified.checked ce) args s₀)
    {σ : List Sys} (hσ : Trace ce.bytes s₀ σ) :
    PlainExeOutcome (srcPlainEval a.front.src a.front.checked a.front.view)
      (fun ns => a.front.GoesWrong (0, ns))
      inp.arity inp.result (fileBase + ce.plan.placement.dataOffset) args σ := by
  obtain ⟨xv', xl', rfl⟩ := toRecheck_spec h'
  obtain ⟨r, hf, hinp⟩ := build_spec hb
  obtain ⟨hahead, _, hnatParams, htySpec⟩ := fragment_spec hf
  have hhead' : a.roots.head? = some r := hahead
  rw [Recheck.RcReplay.run_roots h] at hhead'
  have hfst : a.front.lowered.roots.map Prod.fst = a.front.cfg.base.exports :=
    Recheck.RcReplay.public_roots (Recheck.RcReplay.runFront_native (Recheck.RcReplay.run_parts h).1).2
  have hroot0 : a.linkedRoots[0]? = some { symbol := r.symbol, params := r.params, ty := r.ty } :=
    head_linkedRoot hfst hhead'
  have hrm : PlainRootMatches inp { symbol := r.symbol, params := r.params, ty := r.ty } := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hinp]
    · rw [hinp]
    · exact htySpec
  have hs := plain_shell_sound ce hroot0 hrm hargs hload hσ
  obtain ⟨-, xv, xl, -, -, hemit, -⟩ := Recheck.RcReplay.run_parts h
  have hts : ce.plan.placement.textSize = a.backend.encoded.text.size :=
    plain_textSize_of_emit hemit (by rw [hinp]; rfl) ce
  have hobjEq : inp.object = a.backend.object := by rw [hinp]; rfl
  have hrp : ({ symbol := r.symbol, params := r.params, ty := r.ty } : Linked.Root).params = inp.arity := by
    rw [hinp]
  rw [hobjEq, hts] at hs
  exact PlainShows.refines_exe hroot0 hrp
    (fun ns D site k o hlen hD hR hrun => by
      have hcov : a.front.Covered c (0, ns) :=
        Recheck.RcReplay.Artifact.covered_head h hahead hnatParams (hlen.trans hrp.symm)
      exact (Recheck.RcReplay.sound_at h D hD site hR (0, ns) hcov).1 k o hrun)
    (fun ns D site k hlen hD hR hngw => by
      have hcov : a.front.Covered c (0, ns) :=
        Recheck.RcReplay.Artifact.covered_head h hahead hnatParams (hlen.trans hrp.symm)
      exact (Recheck.RcReplay.sound_at h D hD site hR (0, ns) hcov).2.1 hngw k)
    hs

/-- `plain_exe_unspecified` for plain-RC objects. -/
theorem Rc.plain_exe_unspecified {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.RcReplay.Cert}
    {a : Recheck.RcReplay.Artifact} (h : Recheck.RcReplay.run cfg P c = .ok a)
    {a' : Recheck.Artifact} (h' : a.toRecheckArtifact c = .ok a')
    {layout : Layout} {inp : X86.Exe.Input} {ce : X86.Exe.Certified inp}
    (hb : Exe.build a' layout = .ok ⟨inp, ce⟩)
    {args : List (List Nat)} (hargs : ArgsOk args)
    {s₀ : ByteEval.State} (hload : Loaded (Certified.checked ce) args s₀)
    {σ : List Sys} {s : ByteEval.State}
    (hr : Run ce.bytes s₀ σ s) (hu : Unspecified ce.bytes s) :
    args.length = inp.arity ∧
    ∃ ns, parseArgsList args = .ok ns ∧ a.front.GoesWrong (0, ns) ∧
      started (fileBase + ce.plan.placement.dataOffset) <+: σ :=
  PlainExeOutcome.goesWrong_of_other
    (Rc.plain_exe_sound h h' hb hargs hload (Run.other_of_unspecified hr hu 0))

/-! ## Unified `.ix.cert` v1 → Real Execution Theorems (`verify-exe`) -/

/-- **End-to-end certified plain executable theorem (`ixcc verify-exe` → x86-64 process):**
from raw certified `.ix.cert` v1 executable bytes accepted by `Exe.Cert.verifyExeBytes`
with `v.exeKind = .plain`, establishes simultaneously:
1. Pure-logical `KF-4` seed-closure kernel acceptance (`Ix.Kernel.Admission.checkBytes`
   under committed `defaultBinding` + committed `preludeFor`, `tableRestrictsDefault`,
   and `N5` `checkClosureModes`), `Stage A` relevance, `EM-0` `Definition.asserts`,
   and `CompileClaim.verifyProgram`;
2. Hardened `.ix.cert` v1 ELF64 trailer invariants (`zeroShdr` core equality,
   strict `0xCC` (`int3`) RX page-tail trap sled, page-aligned `.ix.cert`, flush EOF);
3. For EVERY finite trace of the verified core executable `ce.bytes` from
   `Process.Loaded`, the trace satisfies `PlainExeOutcome` against the verified
   source program (across `.immortal`, `.zeroRc`, and `.plainRc` policies). -/
theorem verifyExeBytes_plain_sound {exeBytes : ByteArray} {extEnv? extEq? : Option ByteArray}
    {v : Exe.Cert.VerifiedExe}
    (h : Exe.Cert.verifyExeBytes exeBytes extEnv? extEq? Src.KernelFront.defaultLimits = .ok v)
    (hkind : v.exeKind = .plain) :
    ∃ (payloadBytes : ByteArray) (inp : Recheck.Input) (tc : Src.Table.TableCert)
      (cl : CompileClaim.ClosureAccepted inp v.claim.target tc Src.KernelFront.defaultLimits)
      (a : Recheck.Artifact) (inpExe : X86.Exe.Input) (ce : X86.Exe.Certified inpExe)
      (srcEval : List Nat → Option Obs → Prop) (goesWrong : List Nat → Prop),
      Ix.Kernel.Admission.checkBytes Src.KernelFront.hash cl.defBinding
        Src.KernelFront.defaultLimits cl.records cl.blobs cl.hints.lookup = .ok cl.env ∧
      CompileClaim.tableRestrictsDefault inp.kernel.acc.table cl.defTable = true ∧
      CompileClaim.checkClosureModes cl.defTable cl.pre cl.env cl.constants cl.blobs = .ok () ∧
      Exe.build a v.layout = .ok ⟨inpExe, ce⟩ ∧
      X86.Exe.Cert.zeroShdr (exeBytes.extract 0 ce.bytes.size) = ce.bytes ∧
      (∀ i, ce.bytes.size ≤ i → i < alignUp ce.bytes.size X86.Exe.Cert.certPageSize →
        exeBytes.data[i]? = some X86.Exe.Cert.trapByte) ∧
      X86.Exe.Cert.checkTrailer ce.bytes payloadBytes exeBytes = true ∧
      (∀ {args : List (List Nat)}, ArgsOk args →
        ∀ {s₀ : ByteEval.State}, Loaded (Certified.checked ce) args s₀ →
        ∀ {σ : List Sys}, Trace ce.bytes s₀ σ →
          PlainExeOutcome srcEval goesWrong inpExe.arity inpExe.result
            (fileBase + ce.plan.placement.dataOffset) args σ) := by
  obtain ⟨payloadBytes, payload, envBytes, equations, certText, inp, tc, cl, a, expectedCore,
    -, -, -, -, -, -, -, hacc, hrest, hmod, -, -, -, hchk, hcore, hsled, -, -,
    hImmRun, hRcRun, hPlain, -⟩ := Exe.Cert.verifyExeBytes_sound h
  obtain ⟨inpExe, ce, hb, hceEq⟩ := hPlain hkind
  subst hceEq
  cases hpol : v.claim.policy with
  | immortal =>
    obtain ⟨cert, _, hrun⟩ := hImmRun (.inl hpol)
    exact ⟨payloadBytes, inp, tc, cl, a, inpExe, ce,
      srcPlainEval a.src a.checked a.front.view, fun ns => a.front.GoesWrong (0, ns),
      hacc, hrest, hmod, hb, hcore, hsled, hchk,
      fun {_} hargs {_} hload {_} hσ => plain_exe_sound hrun hb hargs hload hσ⟩
  | zeroRc =>
    obtain ⟨cert, _, hrun⟩ := hImmRun (.inr hpol)
    exact ⟨payloadBytes, inp, tc, cl, a, inpExe, ce,
      srcPlainEval a.src a.checked a.front.view, fun ns => a.front.GoesWrong (0, ns),
      hacc, hrest, hmod, hb, hcore, hsled, hchk,
      fun {_} hargs {_} hload {_} hσ => plain_exe_sound hrun hb hargs hload hσ⟩
  | plainRc =>
    obtain ⟨cert, rcArt, _, hrun, hto⟩ := hRcRun hpol
    exact ⟨payloadBytes, inp, tc, cl, a, inpExe, ce,
      srcPlainEval rcArt.front.src rcArt.front.checked rcArt.front.view,
      fun ns => rcArt.front.GoesWrong (0, ns),
      hacc, hrest, hmod, hb, hcore, hsled, hchk,
      fun {_} hargs {_} hload {_} hσ => Rc.plain_exe_sound hrun hto hb hargs hload hσ⟩

/-- **End-to-end certified machine executable theorem (`ixcc verify-exe` → x86-64 process):**
analogous to `verifyExeBytes_plain_sound` for `v.exeKind = .machine`, composing
`Exe.Cert.verifyExeBytes_sound` with `machine_exe_sound` / `Rc.machine_exe_sound`. -/
theorem verifyExeBytes_machine_sound {exeBytes : ByteArray} {extEnv? extEq? : Option ByteArray}
    {v : Exe.Cert.VerifiedExe}
    (h : Exe.Cert.verifyExeBytes exeBytes extEnv? extEq? Src.KernelFront.defaultLimits = .ok v)
    (hkind : v.exeKind = .machine) :
    let L : X86.Exe.Machine.Layout := { stack := v.layout.stack, region := v.layout.region }
    ∃ (payloadBytes : ByteArray) (inp : Recheck.Input) (tc : Src.Table.TableCert)
      (cl : CompileClaim.ClosureAccepted inp v.claim.target tc Src.KernelFront.defaultLimits)
      (a : Recheck.Artifact) (root : Recheck.Root)
      (ce : X86.Exe.Machine.Certified L root.symbol a.object)
      (srcCall : Exe.Machine.Call) (goesWrong : Nat → Nat → Prop),
      Ix.Kernel.Admission.checkBytes Src.KernelFront.hash cl.defBinding
        Src.KernelFront.defaultLimits cl.records cl.blobs cl.hints.lookup = .ok cl.env ∧
      CompileClaim.tableRestrictsDefault inp.kernel.acc.table cl.defTable = true ∧
      CompileClaim.checkClosureModes cl.defTable cl.pre cl.env cl.constants cl.blobs = .ok () ∧
      Exe.buildMachine a L = .ok ⟨root, ce⟩ ∧
      X86.Exe.Cert.zeroShdr (exeBytes.extract 0 ce.checked.bytes.size) = ce.checked.bytes ∧
      (∀ i, ce.checked.bytes.size ≤ i → i < alignUp ce.checked.bytes.size X86.Exe.Cert.certPageSize →
        exeBytes.data[i]? = some X86.Exe.Cert.trapByte) ∧
      X86.Exe.Cert.checkTrailer ce.checked.bytes payloadBytes exeBytes = true ∧
      (∀ {args : List (List Nat)}, ArgsOk args →
        ∀ {s₀ : ByteEval.State}, Loaded ce.checked args s₀ →
        ∀ {σ : List Sys}, Trace ce.checked.bytes s₀ σ →
          Outcome srcCall goesWrong
            (fileBase + ce.checked.plan.placement.dataOffset) args σ) := by
  intro L
  obtain ⟨payloadBytes, payload, envBytes, equations, certText, inp, tc, cl, a, expectedCore,
    -, -, -, -, -, -, -, hacc, hrest, hmod, -, -, -, hchk, hcore, hsled, -, -,
    hImmRun, hRcRun, -, hMach⟩ := Exe.Cert.verifyExeBytes_sound h
  obtain ⟨root, ce, hb, hceEq⟩ := hMach hkind
  subst hceEq
  have hm : Exe.machine a = .ok root := by
    unfold Exe.buildMachine at hb
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hb
    cases hmr : Exe.machine a with
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
  cases hpol : v.claim.policy with
  | immortal =>
    obtain ⟨cert, _, hrun⟩ := hImmRun (.inl hpol)
    exact ⟨payloadBytes, inp, tc, cl, a, root, ce,
      Exe.Machine.srcCall a, fun s e => a.front.GoesWrong (0, [s, e]),
      hacc, hrest, hmod, hb, hcore, hsled, hchk,
      fun {_} hargs {_} hload {_} hσ => machine_exe_sound hrun hm ce hargs hload hσ⟩
  | zeroRc =>
    obtain ⟨cert, _, hrun⟩ := hImmRun (.inr hpol)
    exact ⟨payloadBytes, inp, tc, cl, a, root, ce,
      Exe.Machine.srcCall a, fun s e => a.front.GoesWrong (0, [s, e]),
      hacc, hrest, hmod, hb, hcore, hsled, hchk,
      fun {_} hargs {_} hload {_} hσ => machine_exe_sound hrun hm ce hargs hload hσ⟩
  | plainRc =>
    obtain ⟨cert, rcArt, _, hrun, hto⟩ := hRcRun hpol
    exact ⟨payloadBytes, inp, tc, cl, a, root, ce,
      Exe.Machine.Rc.srcCall rcArt, fun s e => rcArt.front.GoesWrong (0, [s, e]),
      hacc, hrest, hmod, hb, hcore, hsled, hchk,
      fun {_} hargs {_} hload {_} hσ => Rc.machine_exe_sound hrun hto hm ce hargs hload hσ⟩

end IxCC.Exe.Plain
