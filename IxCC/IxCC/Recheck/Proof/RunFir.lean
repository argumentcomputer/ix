import IxCC.Recheck.RunFir
import IxCC.Recheck.Proof.Front
import IxCC.Fir.Proof.Lang

/-!
# The front half up to Fir refines

`Recheck.front_fir`: for every program `Recheck.runFir` accepts, the Fir
program refines the checked source (SrcEval on the program the front end
checked), on every covered input (`FrontFir.Covered`: an input of exactly its
root's declared parameter count, and every input when the closures step left
the certificate's program unchanged). It is the composition `front_cfg` makes
down to Cfg, stopped at Fir:

```text
SrcEval ─erase_refines→ Lam ─anfOf_refines (covered inputs)→ Anf ─Fir.Proof.lower_refines→ Fir
```

As every refinement of the pipeline, it asks nothing of a stuck source
(`Sem.Behaviour.Refines.stuck`): a value Fir returns is a value SrcEval
returns with the same observation, **or SrcEval is stuck**
(`Sem.RefinesOn.backward`).

`runLir_runFir`: a program the native front half accepts is accepted here,
with the same source, annotation, Lam, Anf and Fir programs.
-/

set_option autoImplicit false

namespace IxCC.Recheck

open IxCC.Lam.Erase.Proof (CheckedProgram)

/-- **The steps up to Fir**: `runFir`'s success is each step's. -/
theorem runFir_spec {cfg : Config} {P : Src.Program} {c : Cert} {f : FrontFir}
    (h : runFir cfg P c = .ok f) :
    front cfg P c = .ok (f.src, f.checked) ∧ (∃ st, Lam.erase f.src f.checked = .ok (f.lam, st)) ∧
      anfOf c f.src f.lam = .ok f.anf ∧ Fir.lower f.anf = .ok f.fir := by
  unfold runFir at h
  cases hfr : front cfg P c with
  | error e => rw [hfr] at h; cases h
  | ok sc =>
    obtain ⟨src, checked⟩ := sc
    rw [hfr] at h
    simp only [bind, Except.bind] at h
    cases her : Lam.erase src checked with
    | error e => rw [her] at h; cases h
    | ok ls =>
      obtain ⟨lam, st⟩ := ls
      simp only [her, Except.mapError] at h
      cases ha : anfOf c src lam with
      | error e => rw [ha] at h; cases h
      | ok a =>
        simp only [ha] at h
        cases hl : Fir.lower a with
        | error e => rw [hl] at h; cases h
        | ok F =>
          simp only [hl, pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact ⟨rfl, ⟨st, her⟩, ha, hl⟩

/-- **The front half up to Fir refines**: for every program `Recheck.runFir`
accepts, the Fir program refines the checked source on every covered input. -/
theorem front_fir {cfg : Config} {P : Src.Program} {c : Cert} {f : FrontFir}
    (h : runFir cfg P c = .ok f) :
    Sem.RefinesOn (f.Covered c) (⟨f.src, f.checked⟩ : CheckedProgram) f.fir := by
  obtain ⟨-, ⟨st, her⟩, hanf, hfir⟩ := runFir_spec h
  exact Sem.RefinesOn.refines_trans (Lam.Erase.Proof.erase_refines her)
    ((anfOf_refines hanf).trans_refines (Fir.Proof.lower_refines hfir))

/-- **One pipeline**: a program the native front half (`runLir`) accepts is
accepted by `runFir`, with the same levels down to Fir. -/
theorem runLir_runFir {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (h : runLir cfg P c = .ok f) :
    runFir cfg P c =
      .ok { src := f.src, checked := f.checked, lam := f.lam, anf := f.anf, fir := f.fir } := by
  obtain ⟨hfr, ⟨st, her⟩, hanf, hfir, -, -, -, -⟩ := runLir_spec h
  unfold runFir
  rw [hfr]
  simp only [bind, Except.bind, her, Except.mapError, hanf, hfir, pure, Except.pure]

end IxCC.Recheck
