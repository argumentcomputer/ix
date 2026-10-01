import Compilatrix.Recheck.Run
import Compilatrix.Lam.Erase.Proof.Correct
import Compilatrix.Anf.Proof.Pass.Pipeline
import Compilatrix.Cfg.Proof.OfAnf
import Compilatrix.Rt.Proof.Lang

/-!
# The front half composed (M2.7)

`Recheck.front_refines`: for every program the recheck path's front half
accepts (`Recheck.runLir`: the table and annotation of the certificate,
`Lazify`, erasure, the middle end on the certificate's decisions, `Fir`,
`Own` and `Cfg`, the roots' parameter check, the switch check and
`Rt.lower`), on every model region `cx_init` accepts, the lowered Lir
program loaded into the region (`Front.loaded`) refines the checked source
(SrcEval on the program the front end checked) viewed at the roots'
readback types (`Front.source`).

The refinements of the passes compose by `Sem.Refines.trans`:

```text
SrcEval ─erase_refines→ Lam ─Pipeline.Proof.run_correct→ Anf ─Cfg.ofAnf_correct→ Cfg      (obsV, by source constructor)
   view (Sem.Viewed.refines)                                                        view
SrcEval at the roots' types ───────────────────────────────────────────→ Cfg at the roots' types
                                                         ─Rt.lower_refines→ Lir (Rt.readback at the type)
```

Every level from SrcEval to Cfg observes values by source constructor; the
runtime reads a word back by tag at the root's type. The view
(`Rt.viewOf`) relabels a source observation by tag at the root's type and
rejects (makes stuck) a result the type does not read back, so a source
result outside its root's type is one more way the source goes wrong
(`Front.GoesWrong`, roadmap §1.1's disjunct at stage S). Clock maps are
hidden by `Sem.Refines`: Anf → Fir `k ↦ tickBound A · (k + 1)`, Cfg → Lir
`k ↦ k + 1`, the rest `id` or forward-only.

At K1's result types the view rejects nothing well typed: a `Nat` root
reports a `Nat` as itself (`view_nat`), a `Bool` root reports `false` and
`true` by their tags (`view_bool`).

For M2.8's `Recheck.sound`: `run_runLir` (a successful `Recheck.run` ran
`runLir`, and its artifact's levels and roots are the front half's) and
`rootsOf_entry` (each of the artifact's roots is the loaded program's entry
at the same index: function, parameter count, readback type).
`Recheck.Proof.Sound` states the interface with the backend half (M2.7b)
and derives `compile_sound` and `compile_safe` from it.
-/

set_option autoImplicit false

namespace Compilatrix.Recheck

open Compilatrix.Sem (Obs Lang)
open Compilatrix.Lam.Erase.Proof (CheckedProgram)

/-! ## The front half's pieces -/

/-- The roots' readback types, by root index (`rootTy`, as `rootsOf`). -/
def Front.tys (f : Front) (r : Nat) : Option (Rt.Sig × Rt.FoTy) :=
  (f.src.roots[r]?).bind fun p => rootTy f.src f.cfg p.2

/-- The view of the front half's results: by tag at the roots' readback
types (`Rt.viewOf`). -/
def Front.view (f : Front) : Nat → Option Obs → Option (Option Obs) := Rt.viewOf f.cfg.ctors f.tys

/-- The checked source viewed at the roots' readback types. -/
def Front.source (f : Front) : Sem.Viewed CheckedProgram := ⟨⟨f.src, f.checked⟩, f.view⟩

/-- The lowered program loaded into machine `M`, its roots read back at
their types. -/
def Front.loaded (f : Front) (M : Rt.Model) : Rt.Loaded := Rt.Loaded.ofLowered f.cfg f.lowered f.tys M

/-- **The front half's steps**: `runLir`'s success is each step's. -/
theorem runLir_spec {cfg : Config} {P : Src.Program} {c : Cert} {f : Front} (h : runLir cfg P c = .ok f) :
    front cfg P c = .ok (f.src, f.checked) ∧ (∃ st, Lam.erase f.src f.checked = .ok (f.lam, st)) ∧
      Anf.Pipeline.run c.mid f.lam = .ok f.anf ∧ Fir.lower f.anf = .ok f.fir ∧
      f.own = Own.immortal f.fir ∧ f.cfg = Cfg.lower f.own ∧ Rt.switchesOk f.cfg = true ∧
      Rt.lower { names := cfg.names } f.cfg = .ok f.lowered := by
  unfold runLir at h
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
      cases hm : middle c lam with
      | error e => rw [hm] at h; cases h
      | ok m =>
        obtain ⟨anf, fir, own, C⟩ := m
        simp only [hm] at h
        cases hp : checkParams cfg C (List.zipIdx C.exports |>.map fun (f, i) => (i, f)) with
        | error e => rw [hp] at h; cases h
        | ok u =>
          simp only [hp] at h
          cases hs : Rt.checkSwitches C with
          | error e => rw [hs] at h; cases h
          | ok u' =>
            simp only [hs] at h
            cases hl : Rt.lower { names := cfg.names } C with
            | error e => rw [hl] at h; cases h
            | ok L =>
              simp only [hl, pure, Except.pure, Except.ok.injEq] at h
              subst h
              unfold middle at hm
              cases ha : Anf.Pipeline.run c.mid lam with
              | error e => rw [ha] at hm; cases hm
              | ok a =>
                simp only [ha, Except.mapError, bind, Except.bind] at hm
                cases hf : Fir.lower a with
                | error e => rw [hf] at hm; cases hm
                | ok F =>
                  simp only [hf, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
                  exact ⟨rfl, ⟨st, her⟩, rfl, hf, rfl, rfl, Rt.checkSwitches_ok hs, hl⟩

theorem checkParams_ok {cfg : Config} {C : Cfg.Program} :
    ∀ {l : List (Nat × Fir.FunId)}, checkParams cfg C l = .ok () → ∀ p ∈ l, cfgParams C p.2 ≤ maxParams
  | [], _, p, hp => nomatch hp
  | (i, g) :: rest, h, p, hp => by
    simp only [checkParams] at h
    split at h
    · cases h
    · rename_i hn
      rcases List.mem_cons.1 hp with rfl | hp'
      · exact Nat.le_of_not_lt hn
      · exact checkParams_ok h p hp'

/-- **Every root takes at most the wrapper's parameters** (`checkParams`,
what the entry wrapper needs: at most `maxParams` arguments). -/
theorem runLir_params {cfg : Config} {P : Src.Program} {c : Cert} {f : Front} (h : runLir cfg P c = .ok f)
    {i : Nat} {g : Fir.FunId} (hg : f.cfg.exports[i]? = some g) : cfgParams f.cfg g ≤ maxParams := by
  unfold runLir at h
  cases hfr : front cfg P c with
  | error e => rw [hfr] at h; cases h
  | ok sc =>
    rw [hfr] at h
    simp only [bind, Except.bind] at h
    cases her : Lam.erase sc.1 sc.2 with
    | error e => rw [her] at h; cases h
    | ok ls =>
      simp only [her, Except.mapError] at h
      cases hm : middle c ls.1 with
      | error e => rw [hm] at h; cases h
      | ok m =>
        simp only [hm] at h
        cases hp : checkParams cfg m.2.2.2 (List.zipIdx m.2.2.2.exports |>.map fun (f, i) => (i, f)) with
        | error e => rw [hp] at h; cases h
        | ok u =>
          simp only [hp] at h
          cases hs : Rt.checkSwitches m.2.2.2 with
          | error e => rw [hs] at h; cases h
          | ok u' =>
            simp only [hs] at h
            cases hl : Rt.lower { names := cfg.names } m.2.2.2 with
            | error e => rw [hl] at h; cases h
            | ok L =>
              simp only [hl, pure, Except.pure, Except.ok.injEq] at h
              subst h
              refine checkParams_ok hp (i, g) (List.mem_map.2 ⟨(g, i), ?_, rfl⟩)
              have := List.getElem?_zipIdx (l := m.2.2.2.exports) (i := 0) (j := i)
              rw [hg, Option.map_some, Nat.zero_add] at this
              exact List.mem_of_getElem? this

/-! ## The view at K1's result types -/

/-- At a `Nat` root the view reports a `Nat` result as itself. -/
theorem view_nat {f : Front} {r : Nat} (h : f.tys r = some ({}, .nat)) (n : Nat) :
    f.view r (some (.nat n)) = some (some (.nat n)) := by
  simp [Front.view, Rt.viewOf, h, Rt.tagify]

/-- At a `Bool` root (both `Bool` constructors pinned and in the table) the
view reports `false` and `true` by their tags. -/
theorem view_bool {f : Front} {r : Nat} (h : f.tys r = some (boolSig f.cfg, .ind 0)) {kF kT : Key.CtorKey}
    {cF cT : Fir.CtorInfo} (hF : f.cfg.known.boolFalse = some kF) (hT : f.cfg.known.boolTrue = some kT)
    (hcF : Fir.CtorInfo.ofKey f.cfg.ctors kF = some cF) (hcT : Fir.CtorInfo.ofKey f.cfg.ctors kT = some cT)
    {cid : Src.CId} {c : Fir.CtorInfo} (hk : Key.CtorKey.src cid = kF ∨ Key.CtorKey.src cid = kT)
    (hc : Fir.CtorInfo.ofKey f.cfg.ctors (.src cid) = some c) :
    f.view r (some (.ctor cid [])) = some (some (.ctor c.tag [])) := by
  have hlt : c.tag < max cF.tag cT.tag + 1 := by
    rcases hk with rfl | rfl
    · rw [hcF] at hc; cases hc; omega
    · rw [hcT] at hc; cases hc; omega
  have hsig : (boolSig f.cfg).ctor? 0 c.tag = some [] := by
    simp only [boolSig, hF, hT, Option.bind_some, hcF, hcT, Option.map_some, Rt.Sig.ctor?,
      List.getElem?_cons_zero, List.getElem?_replicate, hlt, if_true]
  simp only [Front.view, Rt.viewOf, h, Option.bind_some, Rt.tagify, hc, hsig, if_true, Option.map_some]

/-! ## The front theorem -/

/-- The checked source refines into Cfg (`erase_refines`, the middle end,
`Cfg.ofAnf_correct`). -/
theorem front_cfg {cfg : Config} {P : Src.Program} {c : Cert} {f : Front} (h : runLir cfg P c = .ok f) :
    Sem.Refines (⟨f.src, f.checked⟩ : CheckedProgram) f.cfg := by
  obtain ⟨-, ⟨st, her⟩, hanf, hfir, hown, hcfg, -, -⟩ := runLir_spec h
  have hofAnf : Cfg.ofAnf f.anf = .ok f.cfg := by
    unfold Cfg.ofAnf
    rw [hfir, hcfg, hown]
    rfl
  exact (Lam.Erase.Proof.erase_refines her).trans
    ((Anf.Pipeline.Proof.run_correct hanf).trans (Cfg.ofAnf_correct hofAnf))

/-- **The front half refines** (M2.7): for every program `Recheck.runLir`
accepts and every model region `cx_init` accepts, the lowered program
loaded into the region refines the checked source viewed at the roots'
readback types. -/
theorem front_refines {cfg : Config} {P : Src.Program} {c : Cert} {f : Front} (h : runLir cfg P c = .ok f)
    {M : Rt.Model} (hok : Rt.Proof.RegionOk M.ctx M.size) (hreg : Rt.Proof.Region M.mem M.ctx M.size) :
    Sem.Refines f.source (f.loaded M) := by
  obtain ⟨-, -, -, -, -, -, hsw, hlow⟩ := runLir_spec h
  exact (Sem.Viewed.refines (front_cfg h) f.view).trans (Rt.lower_refines hlow hsw f.tys hok hreg)

/-- **The front half refines** on a model region `cx_init` accepts whose part
Lir uses is readable and writable (`LirRegion`, from `ctx − 48`): what the
backend's entry invariant allows (the wrapper's 16 context bytes are not
Lir's). -/
theorem front_refines_lir {cfg : Config} {P : Src.Program} {c : Cert} {f : Front} (h : runLir cfg P c = .ok f)
    {M : Rt.Model} (hok : Rt.Proof.RegionOk M.ctx M.size) (hreg : Rt.Proof.LirRegion M.mem M.ctx M.size) :
    Sem.Refines f.source (f.loaded M) := by
  obtain ⟨-, -, -, -, -, -, hsw, hlow⟩ := runLir_spec h
  exact (Sem.Viewed.refines (front_cfg h) f.view).trans (Rt.lower_refines_lir hlow hsw f.tys hok hreg)

/-- `front_refines` in the traced shape (decision D-1). -/
theorem front_refines_traced {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (h : runLir cfg P c = .ok f) {M : Rt.Model} (hok : Rt.Proof.RegionOk M.ctx M.size)
    (hreg : Rt.Proof.Region M.mem M.ctx M.size) :
    Sem.TRefines f.source (f.loaded M) :=
  Sem.Refines.ofPure (front_refines h hok hreg)

/-! ## The recheck path's front half -/

/-- `runTyped` runs `runLir` first. -/
theorem runTyped_runLir {cfg : Config} {P : Src.Program} {c : Cert} {t : Typed} (h : runTyped cfg P c = .ok t) :
    ∃ f, runLir cfg P c = .ok f ∧ t.src = f.src ∧ t.checked = f.checked ∧ t.lam = f.lam ∧ t.anf = f.anf ∧
      t.fir = f.fir ∧ t.own = f.own ∧ t.cfg = f.cfg ∧ t.lowered = f.lowered ∧
      t.roots = rootsOf cfg f.src f.cfg f.lowered
        ((List.range f.src.roots.length).zip (f.src.roots.zip (f.cfg.exports.zip f.lowered.roots))) := by
  unfold runTyped at h
  cases hf : runLir cfg P c with
  | error e => rw [hf] at h; cases h
  | ok f =>
    rw [hf] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨f, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `run` runs `runLir` first: the artifact's levels are the front half's. -/
theorem run_runLir {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact} (h : run cfg P c = .ok a) :
    ∃ f, runLir cfg P c = .ok f ∧ a.src = f.src ∧ a.checked = f.checked ∧ a.lam = f.lam ∧ a.anf = f.anf ∧
      a.fir = f.fir ∧ a.own = f.own ∧ a.cfg = f.cfg ∧ a.lowered = f.lowered ∧
      a.roots = rootsOf cfg f.src f.cfg f.lowered
        ((List.range f.src.roots.length).zip (f.src.roots.zip (f.cfg.exports.zip f.lowered.roots))) := by
  unfold run at h
  cases ht : runTyped cfg P c with
  | error e => rw [ht] at h; cases h
  | ok t =>
    rw [ht] at h
    simp only [bind, Except.bind] at h
    cases hb : Backend.finish t.xl.main t.stacked t.program t.exports t.provenance with
    | error e => rw [hb] at h; cases h
    | ok b =>
      simp only [hb, Except.mapError, pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨f, hf, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := runTyped_runLir ht
      exact ⟨f, hf, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem rootsOf_get {cfg : Config} {p : Src.Program} {C : Cfg.Program} {l : Rt.Lowered} :
    ∀ {rows : List (Nat × (Ixon.Address × Src.CId) × Fir.FunId × (Lir.FunId × String))} {i : Nat} {root : Root},
      (rootsOf cfg p C l rows)[i]? = some root →
      ∃ j addr cst fx fn sym, rows[i]? = some (j, (addr, cst), fx, (fn, sym)) ∧ root.fn = fn ∧
        root.params = cfgParams C fx ∧ root.ty = rootTy p C cst := by
  intro rows
  induction rows with
  | nil => intro i root h; simp [rootsOf] at h
  | cons row rest ih =>
    obtain ⟨j, ⟨addr, cst⟩, fx, ⟨fn, sym⟩⟩ := row
    intro i root h
    cases i with
    | zero =>
      simp only [rootsOf, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨j, addr, cst, fx, fn, sym, rfl, rfl, rfl, rfl⟩
    | succ i =>
      simp only [rootsOf, List.getElem?_cons_succ] at h
      exact ih h

/-- **A root of the artifact is an entry of the loaded program**: its Lir
function, parameter count and readback type. -/
theorem rootsOf_entry {cfg : Config} {P : Src.Program} {c : Cert} {f : Front} (h : runLir cfg P c = .ok f)
    (M : Rt.Model) {i : Nat} {root : Root}
    (hr : (rootsOf cfg f.src f.cfg f.lowered
      ((List.range f.src.roots.length).zip (f.src.roots.zip (f.cfg.exports.zip f.lowered.roots))))[i]? = some root) :
    (f.loaded M).entries[i]? = some { fn := root.fn, params := root.params, ty := root.ty } := by
  obtain ⟨-, -, -, -, -, -, -, hlow⟩ := runLir_spec h
  obtain ⟨j, addr, cst, fx, fn, sym, hrow, hfn, hpar, hty⟩ := rootsOf_get hr
  simp only [List.getElem?_zip_eq_some] at hrow
  obtain ⟨-, hsrc, hex, hl⟩ := hrow
  have hfx : fn = fx := by
    have := congrArg (·[i]?) (Rt.lower_shape hlow).2
    simp only [List.getElem?_map, hl, hex, Option.map_some, Option.some.injEq] at this
    exact this
  subst hfx
  simp only [Front.loaded, Rt.Loaded.ofLowered, Rt.entriesOf_get, hl, Option.map_some, Option.some.injEq,
    Rt.Entry.mk.injEq]
  refine ⟨hfn.symm, by rw [hpar]; rfl, ?_⟩
  simp only [Front.tys, hsrc, Option.bind_some, hty]

end Compilatrix.Recheck
