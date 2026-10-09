import Compilatrix.Recheck.Rc.Proof.Exports
import Compilatrix.Recheck.Rc.Proof.Roots
import Compilatrix.Recheck.Rc.Linked
import Compilatrix.Cfg.Rc.Proof.Physical.PublicInit
import Compilatrix.Recheck.Proof.Back

/-! The emitted RC object simulates the actual public Lir program. This uses
existing backend selection, allocation, stacking, encoding and ELF proofs,
with the actual RC initializer and raw-word export configuration. -/
set_option autoImplicit false
namespace Compilatrix.Recheck.RcReplay
open Compilatrix.Sem (Result Obs Lang Sim)
open Compilatrix.X86 (Driver)
open Compilatrix.X86.ObjectEval (Lifted call call_mono)
open Compilatrix.Xv.Stacking.Proof (EntryInv mainReps)

section Call

variable {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact} (h : run cfg P c = .ok a) {D : Driver}
  (hD : D.Ok a.backend.encoded.text.size)

/-- Root `r`'s entry of the loaded program. -/
def entryOf (a : Artifact) (r fn : Nat) : Rt.Entry := { fn, params := cfgParams a.front.cfg.base fn, ty := a.front.tys r }

/-- Root `r` of the linked object. -/
def rootOf (a : Artifact) (r fn : Nat) (sym : String) : X86.Linked.Root :=
  { symbol := sym, params := cfgParams a.front.cfg.base fn, ty := a.front.tys r }

/-- The stacked program's block count, which scales the clock. -/
abbrev Artifact.blocks (a : Artifact) : Nat := a.backend.stacked.program.blocks.size

include h hD in
/-- **An exact call of a root**: the object's call simulates the loaded Lir
program's, with the clock map `k ↦ (B + 1)(k + 1)`. -/
theorem call_sim_linked {r fn : Nat} {sym : String} (hr : a.front.lowered.roots[r]? = some (fn, sym))
    (ns : List Nat) (hns : ns.length = cfgParams a.front.cfg.base fn) :
    Sim Eq (fun k => (a.blocks + 1) * (k + 1))
      (fun k => (a.front.loaded (model D)).call (entryOf a r fn) ns k)
      (fun k => (a.linked D).call (rootOf a r fn sym) ns k) := by
  obtain ⟨hf, xv, xl, hs, hv, he, hapart⟩ := run_parts h
  have hlow := (runFront_native hf).2
  have hshape := public_roots hlow
  obtain ⟨left, mem', base, limit, hinit, hpost, _⟩ :=
    Cfg.Rc.Public.Spec.initialize_heap hlow [] (budget := D.budget)
      (X86.Driver.regionOk hD) (X86.Driver.lirRegion hD)
  obtain ⟨xi, hxi, hxic, hxip, initReps⟩ := run_init h hs hv
  obtain ⟨xf, hxf, hxfc, hxfp, hfn, notDrop, rootReps⟩ := run_root h hs hv hr
  have hlen5 : ns.length ≤ 5 := by
    rw [hns]
    have hex : a.front.cfg.base.exports[r]? = some fn := by
      rw [← hshape, List.getElem?_map]
      show Option.map _ a.front.lowered.roots[r]? = _
      rw [hr]; rfl
    exact runFront_params hf hex
  -- the backend configuration and its argument passing
  let bcfg := emittedConfig cfg a.front c.base
  have hv' : Xv.Validate.run bcfg.env xv c.base.alloc = .ok xl := hv
  -- `cx_init`'s call
  let core₀ := D.core [D.size, D.budget] D.initBytes
  have hinv₀ : EntryInv { xl with main := a.front.lowered.init } bcfg.reps core₀ D.ret [D.size, D.budget] D.lirMem D.ctx :=
    { toEntryBase := X86.Driver.entryBase_init hD _
      args := by
        show _ = Xv.Stacking.Proof.wrapperArgs (mainReps { xl with main := a.front.lowered.init } bcfg.reps) core₀
        simp only [mainReps, hxi, Xv.Stacking.exportReps, show bcfg.reps a.front.lowered.init = some [.word, .word] from initReps, Option.getD_some]
        rfl
      fit := by
        show Xv.Stacking.Proof.ArgsFit (mainReps { xl with main := a.front.lowered.init } bcfg.reps) core₀
        simp only [mainReps, hxi, Xv.Stacking.exportReps, show bcfg.reps a.front.lowered.init = some [.word, .word] from initReps, Option.getD_some]
        exact X86.Driver.argsFit_words _ }
  have hsim₀ := Backend.call_sim_export hs hv' he hapart hxi hxic [D.size, D.budget] D.lirMem D.ctx core₀ D.base D.ret
    D.flags hinv₀ hD.retOut
  have hinit' : ∀ k, Lir.eval { a.front.lowered.program with main := a.front.lowered.init } k [D.size, D.budget] D.lirMem D.ctx =
      .ok ([left], mem') := hinit
  -- the root's call from a memory `cx_init` left
  have hreps : mainReps { xl with main := fn } bcfg.reps = List.replicate ns.length .nat := by
    show mainReps { xl with main := fn } bcfg.reps = _
    simp only [mainReps, hxf, Xv.Stacking.exportReps,
      show bcfg.reps fn = none from rootReps, Option.getD_none]
    rw [hxfp, hns]
  have hbase : ∀ (wv : X86.Word) (m : X86.Memory), Lifted Backend.StackFinal ([left], mem') (wv, m) →
      Xv.Stacking.Proof.EntryBase (D.core (ns.map UInt64.ofNat) m.bytes) D.ret mem' D.ctx := by
    intro wv m hl
    obtain ⟨-, hbytes⟩ := lifted_final hl
    have hr' : mem'.readable = D.inLir := hpost.readable
    have hw' : mem'.writable = D.inLir := hpost.writable
    refine X86.Driver.entryBase hD _ (fun i hi => ?_) hr' hw' (fun x hx => (hbytes x (.inl (by rw [hr']; exact hx))).symm)
    rw [hbytes _ (.inl (hpost.budget.readable i hi))]
    exact hpost.budget.bytes i hi
  have hmono : ∀ v : X86.Word × X86.Memory, Sem.ClockMono (fun k => ((a.linked D).rootCall (rootOf a r fn sym) ns v.2.bytes k).map fun v' => (a.linked D).observe
        (rootOf a r fn sym) v'.1 v'.2) :=
    fun _ => Sem.ClockMono.bind (call_mono _ _ _ _ _) fun _ => Sem.ClockMono.const _
  cases hws : Rt.natWords ns with
  | some ws =>
    obtain ⟨hwsEq, hlt⟩ := natWords_eq hws
    have h64 : ns.all (· < 2 ^ 64) = true := List.all_eq_true.2 fun n hn => by
      have := hlt n hn; simp only [decide_eq_true_eq]; omega
    refine Sim.ofEq (c₁ := fun k => (Lir.eval { a.front.lowered.program with main := a.front.lowered.init } k [D.size, D.budget]
        D.lirMem D.ctx).bind fun v => (Lir.eval { a.front.lowered.program with main := fn } k ws v.2 D.ctx).map fun v' =>
          (entryOf a r fn).observe (model D).fuel v'.1 v'.2)
      (c₂ := fun k => ((a.linked D).initCall k).bind fun v =>
        ((a.linked D).rootCall (rootOf a r fn sym) ns v.2.bytes k).map
          fun v' => (a.linked D).observe (rootOf a r fn sym) v'.1 v'.2)
      ?_ (fun k => by simp [Rt.Loaded.call, hws, Front.loaded, Rt.Loaded.ofLowered, model]; rfl)
      (fun k => by simp [X86.Linked.call, h64])
    refine Sim.bind_const hinit' (call_mono _ _ _ _ _) hsim₀ hmono fun ⟨wv, m⟩ hl => ?_
    have hinv : EntryInv { xl with main := fn } bcfg.reps (D.core (ns.map UInt64.ofNat) m.bytes) D.ret ws mem' D.ctx :=
      { toEntryBase := hbase wv m hl
        args := by rw [hreps, X86.Driver.wrapperArgs_nat hlen5, hwsEq]
        fit := by rw [hreps]; exact (X86.Driver.argsFit_nat hlen5 (fun n hn => by have := hlt n hn; omega) _).2 hlt }
    have hsim₁ := (Backend.call_sim_export hs hv' he hapart hxf hxfc ws mem' D.ctx _ D.base D.ret D.flags hinv
      hD.retOut).and_source (P := fun v => Lir.SamePerms mem' v.2) fun k v hk => Lir.eval_perms hk
    refine hsim₁.map_eq fun v w hvw => ?_
    obtain ⟨hlift, hperm⟩ := hvw
    have hperm' : Lir.SamePerms D.lirMem v.2 := ⟨hperm.1.trans hpost.readable, hperm.2.trans hpost.writable⟩
    exact observe_eq rfl (a.linked D) rfl hlift hperm'
  | none =>
    obtain ⟨n, hn, hbig⟩ := natWords_none hws
    have hsrc : ∀ k, (a.front.loaded (model D)).call (entryOf a r fn) ns k =
        .resource .natOverflow := fun k => by simp [Rt.Loaded.call, hws]
    refine Sim.ofEq (c₁ := fun _ => .resource .natOverflow) ?_ hsrc (fun _ => rfl)
    by_cases h64 : ns.all (· < 2 ^ 64) = true
    · have h64' : ∀ n ∈ ns, n < 2 ^ 64 := fun n hn => by simpa using List.all_eq_true.1 h64 n hn
      have hcall : ∀ k, (a.linked D).call (rootOf a r fn sym) ns k =
          ((a.linked D).initCall k).bind fun v =>
            ((a.linked D).rootCall (rootOf a r fn sym) ns v.2.bytes k).map
              fun v' => (a.linked D).observe (rootOf a r fn sym) v'.1 v'.2 :=
        fun k => by simp [X86.Linked.call, h64]
      obtain ⟨k₀, hr₀⟩ := hsim₀.forward 0 (by rw [hinit']; simp)
      rw [hinit'] at hr₀
      change Result.Refines _ _ ((a.linked D).initCall k₀) at hr₀
      generalize hb₀ : (a.linked D).initCall k₀ = t at hr₀
      cases hr₀ with
      | resource fl => exact Sim.of_eventually_resource (k₀ := k₀) (fl := fl) (by rw [hcall, hb₀]; rfl)
      | ok hl =>
        rename_i w
        obtain ⟨wv, m⟩ := w
        have hbig' : ¬Xv.Stacking.Proof.ArgsFit (mainReps { xl with main := fn } bcfg.reps)
            (D.core (ns.map UInt64.ofNat) m.bytes) := by
          rw [hreps, X86.Driver.argsFit_nat hlen5 h64' _]
          exact fun hall => hbig (hall n hn)
        obtain ⟨k₁, hk₁⟩ := Backend.call_overflow_export he hapart hxf hxfc D.flags (hbase wv m hl) hbig' hD.retOut
        refine Sim.of_eventually_resource (k₀ := max k₀ k₁) (fl := .natOverflow) ?_
        have hb₀' : call a.backend.object Rt.Procs.initSymbol D.base core₀ D.flags k₀ = .ok (wv, m) := hb₀
        have hi : (a.linked D).initCall (max k₀ k₁) = .ok (wv, m) := by
          show call a.backend.object Rt.Procs.initSymbol D.base core₀ D.flags (max k₀ k₁) = _
          rw [call_mono _ _ _ _ _ (Nat.le_max_left _ _) (by rw [hb₀']; simp)]
          exact hb₀'
        have hroot : (a.linked D).rootCall (rootOf a r fn sym) ns m.bytes
            (max k₀ k₁) = .resource .natOverflow := by
          show call a.backend.object sym D.base (D.core (ns.map UInt64.ofNat) m.bytes) D.flags (max k₀ k₁) = _
          rw [call_mono _ _ _ _ _ (Nat.le_max_right _ _) (by rw [hk₁]; simp)]
          exact hk₁
        rw [hcall, hi, Result.bind_ok, hroot]
        rfl
    · exact Sim.of_eventually_resource (k₀ := 0) (fl := .natOverflow) (by simp [X86.Linked.call, h64])

include h hD in
/-- **The backend half** (`hback`, M2.7b): for an artifact `Recheck.run`
returns, the object run by a driver that keeps its contract refines the
lowered Lir program loaded into the driver's region. -/
theorem back_refines : Sem.Refines (a.front.loaded (model D)) (a.linked D) := by
  refine Sem.Refines.of_sim (R := Eq) (fun _ _ h => h) fun ⟨r, ns⟩ => ⟨fun k => (a.blocks + 1) * (k + 1), ?_⟩
  show Sim Eq _ ((a.front.loaded (model D)).run (r, ns)) ((a.linked D).run (r, ns))
  unfold Rt.Loaded.run X86.Linked.run
  have hl : (a.front.loaded (model D)).entries[r]? = (a.front.lowered.roots[r]?).map fun p => entryOf a r p.1 := by
    simp only [Front.loaded, Rt.Loaded.ofLowered, Rt.entriesOf_get]
    rfl
  have hlr : (a.linked D).roots[r]? = (a.front.lowered.roots[r]?).map fun p => rootOf a r p.1 p.2 := by
    simp only [Artifact.linked, Artifact.linkedRoots, List.getElem?_map, List.getElem?_zipIdx]
    cases a.front.lowered.roots[r]? <;> simp [rootOf, Front.tys] <;> rfl
  simp only [hl, hlr]
  cases hr : a.front.lowered.roots[r]? with
  | none => exact Sim.of_stuck
  | some p =>
    obtain ⟨fn, sym⟩ := p
    simp only [Option.map_some]
    have hcs : ∀ ns' : List Nat, ns'.length = cfgParams a.front.cfg.base fn → _ :=
      fun ns' hns' => call_sim_linked h hD hr ns' hns'
    show Sim Eq _ (fun k => Sem.entryRun (cfgParams a.front.cfg.base fn) none ((a.front.loaded (model D)).call (entryOf a r fn)) ns k)
      (fun k => Sem.entryRun (cfgParams a.front.cfg.base fn) none ((a.linked D).call (rootOf a r fn sym)) ns k)
    unfold Sem.entryRun
    by_cases he : ns.length = cfgParams a.front.cfg.base fn
    · simp only [he, ↓reduceIte]
      exact hcs ns he
    · by_cases hlt : ns.length < cfgParams a.front.cfg.base fn
      · simp only [he, hlt, ↓reduceIte]
        by_cases hn : ns = []
        · simp only [hn, ↓reduceIte]
          exact Sim.okConst rfl
        · simp only [hn, ↓reduceIte]
          exact Sim.laterConst rfl fun k hk => absurd hk (Nat.mul_ne_zero (by omega) (by omega))
      · simp only [he, hlt, ↓reduceIte]
        exact Sim.bindStuck (hcs (ns.take (cfgParams a.front.cfg.base fn)) (by simp only [List.length_take]; omega))
          fun _ _ _ => rfl



end Call

end Compilatrix.Recheck.RcReplay
