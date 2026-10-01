import Compilatrix.Recheck.Proof.Parts
import Compilatrix.Backend.Proof.Driver
import Compilatrix.Rt.Proof.ReadbackCongr
import Compilatrix.Lir.Proof.Perms
import Compilatrix.Sem.SimConst

/-!
# The backend half: the object refines the loaded Lir program (M2.7b)

`back_refines`: for an artifact `Recheck.run` returns and a driver that
keeps its contract (`X86.Driver.Ok`), the object run by the driver
(`Artifact.linked`, the object's `Lang`) refines the lowered Lir program
loaded into the driver's region (`Front.loaded (model D)`): what
`Recheck.compile_sound` called `hback`.

On input `(r, ns)` both apply root `r` the same way (`Sem.entryRun`, the
same parameter count). An exact call (`call_sim_linked`):

- `cx_init`: the loaded program's run of `cx_init` returns the same value
  at every clock (`Rt.init_correct_checked_lir`, on the part of the region
  Lir uses); the object's call of `cx_init` simulates it
  (`Backend.call_sim_export`, the wrapper's entry invariant from the
  driver's contract, `Driver.entryBase_init`);
- the root: for every memory the object's `cx_init` leaves related to
  Lir's (`Lifted StackFinal`), the invariant holds again (the budget word,
  Lir's memory inside the machine's) and the object's call of the root's
  symbol simulates the root's Lir run; the result word reads back alike
  (`Rt.readback_congr`: Lir's final memory has the part of the region Lir
  uses readable, `Lir.eval_perms`, and agrees with the object's there);
- the two compose (`Sem.Sim.bind_const`) with the clock map
  `k ↦ (B + 1)(k + 1)`, `B` the stacked program's block count;
- a `Nat` argument of 2^63 or more: the loaded program fails with
  `natOverflow`, and so does the object (the wrapper's status 3, or the
  driver for 2^64 or more) unless `cx_init` failed for a resource first.
-/

set_option autoImplicit false

namespace Compilatrix.Recheck

open Compilatrix.Sem (Result Obs Lang Sim)
open Compilatrix.X86 (Driver)
open Compilatrix.X86.ObjectEval (Lifted call call_mono)
open Compilatrix.Xv.Stacking.Proof (EntryInv mainReps)

/-- The model region of a driver: its context, region size, budget, and
Lir's memory, the part of the region Lir uses. -/
def model (D : Driver) : Rt.Model := ⟨D.ctx, D.size, D.budget, D.lirMem⟩

/-- What a related final value says: the result is one word, and the
object's memory holds Lir's bytes where Lir may read or write. -/
theorem lifted_final {vals : List X86.Word} {xm m : X86.Memory} {w : X86.Word}
    (h : Lifted Backend.StackFinal (vals, xm) (w, m)) :
    vals = [w] ∧ ∀ a, (xm.readable a = true ∨ xm.writable a = true) → m.bytes a = xm.bytes a := by
  obtain ⟨mm, holes, ⟨m₀, ⟨hv, hin, hholes⟩, hrel₀⟩, hrel⟩ := h
  refine ⟨hv, fun a ha => ?_⟩
  have hnh : ¬holes a := fun hh => by
    obtain ⟨h1, h2⟩ := hholes a hh
    rcases ha with ha | ha <;> simp_all
  rw [← hrel.bytes a hnh, ← hrel₀.bytes a hnh]
  exact hin.bytes a ha

theorem natWords_eq {ns : List Nat} {ws : List X86.Word} (h : Rt.natWords ns = some ws) :
    ws = ns.map (fun n => UInt64.ofNat n + UInt64.ofNat n + 1) ∧ ∀ n ∈ ns, n < 2 ^ 63 := by
  induction ns generalizing ws with
  | nil =>
    simp only [Rt.natWords, List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp
  | cons n ns ih =>
    simp only [Rt.natWords, List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih hws
    unfold Rt.natWord at hw
    split at hw
    · rename_i hlt
      simp only [Option.some.injEq] at hw
      subst hw
      refine ⟨?_, ?_⟩
      · rw [h1]
        simp only [List.map_cons, List.cons.injEq, and_true]
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
        have : (1 : X86.Word).toNat = 1 := rfl
        rw [this]
        omega
      · intro m hm
        rcases List.mem_cons.1 hm with rfl | hm
        · exact hlt
        · exact h2 m hm
    · cases hw

theorem natWords_none {ns : List Nat} (h : Rt.natWords ns = none) : ∃ n ∈ ns, ¬n < 2 ^ 63 := by
  induction ns with
  | nil => simp [Rt.natWords] at h
  | cons n ns ih =>
    simp only [Rt.natWords, List.mapM_cons, bind, Option.bind_eq_none_iff, pure] at h
    by_cases hn : n < 2 ^ 63
    · have hw : Rt.natWord n = some (UInt64.ofNat (2 * n + 1)) := by simp [Rt.natWord, Rt.natLimit, hn]
      have hrest : Rt.natWords ns = none := by
        cases hr : Rt.natWords ns with
        | none => rfl
        | some ws => exact absurd (h _ hw ws hr) (by simp)
      obtain ⟨m, hm, hm'⟩ := ih hrest
      exact ⟨m, List.mem_cons_of_mem _ hm, hm'⟩
    · exact ⟨n, List.mem_cons_self, hn⟩

/-- Lir's view of an entry's result is the object's: the word, read back
over memories that agree where Lir may read. -/
theorem observe_eq {D : Driver} {e : Rt.Entry} {r : X86.Linked.Root} (hty : e.ty = r.ty) (L : X86.Linked)
    (hL : L.driver = D) {vals : List X86.Word} {xm m : X86.Memory} {w : X86.Word}
    (hlift : Lifted Backend.StackFinal (vals, xm) (w, m)) (hperm : Lir.SamePerms D.lirMem xm) :
    e.observe (model D).fuel vals xm = L.observe r w m := by
  obtain ⟨hv, hbytes⟩ := lifted_final hlift
  subst hv hL
  have hsame : Rt.SameReadable xm (L.driver.lirView m) := by
    refine ⟨?_, fun a ha => (hbytes a (.inl ha)).symm⟩
    rw [hperm.1]
    rfl
  unfold Rt.Entry.observe X86.Linked.observe
  rw [hty]
  cases r.ty with
  | none => rfl
  | some st =>
    obtain ⟨sig, ty⟩ := st
    exact Rt.readback_congr hsame sig _ ty w

section Call

variable {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact} (h : run cfg P c = .ok a) {D : Driver}
  (hD : D.Ok a.backend.encoded.text.size)

/-- Root `r`'s entry of the loaded program. -/
def entryOf (a : Artifact) (r fn : Nat) : Rt.Entry := { fn, params := cfgParams a.cfg fn, ty := a.front.tys r }

/-- Root `r` of the linked object. -/
def rootOf (a : Artifact) (r fn : Nat) (sym : String) : X86.Linked.Root :=
  { symbol := sym, params := cfgParams a.cfg fn, ty := a.front.tys r }

/-- The stacked program's block count, which scales the clock. -/
abbrev Artifact.blocks (a : Artifact) : Nat := a.backend.stacked.program.blocks.size

include h hD in
/-- **An exact call of a root**: the object's call simulates the loaded Lir
program's, with the clock map `k ↦ (B + 1)(k + 1)`. -/
theorem call_sim_linked {r fn : Nat} {sym : String} (hr : a.lowered.roots[r]? = some (fn, sym))
    (ns : List Nat) (hns : ns.length = cfgParams a.cfg fn) :
    Sim Eq (fun k => (a.blocks + 1) * (k + 1))
      (fun k => (a.front.loaded (model D)).call (entryOf a r fn) ns k)
      (fun k => (a.linked D).call (rootOf a r fn sym) ns k) := by
  obtain ⟨hf, xv, hs, hv, he, hapart⟩ := run_parts h
  obtain ⟨-, -, -, -, -, -, hsw, hlow⟩ := runLir_spec hf
  have hshape := Rt.lower_shape hlow
  obtain ⟨left, mem', hinit, hpost, -⟩ :=
    Rt.init_correct_checked_lir hlow hsw (budget := D.budget) (X86.Driver.regionOk hD) (X86.Driver.lirRegion hD)
  obtain ⟨xi, hxi, hxic, hxip⟩ := run_init h hs hv
  obtain ⟨xf, hxf, hxfc, hxfp, hfn⟩ := run_root h hs hv hr
  have hlen5 : ns.length ≤ 5 := by
    rw [hns]
    have hex : a.front.cfg.exports[r]? = some fn := by
      rw [← hshape.2, List.getElem?_map]
      show Option.map _ a.lowered.roots[r]? = _
      rw [hr]; rfl
    exact runLir_params hf hex
  -- the backend configuration and its argument passing
  let bcfg := backendConfig cfg a.lowered ((a.src.roots.head?.map (·.1)).getD default) c
  have hv' : Xv.Validate.run bcfg.env xv c.alloc = .ok a.xl := hv
  have hinitEq : a.lowered.init = a.cfg.size := hshape.1
  -- `cx_init`'s call
  let core₀ := D.core [D.size, D.budget] D.initBytes
  have hinv₀ : EntryInv { a.xl with main := a.lowered.init } bcfg.reps core₀ D.ret [D.size, D.budget] D.lirMem D.ctx :=
    { toEntryBase := X86.Driver.entryBase_init hD _
      args := by
        show _ = Xv.Stacking.Proof.wrapperArgs (mainReps { a.xl with main := a.lowered.init } a.lowered.reps) core₀
        simp only [mainReps, hxi, Xv.Stacking.exportReps, Rt.Lowered.reps, beq_self_eq_true, ite_true, Option.getD_some]
        rfl
      fit := by
        show Xv.Stacking.Proof.ArgsFit (mainReps { a.xl with main := a.lowered.init } a.lowered.reps) core₀
        simp only [mainReps, hxi, Xv.Stacking.exportReps, Rt.Lowered.reps, beq_self_eq_true, ite_true, Option.getD_some]
        exact X86.Driver.argsFit_words _ }
  have hsim₀ := Backend.call_sim_export hs hv' he hapart hxi hxic [D.size, D.budget] D.lirMem D.ctx core₀ D.base D.ret
    D.flags hinv₀ hD.retOut
  have hinit' : ∀ k, Lir.eval { a.lowered.program with main := a.lowered.init } k [D.size, D.budget] D.lirMem D.ctx =
      .ok ([left], mem') := by rw [hinitEq]; exact hinit
  -- the root's call from a memory `cx_init` left
  have hreps : mainReps { a.xl with main := fn } bcfg.reps = List.replicate ns.length .nat := by
    show mainReps { a.xl with main := fn } a.lowered.reps = _
    simp only [mainReps, hxf, Xv.Stacking.exportReps, Rt.Lowered.reps, Option.getD]
    rw [ite_eq_right_iff.mpr (fun h => absurd (by simpa using h) hfn), hxfp, hns]
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
    refine Sim.ofEq (c₁ := fun k => (Lir.eval { a.lowered.program with main := a.lowered.init } k [D.size, D.budget]
        D.lirMem D.ctx).bind fun v => (Lir.eval { a.lowered.program with main := fn } k ws v.2 D.ctx).map fun v' =>
          (entryOf a r fn).observe (model D).fuel v'.1 v'.2)
      (c₂ := fun k => ((a.linked D).initCall k).bind fun v =>
        ((a.linked D).rootCall (rootOf a r fn sym) ns v.2.bytes k).map
          fun v' => (a.linked D).observe (rootOf a r fn sym) v'.1 v'.2)
      ?_ (fun k => by simp [Rt.Loaded.call, hws, Front.loaded, Rt.Loaded.ofLowered, model]; rfl)
      (fun k => by simp [X86.Linked.call, h64])
    refine Sim.bind_const hinit' (call_mono _ _ _ _ _) hsim₀ hmono fun ⟨wv, m⟩ hl => ?_
    have hinv : EntryInv { a.xl with main := fn } bcfg.reps (D.core (ns.map UInt64.ofNat) m.bytes) D.ret ws mem' D.ctx :=
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
        have hbig' : ¬Xv.Stacking.Proof.ArgsFit (mainReps { a.xl with main := fn } bcfg.reps)
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
  have hl : (a.front.loaded (model D)).entries[r]? = (a.lowered.roots[r]?).map fun p => entryOf a r p.1 := by
    simp only [Front.loaded, Rt.Loaded.ofLowered, Rt.entriesOf_get]
    rfl
  have hlr : (a.linked D).roots[r]? = (a.lowered.roots[r]?).map fun p => rootOf a r p.1 p.2 := by
    simp only [Artifact.linked, Artifact.linkedRoots, List.getElem?_map, List.getElem?_zipIdx]
    cases a.lowered.roots[r]? <;> simp [rootOf, Front.tys] <;> rfl
  simp only [hl, hlr]
  cases hr : a.lowered.roots[r]? with
  | none => exact Sim.of_stuck
  | some p =>
    obtain ⟨fn, sym⟩ := p
    simp only [Option.map_some]
    have hcs : ∀ ns' : List Nat, ns'.length = cfgParams a.cfg fn → _ :=
      fun ns' hns' => call_sim_linked h hD hr ns' hns'
    show Sim Eq _ (fun k => Sem.entryRun (cfgParams a.cfg fn) none ((a.front.loaded (model D)).call (entryOf a r fn)) ns k)
      (fun k => Sem.entryRun (cfgParams a.cfg fn) none ((a.linked D).call (rootOf a r fn sym)) ns k)
    unfold Sem.entryRun
    by_cases he : ns.length = cfgParams a.cfg fn
    · simp only [he, ↓reduceIte]
      exact hcs ns he
    · by_cases hlt : ns.length < cfgParams a.cfg fn
      · simp only [he, hlt, ↓reduceIte]
        by_cases hn : ns = []
        · simp only [hn, ↓reduceIte]
          exact Sim.okConst rfl
        · simp only [hn, ↓reduceIte]
          exact Sim.laterConst rfl fun k hk => absurd hk (Nat.mul_ne_zero (by omega) (by omega))
      · simp only [he, hlt, ↓reduceIte]
        exact Sim.bindStuck (hcs (ns.take (cfgParams a.cfg fn)) (by simp only [List.length_take]; omega))
          fun _ _ _ => rfl

end Call

end Compilatrix.Recheck
