import Compilatrix.Rt.Proof.Correct
import Compilatrix.Rt.Proof.Readback
import Compilatrix.Rt.Proof.CxInit
import Compilatrix.Sem.TracedSim

/-!
# M2.5's published theorems

`Rt.lower_correct` (06 S32): the runtime lowering simulates Cfg's immortal
semantics, clock map `k ↦ k + 1` at the level of `Cfg.run` and `Lir.eval`.
`Rt.lower_correct_traced`: the same in the traced vocabulary of decision
D-1, for every environment and event type (`TSim.ofPure`).
`Rt.readback_sound`: the runtime readback of a related result word is
Own's readback of the value. `Rt.result_readback`: what the two together
give for a final result. `Rt.init_correct`: the lowered program's
`cx_init` (`Rt.Proof.cxInit_ok`) establishes the heap invariant
`Rt.lower_correct` starts from, for the empty heap.

A `Transform.lift` corollary needs `Lang` instances for Cfg and Lir (an
input type both programs run on and the observation of their values); the
end-to-end theorem (M2.7) fixes that binding.
-/

set_option autoImplicit false

namespace Compilatrix.Rt

open Compilatrix.Lir (Word)
open Compilatrix.Rt.Proof

/-- **`Rt.lower_correct`** (see `Rt.Proof.lower_correct`). -/
theorem lower_correct {cfg : Config} {P : Cfg.Program} {L : Lowered} (h : lower cfg P = .ok L) {g : Nat}
    {args : List Own.RVal} {H : Own.Heap} {ws : List Word} {mem : X86.Memory} {ctx : Word} {Pw : List Word}
    (hargs : ListRel (ValRel (Lower.tables P) Pw) args ws) (hheap : HeapInv (Lower.tables P) Pw H ctx mem)
    (hsafe : ∀ s, Reach P (.call g args [] H) s → SwitchOk P s) :
    Sem.Sim (Res P ctx) (· + 1) (fun k => Cfg.run .immortal P k g args H)
      (fun k => Lir.eval { L.program with main := g } k ws mem ctx) :=
  Proof.lower_correct h hargs hheap hsafe

/-- **`Rt.lower_correct`, traced** (D-1): for every environment and event
type. -/
theorem lower_correct_traced {Env E : Type} {cfg : Config} {P : Cfg.Program} {L : Lowered}
    (h : lower cfg P = .ok L) {g : Nat} {args : List Own.RVal} {H : Own.Heap} {ws : List Word}
    {mem : X86.Memory} {ctx : Word} {Pw : List Word}
    (hargs : ListRel (ValRel (Lower.tables P) Pw) args ws) (hheap : HeapInv (Lower.tables P) Pw H ctx mem)
    (hsafe : ∀ s, Reach P (.call g args [] H) s → SwitchOk P s) :
    Sem.TSim (Env := Env) (E := E) (Res P ctx) (· + 1)
      (fun _ k => Sem.Traced.lift (Cfg.run .immortal P k g args H))
      (fun _ k => Sem.Traced.lift (Lir.eval { L.program with main := g } k ws mem ctx)) :=
  Sem.TSim.ofPure (lower_correct h hargs hheap hsafe)

/-- **`Rt.readback_sound`** (see `Rt.Proof.readback_sound`). -/
theorem readback_sound {T : Lower.Tables} {P : List Word} {H : Own.Heap} {ctx : Word} {m : X86.Memory}
    {sig : Sig} {ty : FoTy} {v : Own.RVal} {w : Word} (hheap : HeapInv T P H ctx m) (hty : Typed sig H ty v)
    (hrel : ValRel T P v w) : readback sig (H.size + 1) m ty w = H.readback v :=
  Proof.readback_sound hheap hty hrel

/-- A final result related by `Res` reads back as Cfg's. -/
theorem result_readback {P : Cfg.Program} {ctx : Word} {v : Own.RVal} {H : Own.Heap} {vals : List Word}
    {m : X86.Memory} (hres : Res P ctx (v, H) (vals, m)) {sig : Sig} {ty : FoTy} (hty : Typed sig H ty v) :
    ∃ w, vals = [w] ∧ readback sig (H.size + 1) m ty w = H.readback v := by
  obtain ⟨Pw, w, hw, hrel, hheap⟩ := hres
  exact ⟨w, hw, readback_sound hheap hty hrel⟩

/-- `Rt.lower` places `cx_init` right after the program's functions. -/
theorem lower_cxInit {cfg : Config} {P : Cfg.Program} {L : Lowered} (h : lower cfg P = .ok L) :
    L.program.funcs[P.size]? = some Procs.cxInit := by
  obtain ⟨funcs, hfs, hprog, -⟩ := Proof.lower_spec h
  obtain ⟨hlen, -⟩ := Proof.functions_spec hfs
  rw [hprog, List.getElem?_toArray, List.getElem?_append_right (by simp [hlen])]
  simp [hlen]

/-- **`cx_init`, then `Rt.lower_correct` from the empty heap**: on a
readable and writable region its checks accept, the lowered program's
`cx_init` returns at every clock with memory over which every function runs
as Cfg's from the empty heap, on arguments related without cells. -/
theorem init_correct {cfg : Config} {P : Cfg.Program} {L : Lowered} (h : lower cfg P = .ok L)
    {size budget ctx : Word} {mem : X86.Memory} (hok : RegionOk ctx size) (hreg : Region mem ctx size) :
    ∃ left mem', (∀ k, Lir.eval { L.program with main := P.size } k [size, budget] mem ctx = .ok ([left], mem')) ∧
      InitPost ctx budget mem mem' ∧
      ∀ {g : Nat} {args : List Own.RVal} {ws : List Word}, ListRel (ValRel (Lower.tables P) []) args ws →
        (∀ s, Reach P (.call g args [] { cells := #[] }) s → SwitchOk P s) →
        Sem.Sim (Res P ctx) (· + 1) (fun k => Cfg.run .immortal P k g args { cells := #[] })
          (fun k => Lir.eval { L.program with main := g } k ws mem' ctx) := by
  obtain ⟨left, mem', hrun, hpost⟩ := cxInit_ok (lower_cxInit h) (budget := budget) hok hreg
  exact ⟨left, mem', hrun, hpost, fun hargs hsafe => lower_correct h hargs (hpost.heap _) hsafe⟩

end Compilatrix.Rt
