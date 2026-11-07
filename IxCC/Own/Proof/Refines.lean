import IxCC.Own.Proof.Immortal
import IxCC.Sem.TracedSim

/-! # `Own.immortal_refines`

The Phase 1 Own refinement (design note 03 §4.4, phase1 M2.4): a Fir
program's immortal embedding `Own.immortal F`, run under the immortal
policy, simulates `F` with the **identity** clock map, in lock step at every
clock (`Own.Proof.lock`). The result relation `ImmRes H`: the Own value
denotes the Fir value in the final heap (`Heap.value?`), the final heap is
immortal (`Heap.immortalOk`) and extends the initial one. So the Own
readback is Fir's (`readback_den`). By `checkImmortal_iff`, the same holds
for every Own program the Phase 1 checker accepts, against its erasure
(`checked_refines`). The traced form (decision D-1) follows by
`TSim.ofPure`. -/

set_option autoImplicit false

namespace IxCC.Own

open IxCC.Sem (Result Sim TSim Forall2)
open IxCC.Fir (FunId)
open IxCC.Own.Proof

/-- The result relation of the Fir → Own refinement from heap `H`: the Own
value denotes the Fir value in the final heap, which is immortal and
extends `H`. -/
def ImmRes (H : Heap) (w : Fir.Val) (p : RVal × Heap) : Prop :=
  Den p.2 p.1 w ∧ p.2.immortalOk = true ∧ Ext H p.2

/-- A denoting value reads back as the Fir value. -/
theorem readback_den {H : Heap} {v : RVal} {w : Fir.Val} (h : Den H v w) :
    H.readback v = Fir.readback w := by
  simp only [Heap.readback, show H.value? v = some w from h, Option.bind_some]

/-- **`Own.immortal_refines`** (03 §4.4, M2.4): for a Fir program whose
`Bool` pins have no fields where its table lists them, its immortal
embedding simulates it with the identity clock map, from every immortal
heap and denoting arguments. -/
theorem immortal_refines {F : Fir.Program} (hb : BoolsOk F) (f : FunId) {H : Heap}
    (hH : H.immortalOk = true) {vs : List RVal} {ws : List Fir.Val} (hds : Forall2 (Den H) vs ws) :
    Sim (ImmRes H) id (fun k => Fir.run F k f ws) (fun k => run .immortal (immortal F) k f vs H) where
  forward k hk := by
    refine ⟨k, ?_⟩
    have hl := run_lock hb k f hH hds
    generalize Fir.run F k f ws = r at hl hk
    generalize run .immortal (immortal F) k f vs H = s at hl
    cases hl with
    | ok hd hok hx => exact .ok ⟨hd, hok, hx⟩
    | timeout => exact absurd rfl hk
    | trap => exact .trap
    | resource fl => exact .resource fl
    | stuck => exact .stuck
  timeout k hk := by
    have hl := run_lock hb k f hH hds
    simp only [id] at hk
    rw [hk] at hl
    generalize run .immortal (immortal F) k f vs H = s at hl ⊢
    cases hl
    exact .inl rfl

/-- `Own.immortal_refines` in the traced shape (decision D-1). -/
theorem immortal_refines_traced {Env E : Type} {F : Fir.Program} (hb : BoolsOk F) (f : FunId) {H : Heap}
    (hH : H.immortalOk = true) {vs : List RVal} {ws : List Fir.Val} (hds : Forall2 (Den H) vs ws) :
    TSim (Env := Env) (E := E) (ImmRes H) id (fun _ k => Sem.Traced.lift (Fir.run F k f ws))
      (fun _ k => Sem.Traced.lift (run .immortal (immortal F) k f vs H)) :=
  TSim.ofPure (immortal_refines hb f hH hds)

/-- Every Own program the Phase 1 checker accepts simulates its erasure. -/
theorem checked_refines {q : Program} (hc : checkImmortal q = true) (hb : BoolsOk (erase q)) (f : FunId)
    {H : Heap} (hH : H.immortalOk = true) {vs : List RVal} {ws : List Fir.Val} (hds : Forall2 (Den H) vs ws) :
    Sim (ImmRes H) id (fun k => Fir.run (erase q) k f ws) (fun k => run .immortal q k f vs H) := by
  have := immortal_refines hb f hH hds
  rwa [(checkImmortal_iff q).1 hc] at this

end IxCC.Own
