import Compilatrix.Rt.Rc.Proof.LiveMemory
import Compilatrix.Own.Plain.Proof.Bounds
import Compilatrix.Lir.Proof.Steps

/-! Fresh abstract locations may reuse physical addresses of dead cells.
Old mappings remain available for stale registers; physical injectivity is a
live-cell property of HeapLive, not a property of this entire address map. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Compilatrix.Rt.Rc.Procs

def placeFresh (addresses : AddressMap) (fresh : Nat) (address : Lir.Word) : AddressMap :=
  fun location => if location = fresh then some address else addresses location

theorem placeFresh_new (addresses : AddressMap) (fresh : Nat) (address : Lir.Word) :
    valueWord (placeFresh addresses fresh address) (.loc fresh) = some address := by
  simp [valueWord, placeFresh]

theorem placeFresh_old {addresses : AddressMap} {fresh : Nat} {address : Lir.Word}
    {value : Own.RVal} (bounded : Own.Plain.Bounded fresh value) :
    valueWord (placeFresh addresses fresh address) value = valueWord addresses value := by
  cases value with
  | loc location =>
    have smaller : location < fresh := bounded
    simp [valueWord, placeFresh, Nat.ne_of_lt smaller]
  | lit literal => cases literal <;> rfl
  | ctor0 ctor => rfl
  | erased => rfl

/-- Only real source-register indices are observed. Marker dummy registers
occupy the checked disjoint range above bound. Mapped dead values may remain
in inactive registers without being interpreted as live objects. -/
def EnvWordsBelow (addresses : AddressMap) (bound : Nat) (source : Own.Env) (target : Lir.Env) : Prop :=
  ∀ x value, x < bound → source.get? x = some value →
    ∃ word, valueWord addresses value = some word ∧ target[x]? = some word

theorem EnvWordsBelow.marker {addresses : AddressMap} {bound dummy : Nat}
    {source : Own.Env} {target : Lir.Env}
    (related : EnvWordsBelow addresses bound source target) (reserved : bound ≤ dummy)
    (word : Lir.Word) : EnvWordsBelow addresses bound source (target.insert dummy word) := by
  intro x value real lookup
  obtain ⟨actual, representation, register⟩ := related x value real lookup
  refine ⟨actual, representation, ?_⟩
  rw [Lir.env_insert_ne _ word (by omega)]
  exact register

theorem EnvWordsBelow.placeFresh {addresses : AddressMap} {fresh bound : Nat}
    {source : Own.Env} {target : Lir.Env}
    (related : EnvWordsBelow addresses bound source target)
    (bounded : Own.Plain.EnvBounded fresh source) (address : Lir.Word) :
    EnvWordsBelow (placeFresh addresses fresh address) bound source target := by
  intro x value real lookup
  obtain ⟨word, representation, register⟩ := related x value real lookup
  refine ⟨word, ?_, register⟩
  rw [placeFresh_old (bounded x value lookup)]
  exact representation



end Compilatrix.Cfg.Rc.Native
