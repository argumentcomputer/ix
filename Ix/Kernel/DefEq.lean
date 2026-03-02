/-
  Kernel DefEq: Definitional equality with lazy delta reduction.

  Uses ReducibilityHints to guide delta unfolding order.
  Handles proof irrelevance, eta expansion, structure eta.
-/
import Ix.Kernel.Whnf

namespace Ix.Kernel

/-! ## Helpers -/

/-- Compare two arrays of levels for equality. -/
def equalUnivArrays (us us' : Array (Level m)) : Bool :=
  us.size == us'.size && Id.run do
    let mut i := 0
    while i < us.size do
      if !Level.equalLevel us[i]! us'[i]! then return false
      i := i + 1
    return true

/-- Check if two expressions have the same const head. -/
def sameHeadConst (t s : Expr m) : Bool :=
  match t.getAppFn, s.getAppFn with
  | .const a _ _, .const b _ _ => a == b
  | _, _ => false

/-- Unfold a delta-reducible definition one step. -/
def unfoldDelta (ci : ConstantInfo m) (e : Expr m) : Option (Expr m) :=
  match ci with
  | .defnInfo v =>
    let levels := e.getAppFn.constLevels!
    let body := v.value.instantiateLevelParams levels
    some (body.mkAppN (e.getAppArgs))
  | .thmInfo v =>
    let levels := e.getAppFn.constLevels!
    let body := v.value.instantiateLevelParams levels
    some (body.mkAppN (e.getAppArgs))
  | _ => none

end Ix.Kernel
