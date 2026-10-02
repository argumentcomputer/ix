/-
Extracted unchanged from Ix/IxonUniv.lean at Ix revision
11aa5649700b371e1c65dcb86157999839fe7e5e. The frozen ingress smart-constructor
rules are shared by host normalization and canonical block comparison.
-/

module
public import Ix.Ixon.Types

public section
@[expose] section

namespace Ixon

namespace Univ

/-- Constructor count — termination measure for the normalization
    family (mirrors `Ix.Tc.KUniv.size`). -/
def size : Univ → Nat
  | .zero => 1
  | .succ u => u.size + 1
  | .max a b => a.size + b.size + 1
  | .imax a b => a.size + b.size + 1
  | .var _ => 1

theorem size_pos (u : Univ) : 0 < u.size := by
  cases u <;> simp [size]

/-- True if this level is an explicit numeral `succ^n zero`. -/
def isExplicit : Univ → Bool
  | .zero => true
  | .succ u => u.isExplicit
  | _ => false

/-- True if this level is nonzero under every parameter assignment. -/
def isNeverZero : Univ → Bool
  | .succ _ => true
  | .max a b => a.isNeverZero || b.isNeverZero
  | .imax _ b => b.isNeverZero
  | _ => false

/-- Peel the outermost constant offset: `(base, n)` with
    `u = succ^n base`, `base` not a `succ`. -/
def offset : Univ → Univ × UInt64
  | .succ u => let (base, n) := u.offset; (base, n + 1)
  | u => (u, 0)

/-- `succ^n u`. -/
def addSuccs (u : Univ) : Nat → Univ
  | 0 => u
  | n + 1 => .succ (addSuccs u n)

end Univ

/-- `mkMax` of the frozen kernel rule set (M1–M8), on `Ixon.Univ`:
    numerals → the larger (ties → `a`); `max a a = a`; zero sides;
    absorption; same-base offsets; raw. Mirrors `Ix.Tc.KUniv.mkMax` /
    Rust `canon_univ::n_max`. -/
def nMax (a b : Univ) : Univ :=
  if a.isExplicit && b.isExplicit then
    let (_, na) := a.offset
    let (_, nb) := b.offset
    if na ≥ nb then a else b
  else if a == b then a
  else if a matches .zero then b
  else if b matches .zero then a
  else
    let absorbB := match b with
      | .max bl br => bl == a || br == a
      | _ => false
    if absorbB then b
    else
      let absorbA := match a with
        | .max al ar => al == b || ar == b
        | _ => false
      if absorbA then a
      else
        let (baseA, offA) := a.offset
        let (baseB, offB) := b.offset
        if baseA == baseB then
          if offA ≥ offB then a else b
        else .max a b

/-- `mkIMax` of the frozen kernel rule set (I1–I6), on `Ixon.Univ`. -/
def nIMax (a b : Univ) : Univ :=
  if b.isNeverZero then nMax a b
  else if b matches .zero then b
  else if a matches .zero then b
  else
    let aIsOne := match a with
      | .succ .zero => true
      | _ => false
    if aIsOne then b
    else if a == b then a
    else .imax a b

/-- The kernel-rebuild closure on stored trees: bottom-up rebuild through
    the simplifying constructors — exactly what anon/meta ingress does.
    A non-fixpoint entry reaches the kernel changed (the stage-1
    decoration-presence test); P6 pins that this rebuild refines into
    the Géran classes. `tc-unit` pins agreement with
    `Ix.Tc.reduceIxonUniv` (the same closure via the kernel's own
    constructors). -/
def reduceUniv : Univ → Univ
  | .zero => .zero
  | .var i => .var i
  | .succ i => .succ (reduceUniv i)
  | .max a b => nMax (reduceUniv a) (reduceUniv b)
  | .imax a b => nIMax (reduceUniv a) (reduceUniv b)

end Ixon

end
