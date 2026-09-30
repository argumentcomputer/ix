/-! # Ownership vocabulary

Parameter modes and value kinds of the Own IR (design note
`plans/x86-v2/03-ownership.md` §3.1). They live below Fir because Fir's
constructor info records a kind per field (`Fir.CtorInfo.fieldKinds`, from
v3 field contracts, default `shared`).

In the Phase 1 fragment (03 §4.4) every kind is `shared` and every mode
`owned`; kinds and modes are recorded, and no step depends on them. -/

namespace Compilatrix.Own

/-- How a parameter is passed. `borrowed esc`: `esc = false` is a local view
(no `inc`, store or return). -/
inductive Mode where
  | owned
  | borrowed (esc : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- A value kind. `unique dup`: `dup = false` holds non-duplicable fields and
is never frozen; `region`: the current frame's region (tier 2, OWN-5). -/
inductive Kind where
  | shared
  | unique (dup : Bool)
  | region
  deriving DecidableEq, Repr, Inhabited

end Compilatrix.Own
