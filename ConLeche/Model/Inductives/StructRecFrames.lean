module

public import ConLeche.Model.Inductives.StructRecRead
public section

/-!
# The recursor's frames (task #175 W4c, P3 module 6, part 13; S2)

`recFrames`: at every parameter valuation the recursor's post-parameter
phase facts hold — `RecBase`: the field chain graded, the motive
binder the Π over the carrier into the elimination sort, the minor
binder the minor space, the major binder the carrier.  Since task
#175 S2 the recursor type is the *generated* one, whose binder data
is `recDataAV`: its parameter entries are the type former's (so the
parameter frames coincide outright), and its three special entries are
spelled out, so every clause of `RecBase` is a **computation** on the
readings — `famSpine_val` for the carrier, `interp_minorSp_of_tele`
for the minor space, the constructor leaf's fold for its core.  The
gradings of the entries come from the opened type's record
(`Opened.okΓ`, the fabricated type's own inference run).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps StructParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Frame arithmetic -/

/-! ## The generated data, by position -/

section Data
variable {m : EnvModel V env} {T C : Name} {ψ : Name → Nat} {nP nF : Nat} {ℓ : Level}
  {pps ds : List (Nat × Nat × AnnotTerm)}

end Data

/-- The field chain's entry `j`. -/
theorem fields_getD {ds : List (Nat × Nat × AnnotTerm)} {nP j : Nat}
    (hj : j < (ds.drop nP).length) :
    (((ds.drop nP).map (·.2.2))).getD j default = ((ds.drop nP).getD j default).2.2 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
    Option.map_some, Option.getD_some]

/-! ## The frames -/

end ConLeche.Model
