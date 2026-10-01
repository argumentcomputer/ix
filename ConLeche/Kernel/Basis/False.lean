module

public import ConLeche.Kernel.Basis.Builder

@[expose] public section

/-!
# The pinned `False` basis block (task #181)

The raw pin — the `False` block exactly as an export carries it: the
toolchain's `Init.Prelude` declaration, no constructors, hence no iota
rules, at the parser's raw binder annotations.  It is the `Empty` pin
(`ConLeche/Kernel/Basis/Empty.lean`) one universe down: `False : Prop`
where `Empty : Type`, and `False.rec` eliminates into every `Sort u`
exactly as `Empty.rec` does (the official kernel lets a
zero-constructor `Prop` eliminate large).

**Why a pin, when the direct sum route installs any zero-constructor
inductive natively (task #175, `n ≠ 1`)?**  So that the consistency
corollary about `False` — `no_proof_of_False_pure`, the statement the
project exists to make — carries no hypothesis about how the stream
declared `False`.  A pinned name cannot be redeclared (the frontend
matches the incoming block against this pin and the recognisers reject
reserved names), so "no constant of type `False`" is a theorem about
the accepted environment alone, exactly as for `Empty`.  The *value*
is the empty set in both cases; `False`'s lives in `Prop`, where the
empty set is the false proposition.

The *annotated* forms (`falseA`, `falseRecA`) are computed from these
by the checker's own annotation pass at elaboration time; see
`ConLeche/Kernel/BasisA.lean`.
-/

namespace ConLeche

open BasisDSL

/-- `False : Prop`. -/
def falseRaw : ConstantInfo :=
  .indInfo ⟨falseName, [], prop⟩ {}

/-- `False.rec.{u} (motive : False → Sort u) (t : False) : motive t`.
The exporter emits the motive as an *explicit* binder here (there is
no major premise to infer it from), as for `Empty.rec`. -/
def falseRecRaw : ConstantInfo :=
  .recInfo ⟨falseName.str "rec", [uN],
    pi "motive" (pi "t" (cnst falseName) (srt u)) <|
    pi "t" (cnst falseName) (.app (bv 1) (bv 0))⟩
    1 1 []

/-- The pinned `False` basis block, in install order. -/
def falseBasis : List ConstantInfo := [falseRaw, falseRecRaw]

end ConLeche
