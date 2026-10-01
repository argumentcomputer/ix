module

public import ConLeche.Kernel.Basis.Builder

@[expose] public section

/-!
# The pinned `Eq` basis block

The raw pin — the `Eq` block exactly as an export carries it: the
toolchain's `Init.Prelude` declaration at the parser's raw binder
annotations.  The *annotated*
forms (`eqA`, `eqReflA`, `eqRecA`) are computed from these by the
checker's own annotation pass at elaboration time; see
`ConLeche/Kernel/BasisA.lean`.
-/

namespace ConLeche

open BasisDSL

/-- `Eq.{u} {α : Sort u} : α → α → Prop`. -/
def eqRaw : ConstantInfo :=
  .indInfo ⟨eqName, [uN],
    piI "α" (srt u) <|
    pi "a" (bv 0) <|
    pi "b" (bv 1) prop⟩
    { ruleK := true }

/-- `Eq.refl.{u} {α : Sort u} (a : α) : Eq α a a`. -/
def eqReflRaw : ConstantInfo :=
  .ctorInfo ⟨eqReflName, [uN],
    piI "α" (srt u) <|
    pi "a" (bv 0) <|
    ap3 (cnst eqName [u]) (bv 1) (bv 0) (bv 0)⟩
    2 0

/-- The motive of `Eq.rec`: `∀ (b : α) (t : Eq α a b), Sort u_1`, in
the `α`/`a` binder context (`α` is `#1`, `a` is `#0` at its head). -/
def eqRecMotive : Expr :=
  pi "b" (bv 1) <|
  pi "t" (ap3 (cnst eqName [u]) (bv 2) (bv 1) (bv 0)) (srt u1)

/-- `Eq.rec.{u_1, u} {α : Sort u} {a : α} {motive : ∀ b, Eq α a b → Sort u_1}
(refl : motive a (Eq.refl α a)) {b : α} (t : Eq α a b) : motive b t`. -/
def eqRecRaw : ConstantInfo :=
  .recInfo ⟨eqName.str "rec", [u1N, uN],
    piI "α" (srt u) <|
    piI "a" (bv 0) <|
    piI "motive" eqRecMotive <|
    pi "refl" (ap2 (bv 0) (bv 1) (ap2 (cnst eqReflName [u]) (bv 2) (bv 1))) <|
    piI "b" (bv 3) <|
    pi "t" (ap3 (cnst eqName [u]) (bv 4) (bv 3) (bv 0)) <|
    ap2 (bv 3) (bv 1) (bv 0)⟩
    5 4
    [rule eqReflName 0 <|
      lmI "α" (srt u) <|
      lm "a" (bv 0) <|
      lm "motive" eqRecMotive <|
      lm "refl" (ap2 (bv 0) (bv 1) (ap2 (cnst eqReflName [u]) (bv 2) (bv 1))) <|
      bv 0]

/-- The pinned `Eq` basis block, in install order. -/
def eqBasis : List ConstantInfo := [eqRaw, eqReflRaw, eqRecRaw]

end ConLeche
