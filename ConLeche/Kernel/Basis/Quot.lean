module

public import ConLeche.Kernel.Basis.Builder

@[expose] public section

/-!
# The pinned `Quot` basis block

Lean's kernel quotient bundle, pinned as an installed basis block:
`Quot` as a stored inductive with the single constructor `Quot.mk`,
the eliminators `Quot.lift`/`Quot.ind` as stored recursors with one
synthetic rule each (applying the lift/ind slot to the packed
element), and `Quot.sound` as a stored axiom (true in the set model).

The raw pins below match the exporter's `quot` records (and
`Quot.sound`'s `axiom` record) verbatim; the *annotated* forms
(`quotA`, …) are computed from them by the checker's own annotation
pass at elaboration time; see `ConLeche/Kernel/BasisA.lean`.
-/

namespace ConLeche

open BasisDSL

/-- The relation argument's type in the `α` binder context:
`α → α → Prop`. -/
def quotRel : Expr := piA (bv 0) (piA (bv 1) prop)

/-- `Quot.{u} {α : Sort u} (r : α → α → Prop) : Sort u`. -/
def quotRaw : ConstantInfo :=
  .indInfo ⟨quotName, [uN],
    piI "α" (srt u) <|
    pi "r" quotRel (srt u)⟩ {}

/-- `Quot.mk.{u} {α : Sort u} (r : α → α → Prop) (a : α) : Quot α r`. -/
def quotMkRaw : ConstantInfo :=
  .ctorInfo ⟨quotMkName, [uN],
    piI "α" (srt u) <|
    pi "r" quotRel <|
    pi "a" (bv 1) (ap2 (cnst quotName [u]) (bv 2) (bv 1))⟩
    2 1

/-- `Quot.lift`'s function slot, in the `α`/`r`/`β` context: `α → β`. -/
def quotLiftF : Expr := pi "a" (bv 2) (bv 1)

/-- `Quot.lift`'s coherence slot, in the `α`/`r`/`β`/`f` context:
`∀ a b, r a b → f a = f b`. -/
def quotLiftH : Expr :=
  pi "a" (bv 3) <|
  pi "b" (bv 4) <|
  pi "a" (ap2 (bv 4) (bv 1) (bv 0)) <|
  ap3 (cnst eqName [v]) (bv 4) (.app (bv 3) (bv 2)) (.app (bv 3) (bv 1))

/-- `Quot.lift.{u, v} {α : Sort u} {r : α → α → Prop} {β : Sort v}
(f : α → β) (h : ∀ a b, r a b → f a = f b) (q : Quot α r) : β`. -/
def quotLiftRaw : ConstantInfo :=
  .recInfo ⟨quotLiftName, [uN, vN],
    piI "α" (srt u) <|
    piI "r" quotRel <|
    piI "β" (srt v) <|
    pi "f" quotLiftF <|
    pi "a" quotLiftH <|
    pi "a" (ap2 (cnst quotName [u]) (bv 4) (bv 3)) (bv 3)⟩
    5 5
    [rule quotMkName 1 <|
      lm "α" (srt u) <|
      lm "r" quotRel <|
      lm "β" (srt v) <|
      lm "f" quotLiftF <|
      lm "h" quotLiftH <|
      lm "a" (bv 4) (.app (bv 2) (bv 0))]

/-- `Quot.ind`'s motive slot, in the `α`/`r` context:
`Quot α r → Prop`. -/
def quotIndMotive : Expr :=
  pi "a" (ap2 (cnst quotName [u]) (bv 1) (bv 0)) prop

/-- `Quot.ind`'s minor premise, in the `α`/`r`/`β` context:
`∀ a, β (Quot.mk α r a)`. -/
def quotIndMk : Expr :=
  pi "a" (bv 2) <|
  .app (bv 1) (ap3 (cnst quotMkName [u]) (bv 3) (bv 2) (bv 0))

/-- `Quot.ind.{u} {α : Sort u} {r : α → α → Prop} {β : Quot α r → Prop}
(mk : ∀ a, β (Quot.mk α r a)) (q : Quot α r) : β q`. -/
def quotIndRaw : ConstantInfo :=
  .recInfo ⟨quotIndName, [uN],
    piI "α" (srt u) <|
    piI "r" quotRel <|
    piI "β" quotIndMotive <|
    pi "mk" quotIndMk <|
    pi "q" (ap2 (cnst quotName [u]) (bv 3) (bv 2)) (.app (bv 2) (bv 0))⟩
    4 4
    [rule quotMkName 1 <|
      lm "α" (srt u) <|
      lm "r" quotRel <|
      lm "β" quotIndMotive <|
      lm "mk" quotIndMk <|
      lm "a" (bv 3) (.app (bv 1) (bv 0))]

/-- `Quot.sound.{u} {α : Sort u} {r : α → α → Prop} {a b : α} :
r a b → Quot.mk α r a = Quot.mk α r b`. -/
def quotSoundRaw : ConstantInfo :=
  .axiomInfo ⟨quotSoundName, [uN],
    piI "α" (srt u) <|
    piI "r" quotRel <|
    piI "a" (bv 1) <|
    piI "b" (bv 2) <|
    piA (ap2 (bv 2) (bv 1) (bv 0)) <|
    ap3 (cnst eqName [u])
      (ap2 (cnst quotName [u]) (bv 4) (bv 3))
      (ap3 (cnst quotMkName [u]) (bv 4) (bv 3) (bv 2))
      (ap3 (cnst quotMkName [u]) (bv 4) (bv 3) (bv 1))⟩

/-- The pinned `Quot` basis block, in install order. -/
def quotBasis : List ConstantInfo :=
  [quotRaw, quotMkRaw, quotLiftRaw, quotIndRaw, quotSoundRaw]

end ConLeche
