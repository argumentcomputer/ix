module

public import ConLeche.Kernel.Basis.Builder

@[expose] public section

/-!
# The pinned `Nat` basis block

The raw pin — the `Nat` block exactly as an export carries it: the
toolchain's `Init.Prelude` declaration at the parser's raw binder
annotations.  The *annotated*
forms (`natA`, …) are computed from these by the checker's own
annotation pass at elaboration time; see `ConLeche/Kernel/BasisA.lean`.
-/

namespace ConLeche

open BasisDSL

/-- The type `Nat`, as a closed constant. -/
def natT : Expr := cnst natName

/-- `Nat : Type`. -/
def natRaw : ConstantInfo :=
  .indInfo ⟨natName, [], type1⟩ {}

/-- `Nat.zero : Nat`. -/
def natZeroRaw : ConstantInfo :=
  .ctorInfo ⟨natZeroName, [], natT⟩ 0 0

/-- `Nat.succ (n : Nat) : Nat`. -/
def natSuccRaw : ConstantInfo :=
  .ctorInfo ⟨natSuccName, [], pi "n" natT natT⟩ 0 1

/-- The motive of `Nat.rec`: `∀ (t : Nat), Sort u`. -/
def natRecMotive : Expr := pi "t" natT (srt u)

/-- The successor minor premise of `Nat.rec`, in the `motive`/`zero`
binder context: `∀ (n : Nat), motive n → motive (Nat.succ n)`. -/
def natRecSucc : Expr :=
  pi "n" natT <|
  pi "n_ih" (.app (bv 2) (bv 0)) <|
  .app (bv 3) (.app (cnst natSuccName) (bv 1))

/-- `Nat.rec.{u} {motive : Nat → Sort u} (zero : motive Nat.zero)
(succ : ∀ n, motive n → motive n.succ) (t : Nat) : motive t`. -/
def natRecRaw : ConstantInfo :=
  .recInfo ⟨natName.str "rec", [uN],
    piI "motive" natRecMotive <|
    pi "zero" (.app (bv 0) (cnst natZeroName)) <|
    pi "succ" natRecSucc <|
    pi "t" natT (.app (bv 3) (bv 0))⟩
    3 3
    [rule natZeroName 0 <|
      lm "motive" natRecMotive <|
      lm "zero" (.app (bv 0) (cnst natZeroName)) <|
      lm "succ" natRecSucc <|
      bv 1,
     rule natSuccName 1 <|
      lm "motive" natRecMotive <|
      lm "zero" (.app (bv 0) (cnst natZeroName)) <|
      lm "succ" natRecSucc <|
      lm "n" natT <|
      ap2 (bv 1) (bv 0) (ap4 (cnst (natName.str "rec") [u]) (bv 3) (bv 2) (bv 1) (bv 0))]

/-- The pinned `Nat` basis block, in install order. -/
def natBasis : List ConstantInfo := [natRaw, natZeroRaw, natSuccRaw, natRecRaw]

end ConLeche
