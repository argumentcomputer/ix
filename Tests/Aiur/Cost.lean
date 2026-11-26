module

public import LSpec
public import Ix.Aiur.Statistics

/-!
Unit tests for the pure FFT cost model in `Ix/Aiur/Statistics.lean`.

Everything here is `Float` arithmetic over integer inputs — fully
deterministic, no execution, no FFI. Exact equalities stick to inputs
whose logs are integral (powers of two); everything else is checked via
strict monotonicity, including across power-of-two boundaries where the
real (padded) prover would plateau.
-/

public section

open LSpec Aiur

namespace AiurTests.Cost

/-- A small function-like circuit: main width 4, one lookup
(stage 2 width `D = 3`), quotient degree 2. -/
def fnShape : CircuitShape :=
  { mainWidth := 4, stage2Width := 3, quotientDegree := 2,
    preprocessedWidth := 0, preprocessedHeight := 0 }

/-- `logBlowup = 2` (production `B = 4`, `D = 3`): trace width `4 + 3 = 7`,
quotient chunks `q·D = 6`; at `h = 8`:
`(B+1)·7·F(8) + D·F(16) + q·D·F(32) = 35·24 + 3·64 + 6·160 = 1992`. -/
def handComputed : Float := 1992.0

def transformCostTests : LSpec.Spec := do
  itBool "F(0) = 0 (empty circuit is deactivated)" (transformCost 0 == 0.0)
  itBool "F(1) = 1 (clamp keeps height-1 transforms nonzero)"
    (transformCost 1 == 1.0)
  itBool "F(2) = 2" (transformCost 2 == 2.0)
  itBool "F(4) = 8" (transformCost 4 == 8.0)
  itBool "F(1024) = 10240" (transformCost 1024 == 10240.0)
  itBool "F strictly increases across a power-of-two boundary"
    (decide (transformCost 1023 < transformCost 1024) &&
     decide (transformCost 1024 < transformCost 1025))

def fftCostTests : LSpec.Spec := do
  itBool "cost is zero at h = 0" (fftCost fnShape 0 2 == 0.0)
  itBool "hand-computed value at h = 8, logBlowup = 2"
    (fftCost fnShape 8 2 == handComputed)
  itBool "one-row sensitivity at small heights"
    (decide (fftCost fnShape 1 2 < fftCost fnShape 2 2) &&
     decide (fftCost fnShape 2 2 < fftCost fnShape 3 2))
  itBool "one-row sensitivity across a power-of-two boundary"
    (decide (fftCost fnShape 1023 2 < fftCost fnShape 1024 2) &&
     decide (fftCost fnShape 1024 2 < fftCost fnShape 1025 2))
  itBool "wider main trace costs more"
    (decide (fftCost fnShape 8 2 <
      fftCost { fnShape with mainWidth := fnShape.mainWidth + 1 } 8 2))
  itBool "extra lookup (wider stage 2) costs more"
    (decide (fftCost fnShape 8 2 <
      fftCost { fnShape with stage2Width := fnShape.stage2Width + 2 } 8 2))
  itBool "higher quotient degree costs more"
    (decide (fftCost fnShape 8 2 <
      fftCost { fnShape with quotientDegree := 4 } 8 2))
  itBool "larger blowup costs more"
    (decide (fftCost fnShape 8 1 < fftCost fnShape 8 2))
  itBool "committedWidth = main + stage2 + q·D"
    (fnShape.committedWidth == 4 + 3 + 2 * G.extensionDegree)

def formatSciTests : LSpec.Spec := do
  itBool "formatSci 0 = 0" (formatSci 0.0 == "0")
  itBool "formatSci 1 = 1.00e0" (formatSci 1.0 == "1.00e0")
  itBool "formatSci 1424 = 1.42e3" (formatSci 1424.0 == "1.42e3")
  itBool "formatSci 174253453 = 1.74e8" (formatSci 174253453.0 == "1.74e8")
  itBool "mantissa carry: formatSci 999.9 = 1.00e3" (formatSci 999.9 == "1.00e3")

def tests : LSpec.Spec := do
  transformCostTests
  fftCostTests
  formatSciTests

end AiurTests.Cost

end
