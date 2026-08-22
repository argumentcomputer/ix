module

public import Benchmarks.PalomarSpec.Types

@[expose] public section

namespace PalomarSpec

/-- The registry snapshot represented by this checked-in catalog. The live
`recent.json` feed contained exactly these 19 current projects on this date. -/
def catalogRevision : String := "palomar-recent-2026-08-22"

def registryIndexUrl : String :=
  "https://data.palomar-registry.org/recent.json"

def gitEntry
    (registryId : String) (version : Nat) (qualifier : Lean.Name)
    (title url rev packageName upstreamToolchain license : String)
    (solutionModule : Lean.Name) (formalizationPath : String)
    (directDependencies : Array String)
    (subdir? : Option String := none) : Entry := {
  registryId
  version
  qualifier
  title
  source := { url, rev, subdir? }
  packageName
  upstreamToolchain
  license
  solutionModule
  formalizationPath
  directDependencies
}

/-- The 19 newest active project versions in Palomar's machine-readable
`recent.json` feed, in feed order as retrieved 2026-08-22. Every source is an
immutable full commit and every nested Lake project records its subdirectory. -/
def catalog : Array Entry := #[
  gitEntry "PALOMAR-2026-08-20-000003" 1 `PalomarCardB "catskillsresearch/cardb"
    "https://github.com/catskillsresearch/cardb"
    "d8c1d63052a18db0c43d44c1c77fb10ca8902ed0" "CARDB"
    "leanprover/lean4:v4.30.0" "Apache-2.0" `Solution "Solution.lean"
    #["mathlib"],
  gitEntry "PALOMAR-2026-08-19-000007" 2 `PalomarPDTLean "stalex444/pdt-lean"
    "https://github.com/stalex444/pdt-lean"
    "0dae307fb786a3d180bba137a44555a1bf645637" "PdtQm"
    "leanprover/lean4:v4.31.0" "MIT" `Solution "Solution.lean"
    #["mathlib"],
  gitEntry "PALOMAR-2026-08-19-000002" 2 `PalomarErdos501 "elliotglazer/erdos501"
    "https://github.com/elliotglazer/erdos501"
    "218d1c1e46f77d4db80e566d1721782e85b94a17" "erdos501"
    "leanprover/lean4:v4.34.0-rc1" "Apache-2.0" `Solution "Solution.lean"
    #["mathlib"],
  gitEntry "PALOMAR-2026-08-20-000002" 1 `PalomarLowRankUnivariateSOS
    "yuanchenyang/lean_low_rank_univariate_sos"
    "https://github.com/yuanchenyang/lean_low_rank_univariate_sos"
    "1fccd921a4530a088ab6e230f832041ab3c5c7f3" "LowRankUnivariateSOS"
    "leanprover/lean4:v4.30.0" "Apache-2.0" `Solution "Solution.lean"
    #["checkdecls", "mathlib"],
  gitEntry "PALOMAR-2026-08-13-000001" 2 `PalomarSendov "teorth/sendov"
    "https://github.com/teorth/sendov"
    "1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d" "sendov"
    "leanprover/lean4:v4.34.0-rc1" "Apache-2.0" `Solution "Solution.lean"
    #["mathlib"],
  gitEntry "PALOMAR-2026-08-20-000001" 1 `PalomarVertexGap22 "dcposch/jc2-lean"
    "https://github.com/dcposch/jc2-lean"
    "3cee8100665bc59734511500b98728628ea190db" "jc72108"
    "leanprover/lean4:v4.34.0-rc1" "Apache-2.0" `Solution "Solution.lean"
    #["mathlib"] (subdir? := some "vertex-gap"),
  gitEntry "PALOMAR-2026-08-19-000006" 1 `PalomarArithmeticOfTime
    "stalex444/arithmetic-of-time" "https://github.com/stalex444/arithmetic-of-time"
    "c48eb12817dd1d7ff3dc4d92306c7a4f249e6d7d" "ArithmeticOfTime"
    "leanprover/lean4:v4.31.0" "MIT" `Solution "Solution.lean"
    #["mathlib"],
  gitEntry "PALOMAR-2026-08-19-000005" 1 `PalomarTheoremA "dcposch/jc2-lean"
    "https://github.com/dcposch/jc2-lean"
    "6c0f56309226432afb90b6213638ec987d46f4a3" "jc72108"
    "leanprover/lean4:v4.34.0-rc1" "Apache-2.0" `Solution "Solution.lean"
    #["mathlib"] (subdir? := some "theorem-a"),
  gitEntry "PALOMAR-2026-08-19-000004" 1 `PalomarWallaceProblem
    "vo-rodrigues/wallace-problem-palomar"
    "https://github.com/vo-rodrigues/wallace-problem-palomar"
    "1ab2fb7ed1fb106e14af45312c2a7ab5d568048b" "WallacePalomar"
    "leanprover/lean4:v4.30.0" "Apache-2.0" `Solution "Solution.lean"
    #["mathlib", "wallace"],
  gitEntry "PALOMAR-2026-08-19-000003" 1 `PalomarRegtsSevenster
    "WillWhistler/Regts-Sevenster"
    "https://github.com/WillWhistler/Regts-Sevenster"
    "504ec6aada68b4472f32c4ad46452ff86614f732" "rs-formal"
    "leanprover/lean4:v4.31.0" "Apache-2.0" `Solution "Solution.lean"
    #["mathlib"],
  gitEntry "PALOMAR-2026-08-19-000001" 1 `PalomarJordanCurve "rkirov/jordan_pick"
    "https://github.com/rkirov/jordan_pick"
    "b3c9b7cf7358bf81a077d78ad67e6e8247869ddd" "jordan_curve"
    "leanprover/lean4:v4.33.0" "Apache-2.0" `Solution "Solution.lean"
    #["mathlib"] (subdir? := some "submission/jordan_curve"),
  gitEntry "PALOMAR-2026-08-18-000003" 1 `PalomarBen27
    "xinjiegit/ben_27_formalization"
    "https://github.com/xinjiegit/ben_27_formalization"
    "f70352964007662e97a810c880abbfea1e2ea262" "NUSLean"
    "leanprover/lean4:v4.32.0" "Apache-2.0" `Solution "Solution.lean"
    #["mathlib"],
  gitEntry "PALOMAR-2026-08-18-000002" 1 `PalomarPrimeGaps
    "AxiomMath/PrimeGapsLib"
    "https://github.com/AxiomMath/PrimeGapsLib"
    "1faa7b14e82ddebc2772dfb9153922f01b106477" "PrimeGapsLib"
    "leanprover/lean4:v4.33.0-rc1" "Apache-2.0" `Solution.Basic
    "Solution/Basic.lean" #["mathlib", "PrimeNumberTheoremAnd"],
  gitEntry "PALOMAR-2026-08-18-000001" 1 `PalomarLDTComparator
    "LionSR/LDT-comparator" "https://github.com/LionSR/LDT-comparator"
    "15f1d5b2797c67ceb9d278d0a4d576772b937e9a" "MIPStarREComparator"
    "leanprover/lean4:v4.32.0" "Apache-2.0" `Solution "Solution.lean"
    #["MIPStarRE"],
  gitEntry "PALOMAR-2026-08-17-000004" 1 `PalomarCantorFrames
    "jaumededios/cantor-frames-palomar"
    "https://github.com/jaumededios/cantor-frames-palomar"
    "e1ce015224e702a4e93ae59e8ca73616daaa8d5a" "CantorFramesPalomar"
    "leanprover/lean4:v4.30.0" "Apache-2.0" `Solution "Solution.lean"
    #["CantorMeasureFrames"],
  gitEntry "PALOMAR-2026-08-17-000003" 1 `PalomarSabidussi
    "gexahedron/sabidussi-lean"
    "https://github.com/gexahedron/sabidussi-lean"
    "58307d74da99ec6e4fe28e012c30c83e369c54c3" "sabidussi"
    "leanprover/lean4:v4.31.0" "Apache-2.0" `Solution "Solution.lean"
    #["mathlib"],
  gitEntry "PALOMAR-2026-08-17-000002" 1 `PalomarHadamard668
    "Paul-Lez/hadamard-668-comparator"
    "https://github.com/Paul-Lez/hadamard-668-comparator"
    "da94bc80401b6ece36d8dd2f5c316755fd97dd65" "hadamard668"
    "leanprover/lean4:v4.34.0-rc1" "Apache-2.0" `Solution "Solution.lean"
    #["mathlib"],
  gitEntry "PALOMAR-2026-08-17-000001" 1 `PalomarRadoRiemannSurface
    "rkirov/jordan_pick" "https://github.com/rkirov/jordan_pick"
    "ccbcc61444864ceb7990ab6b1abb5238c4fc6243" "rado_riemannSurface"
    "leanprover/lean4:v4.33.0" "Apache-2.0" `Solution "Solution.lean"
    #["mathlib"] (subdir? := some "submission/rado_riemannSurface"),
  gitEntry "PALOMAR-2026-08-08-000001" 3 `PalomarErdosUnitDistance
    "kim-em/erdos-unit-distance-comparator"
    "https://github.com/kim-em/erdos-unit-distance-comparator"
    "be6c2ee4c9fb16fd6bed442b4c361fb10369beb5" "ErdosUnitDistanceComparator"
    "leanprover/lean4:v4.31.0-rc2" "Apache-2.0" `Solution "Solution.lean"
    #["ErdosUnitDistance"]
]

def findEntry? (qualifier : Lean.Name) : Option Entry :=
  catalog.find? (·.qualifier == qualifier)

def isEntryQualifier (qualifier : Lean.Name) : Bool :=
  (findEntry? qualifier).isSome

end PalomarSpec
