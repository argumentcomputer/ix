module

public import Benchmarks.TruthMinesSpec.Types

@[expose] public section

namespace TruthMinesSpec

/-- Bump whenever a semantic catalog edit invalidates the frozen admission
spec (`Benchmarks.TruthMinesSpec.Spec`). Echoed into build provenance. -/
def catalogRevision : String := "ix-corpus-v1"

/-- The one toolchain every catalog record must target.

This is not an independent choice: `ix catalog` loads member `.olean`s with
ix's own Lean runtime, so the corpus builds on ix's toolchain or it does not
build at all. Living in the ix repo, the string is derived from the running
toolchain rather than authored — the TruthMines-era external-CLI version
handshake dissolves — and catalog validation asserts every record targets it,
so an ix toolchain bump surfaces as a named validation failure, not a silent
load error. The `truthmines-spec` suite additionally pins this against the
repo's `lean-toolchain` file and the generated workspace's copy. -/
def expectedToolchain : String := s!"leanprover/lean4:v{Lean.versionString}"

def gitPackage
    (lakeName : String) (qualifier : Lean.Name)
    (url rev : String) (directDeps : Array String)
    (license lastCommit : String) (rootModules : Array Lean.Name)
    (subdir? : Option String := none)
    (moduleIncludes : Array Lean.Name := #[])
    (moduleExcludes : Array Lean.Name := #[])
    (notes : String := "") : PackageSpec := {
  lakeName
  qualifier
  source := .git {url, rev, subdir?}
  upstreamToolchain := expectedToolchain
  directDeps
  license
  lastCommit
  rootModules
  moduleIncludes
  moduleExcludes
  hermetic := true
  disposition := .candidate
  notes
}

def excludedGitPackage
    (lakeName : String) (qualifier : Lean.Name)
    (url rev license lastCommit reason : String)
    (notes : String := "") : PackageSpec := {
  lakeName
  qualifier
  source := .git {url, rev}
  upstreamToolchain := expectedToolchain
  directDeps := #[]
  license
  lastCommit
  rootModules := #[]
  hermetic := false
  disposition := .excluded reason
  notes
}

/-- The two local packages remain as declaration-form and collision fixtures.
The ecosystem records below are the production-scale qualified aggregate. -/
def catalog : Array PackageSpec := #[
  {
    lakeName := "relocFixtureB"
    qualifier := `B
    source := .local "../Catalog/RelocFixtureB"
    upstreamToolchain := expectedToolchain
    directDeps := #[]
    license := "Apache-2.0"
    lastCommit := "workspace-fixture"
    rootModules := #[`FixtureB]
    hermetic := true
    disposition := .candidate
    notes := "Collision and declaration-coverage fixture; dependency leaf."
  },
  {
    lakeName := "relocFixtureA"
    qualifier := `A
    source := .local "../Catalog/RelocFixtureA"
    upstreamToolchain := expectedToolchain
    directDeps := #["relocFixtureB"]
    license := "Apache-2.0"
    lastCommit := "workspace-fixture"
    rootModules := #[`FixtureA]
    hermetic := true
    disposition := .candidate
    notes := "Depends on B and verifies owner-aware reference rewriting."
  },
  gitPackage "mathlib" `Mathlib
    "https://github.com/leanprover-community/mathlib4"
    "db584cd6d46c92f209a44c0f1c829460d327499d"
    #["LeanSearchClient", "Qq", "aesop", "batteries", "importGraph", "plausible", "proofwidgets"] "Apache-2.0" "2026-08-10"
    #[`Mathlib] (notes := "the spine; toolchain and every other core pin are chosen for it"),
  gitPackage "plausible" `Plausible
    "https://github.com/leanprover-community/plausible"
    "b7eb3304aeae834b12dda98993a37f6a41f6f0bb"
    #[] "Apache-2.0" "2026-08-10"
    #[`Plausible] (notes := "pinned by mathlib@leanprover/lean4:v4.33.0"),
  gitPackage "LeanSearchClient" `LeanSearchClient
    "https://github.com/leanprover-community/LeanSearchClient"
    "5f4d51b81cbd3f6b32b156bfad9056621a040404"
    #[] "Apache-2.0" "2026-08-10"
    #[`LeanSearchClient] (notes := "pinned by mathlib@leanprover/lean4:v4.33.0"),
  gitPackage "importGraph" `ImportGraph
    "https://github.com/leanprover-community/import-graph"
    "16f02aa7642864af59f1ff0e384a015994db9118"
    #["Cli"] "Apache-2.0" "2026-08-10"
    #[`ImportGraph] (notes := "pinned by mathlib@leanprover/lean4:v4.33.0"),
  gitPackage "proofwidgets" `ProofWidgets
    "https://github.com/leanprover-community/ProofWidgets4"
    "4be2e3d5087eeb272cf5a8853b8f9dd025ef5957"
    #[] "Apache-2.0" "2026-08-10"
    #[`ProofWidgets] (notes := "pinned by mathlib@leanprover/lean4:v4.33.0"),
  gitPackage "aesop" `Aesop
    "https://github.com/leanprover-community/aesop"
    "3448c0bcc5ce01b2d1546e483ec3620e32df3d0e"
    #["batteries"] "Apache-2.0" "2026-08-10"
    #[`Aesop] (notes := "pinned by mathlib@leanprover/lean4:v4.33.0"),
  gitPackage "Qq" `Qq
    "https://github.com/leanprover-community/quote4"
    "92c15be17b7caf78c2ad767ec40f89052d908d81"
    #[] "Apache-2.0" "2026-08-10"
    #[`Qq] (notes := "pinned by mathlib@leanprover/lean4:v4.33.0"),
  gitPackage "batteries" `Batteries
    "https://github.com/leanprover-community/batteries"
    "4488d40d070b9700d4d5a6aa342f0d40c31b2a2d"
    #[] "Apache-2.0" "2026-08-10"
    #[`Batteries] (notes := "pinned by mathlib@leanprover/lean4:v4.33.0"),
  gitPackage "Cli" `Cli
    "https://github.com/leanprover/lean4-cli"
    "6130a47896ce867c6a4a55373441e59e565bad0f"
    #[] "Apache-2.0" "2026-08-10"
    #[`Cli] (notes := "pinned by mathlib@leanprover/lean4:v4.33.0"),
  gitPackage "Apportionmentlib" `Apportionmentlib
    "https://github.com/mdbrnowski/Apportionmentlib"
    "34e0fb30422829494ba7d634e5ed983db94e54a2"
    #["mathlib"] "Apache-2.0" "2026-08-13"
    #[`Apportionmentlib] (notes := "Social choice: apportionment methods (Hamilton/Jefferson/Webster) with quota and monotonicity theorems. Upstream pins mathlib to the moving tag 'stable'; our root pin fixes it."),
  gitPackage "GibbsMeasure" `GibbsMeasure
    "https://github.com/YaelDillies/gibbs-measure"
    "2c57fb5f363f6afeb252b008f2bcedbd1b87b8cc"
    #["mathlib"] "Apache-2.0" "2026-07-16"
    #[`GibbsMeasure] (notes := "Statistical physics: Gibbs measures, Ising, percolation. Recent toolchain, contains sorries."),
  gitPackage "LeanCert" `LeanCert
    "https://github.com/alerad/LeanCert"
    "501b2c09e367721f58200f53261787a3d280abe2"
    #["mathlib"] "Apache-2.0" "2026-08-13"
    #[`LeanCert] (notes := "Verified interval arithmetic and certified bounds on exp/sin/cos plus root finding. Recent toolchain. The heavy native_decide targets are outside the default build."),
  gitPackage "LeanMachineLearning" `LeanMachineLearning
    "https://github.com/LeanMachineLearning/LML"
    "0dcb334ae15427bb297a0cc7e0008292ec4d63af"
    #["mathlib", "verso"] "Apache-2.0" "2026-08-15"
    #[`LeanMachineLearning] (notes := "Current toolchain and committed today. Repo is LML, not LeanMachineLearning."),
  gitPackage "LeanSha256" `LeanSha256
    "https://github.com/etheorem/LeanSha256"
    "d8a7dc10c8a089330f9a13632b6f2a2283e4e43b"
    #[] "LGPL-3.0-only" "2026-06-30"
    #[`LeanSha256] (notes := "LGPL-3.0 -- weak copyleft, flagged for the aggregate license join. Pure-Lean NIST-CAVP-validated SHA-256, no FFI, no Mathlib. Trivially buildable."),
  gitPackage "Quantum4Lean" `Quantum4Lean
    "https://github.com/Alektronnik/Quantum4Lean"
    "0a4ec3a76464fd36dea0150e571daa356350d0bf"
    #[] "Apache-2.0" "2026-07-04"
    #[`Quantum4Lean] (notes := "NISQ simulator: StateVector, VQE, QAOA. ZERO Lean deps -- no Mathlib -- so the cheapest quantum package here. Its C++/Metal Apple-Silicon bridge is optional."),
  gitPackage "Statlib" `Statlib
    "https://github.com/stat-lib/Statlib"
    "01d2a03770455f5c775bb25c57e7fbb8e1eaf8d8"
    #["mathlib", "subverso"] "Apache-2.0" "2026-08-13"
    #[`Statlib] (notes := "General statistics library. autoImplicit = true upstream."),
  gitPackage "pacioli" `Pacioli
    "https://github.com/ojhermann-org/pacioli"
    "9fa4ff363174f78ba19d74ceb1d7fc5c6efbfb90"
    #["mathlib"] "Apache-2.0" "2026-08-12"
    #[`Pacioli] (notes := "Verified core of double-entry accounting mechanics. Genuinely unusual domain."),
  gitPackage "LSpec" `LSpec
    "https://github.com/argumentcomputer/LSpec"
    "e780f4188c9649aef988270f4d126651460ca9c4"
    #["plausible"] "MIT" "2026-08-12"
    #[`LSpec] (notes := "Testing framework on plausible, v2.0.0. Upstream pins plausible at v4.33.0 while our spine takes Mathlib's v4.34.0-rc1 plausible -- a direct version conflict that our root pin resolves in the spine's favour. Whether LSpec survives that is exactly what the probe answers."),
  gitPackage "MD4Lean" `MD4Lean
    "https://github.com/acmepjz/md4lean"
    "31907cc18f48a95384f99cee5582c00fb39e0f67"
    #[] "MIT" "2026-06-22"
    #[`MD4Lean] (notes := "Wrapper for the MD4C CommonMark parser. VENDORS md4c's C sources and links them into the lean_lib via moreLinkObjs -- no system library, no downloads. Pins v4.29.0-rc1 yet is consumed by verso and doc-gen4 at v4.34.0-rc1, which is direct evidence that forward compatibility across five releases does hold in practice."),
  gitPackage "Parser" `Parser
    "https://github.com/fgdorais/lean4-parser"
    "e2c2439d75fe54df49f72f809d22ceeacf261f21"
    #["UnicodeBasic", "batteries"] "Apache-2.0" "2026-08-12"
    #[`Parser] (notes := "General parser-combinator library. Pure Lean, current toolchain, sets allowImportAll. Reservoir lists it as fgdorais/Parser while the repo is lean4-parser -- resolve by URL."),
  gitPackage "Regex" `Regex
    "https://github.com/pandaman64/lean-regex"
    "30b7188eeecd7268d0f9816f97eb6304083c1bfb"
    #[] "Apache-2.0" "2026-08-14"
    #[`Regex] (subdir? := some "regex") (notes := "SUBDIR regex/ -- lakefile.toml and lean-toolchain are not at the repo root. Verified NFA-based regex engine with correctness proofs. Zero deps, current toolchain, one of the most hermetic packages found. Beats bergmannjg/regex, which claims the same package name on an older toolchain."),
  gitPackage "UnicodeBasic" `UnicodeBasic
    "https://github.com/fgdorais/lean4-unicode-basic"
    "f199e403002f82257a35add247ae05e00fd01c3c"
    #[] "Apache-2.0" "2026-08-12"
    #[`UnicodeBasic] (notes := "Unicode general category and case mapping. Compiles a small bundled C table library with precompileModules -- vendored, no system library, no downloads. Zero deps, current toolchain, 460 dependents."),
  gitPackage "bignum" `Bignum
    "https://github.com/arademaker/bignum"
    "4b32a232d3481f9a7b4b3c101fa0dcd946392508"
    #["cslib", "mathlib"] "Apache-2.0" "2026-04-21"
    #[`Bignum] (notes := "Port of AWS s2n-bignum: verified arbitrary-precision arithmetic primitives. Uses the new module system."),
  gitPackage "binary" `Binary
    "https://github.com/Lean-zh/binary"
    "c1adb7380ea3a538cd800bc5974a1fa05d8b488e"
    #[] "MIT" "2026-08-03"
    #[`Binary] (notes := "Binary Get/Put serialization with deriving handlers plus a UTF-8 codec. Zero deps -- the cheapest serialization library found. Uses the new module system (public import). Root module Binary is generic enough to be a collision surface."),
  gitPackage "lean-uri" `LeanUri
    "https://github.com/josephmckinsey/lean-uri"
    "4d717ff58f42b229ac08815855087344a62ec613"
    #[] "Apache-2.0" "2026-01-26"
    #[`LeanUri] (moduleExcludes := #[`UriTesting])
    (notes := "Upstream declares an absent UriTesting root; the LeanUri library is complete."),
  gitPackage "maze" `Maze
    "https://github.com/dwrensha/lean4-maze"
    "fb7e61cb1a224ead7eac95de1511620861cd44fe"
    #[] "Apache-2.0" "2025-07-02"
    #[`Maze] (notes := "A maze encoded in Lean 4 syntax -- a metaprogramming demo. Zero deps."),
  gitPackage "numbers" `Numbers
    "https://github.com/T-Brick/Numbers"
    "f6494eb3029f3784fb9f5902e3c2c65ce917860b"
    #[] "GPL-3.0" "2025-11-14"
    #[`Numbers] (notes := "GPL-3.0 -- copyleft; including it would make the aggregate GPL. Arbitrary bit-length integers. Flagged for the license decision."),
  gitPackage "protobuf" `Protobuf
    "https://github.com/Lean-zh/protobuf"
    "8c707f2cb4ab8eae280127651162d28e58164c1e"
    #["binary"] "MIT" "2026-08-03"
    #[`Protobuf] (notes := "Full proto3: wire codec, descriptors, extensions, ProtoJSON, reflection, conformance suite. preferReleaseBuild means Lake tries a prebuilt download first. COLLISION HISTORY: this collided with Cedar over the Protobuf.* module namespace (Cedar ships cedar-lean/Protobuf/Encoding/* for CedarProto), and was excluded in favour of Cedar. Cedar then failed the Mathlib-aware probe outright -- it redeclares List.filterMap_congr, which Mathlib.Data.List.Basic also defines -- so the collision is moot and protobuf is back. Restore the exclusion if Cedar ever returns."),
  gitPackage "AddCombi" `AddCombi
    "https://github.com/leanprover-community/add-combi"
    "ecee0cf8bff785b2bdffe2e292a7e08e77384c60"
    #["mathlib"] "Apache-2.0" "2026-08-14"
    #[`AddCombi] (notes := "leanprover-community shared additive-combinatorics core, extracted from PFR/LeanAPAP. 14 files, 0 sorries. Same toolchain as the spine."),
  gitPackage "BET" `BET
    "https://github.com/mseri/BET"
    "e984d1b08f6c6d07fa690a78674e9ac6ef1050c2"
    #["mathlib"] "Apache-2.0" "2026-08-07"
    #[`BET] (notes := "Birkhoff Ergodic Theorem. 17 files, single dep, near-current toolchain. Cheap, low risk."),
  gitPackage "CamCombi" `CamCombi
    "https://github.com/YaelDillies/cam-combi"
    "2e8be1b215cc08853390d8fde013e503bb9d0863"
    #["mathlib"] "Apache-2.0" "2026-07-16"
    #[`CamCombi] (notes := "Renamed from LeanCamCombi. Small now (21 files) -- most content upstreamed to Mathlib/AddCombi."),
  gitPackage "CombinatorialGames" `CombinatorialGames
    "https://github.com/vihdzp/combinatorial-games"
    "99a469a2e02fd9fab9a717efe27f7fc84b880bbb"
    #["mathlib"] "Apache-2.0" "2026-08-15"
    #[`CombinatorialGames] (notes := "Surreal numbers / Conway games, successor to Mathlib's SetTheory.Game. 56 files, 0 sorries, single dep. Repo slug differs from package name."),
  gitPackage "Toric" `Toric
    "https://github.com/YaelDillies/Toric"
    "e3aa113849165565a7d5ccfba5ee2203fa75b17a"
    #["mathlib"] "Apache-2.0" "2026-08-14"
    #[`Toric] (notes := "Toric varieties. Small (19 files), current toolchain, low risk."),
  gitPackage "carleson" `Carleson
    "https://github.com/fpvandoorn/carleson"
    "abad489adf7eb4e94ef5933d9880877c76fbd09f"
    #["mathlib"] "Apache-2.0" "2026-08-11"
    #[`Carleson] (notes := "Metric-space Carleson theorem. 122 files / 50k LOC, ~26 sorries. Package name lowercase, root module capitalised. Only Carleson listed: Challenge/Solution are eval scaffolding."),
  gitPackage "kolmogorov_extension4" `KolmogorovExtension4
    "https://github.com/RemyDegenne/kolmogorov_extension4"
    "7d76e184c3d2138a2741baf923b57e9a01b9cf25"
    #["mathlib"] "Apache-2.0" "2026-07-24"
    #[`KolmogorovExtension4] (notes := "Mostly upstreamed to Mathlib; now a 6-file shim, 0 sorries. Near-zero build cost. Required by BrownianMotion."),
  gitPackage "miniF2F" `MiniF2F
    "https://github.com/google-deepmind/miniF2F"
    "f0a20e14c1eeccd859d51bb4c2b3ee487889c303"
    #["formal_conjectures"] "Apache-2.0" "2026-04-23"
    #[`MiniF2F.Valid] (notes := "Google DeepMind's current miniF2F benchmark; replaces the older yangky11 port."),
  gitPackage "MRiscX" `MRiscX
    "https://github.com/JulsDE/MRiscX"
    "5dc879f717cf69d76805a38927ef086d0c2ea257"
    #["mathlib"] "Apache-2.0" "2026-08-11"
    #[`MRiscX] (notes := "Certified RISC-V interpreter with a Hoare logic. Hand-written rather than Sail-generated, so far lighter than the generated ISA models. Clean single lib, current toolchain."),
  gitPackage "PolyFun" `PolyFun
    "https://github.com/Verified-zkEVM/PolyFun"
    "4247ad7e8fa5ece217508af97bc2e24b168a1cf6"
    #["cslib", "mathlib"] "Apache-2.0" "2026-08-13"
    #[`PolyFun] (notes := "Polynomial functors and interaction trees for interactive protocols. One of the few third-party packages already requiring cslib."),
  gitPackage "VerilLean" `VerilLean
    "https://github.com/verilog-proof/VerilLean"
    "18acff7b33019bcbcc64154d5b6fdf566867f4d7"
    #[] "NONE" "2026-08-13"
    #[`VerilLean] (notes := "UNLICENSED. Lean-embedded framework for verifying Verilog modules. Zero deps."),
  gitPackage "descriptive-complexity" `DescriptiveComplexity
    "https://github.com/PierreSenellart/descriptive-complexity"
    "5e054e156f0e1a97db28b6fe274d78834afd8ddb"
    #["mathlib"] "Apache-2.0" "2026-08-13"
    #[`DescriptiveComplexity] (notes := "Descriptive complexity, machine-model-free NP-completeness. Zero deps, recent toolchain."),
  gitPackage "domain-theory" `DomainTheory
    "https://github.com/zilberstein/domain-theory"
    "5c667c350be8b83ab49e3f9d26d7db8fb90b5f50"
    #["mathlib"] "Apache-2.0" "2026-08-03"
    #[`DomainTheory] (notes := "Domain theory: CPOs, fixed points."),
  gitPackage "fad" `Fad
    "https://github.com/arademaker/fad"
    "d9a9328f8819b2a2bb831a2b25992dcadf432878"
    #["cslib"] "Apache-2.0" "2026-08-12"
    #[`Fad] (notes := "Functional Algorithm Design (Bird & Gibbons). Requires cslib. Very current."),
  gitPackage "haskell-spec" `HaskellSpec
    "https://github.com/haskell-spec/haskell-spec"
    "d941b26f830712cdc027e04400ad94d3095dab6b"
    #[] "NONE" "2026-03-02"
    #[`HaskellSpec] (notes := "UNLICENSED. Formal specification of the Haskell Language Report. Zero deps."),
  gitPackage "implab" `ImpLab
    "https://github.com/ejgallego/imp-lab"
    "a56ea1cd6429dba7e093f1483cf59867c5a94ab9"
    #[] "Apache-2.0" "2026-05-19"
    #[`ImpLab] (moduleExcludes := #[`examples, `Test])
    (notes := "Upstream declares absent examples and Test roots; the ImpLab sources remain complete."),
  gitPackage "lean-sail" `Sail
    "https://github.com/rems-project/lean-sail"
    "079463134b9c50450b8393e1566a09fc492a34d9"
    #[] "NONE" "2026-07-20"
    #[`Sail] (notes := "UNLICENSED. REMS' Sail-to-Lean runtime library, the substrate for Sail-generated ISA models. Zero deps."),
  gitPackage "lean4lean" `Lean4Lean
    "https://github.com/digama0/lean4lean"
    "e0e3f6bcccb840cb0ea6f11c2b274ada93a12e00"
    #["batteries"] "Apache-2.0" "2026-08-14"
    #[`Lean4Lean] (notes := "The Lean 4 kernel reimplemented and verified in Lean 4. Clean pure-Lean build, batteries only. Library target is Lean4Lean, not the capitalisation Lake would guess from the package name."),
  gitPackage "phi-confluence" `PhiConfluence
    "https://github.com/objectionary/proof"
    "58aa7731076d02bf51b2dfbcdc06c4f764101fb4"
    #["mathlib"] "MIT" "2026-06-14"
    #[`PhiConfluence] (notes := "Confluence proof for the phi-calculus (EO language core)."),
  gitPackage "plfl" `Plfl
    "https://github.com/rami3l/PLFaLean"
    "138c217949256462d1ed68853ab650b0bacd48f8"
    #["mathlib"] "MIT" "2026-08-08"
    #[`Plfl] (notes := "Programming Language Foundations in Agda, ported to Lean 4: lambda calculi, type soundness, subtyping, bisimulation."),
  gitPackage "yul-semantics" `YulSemantics
    "https://github.com/powdr-labs/yul-semantics"
    "d557aacbf4937ee1f7d08e32f8569108d7045eea"
    #["batteries"] "Apache-2.0" "2026-08-06"
    #[`YulSemantics] (notes := "Yul (Solidity IR) semantics. batteries-only, single lib -- very easy to include."),
  gitPackage "Curl" `Curl
    "https://github.com/bergmannjg/leanCurl"
    "d725fede14f67acc746c18eaec962f6461dee5cb"
    #[] "MIT" "2026-02-03"
    #[`Curl] (notes := "libcurl bindings via a C++ shim. REQUIRES SYSTEM libcurl, located by shelling out to `ldd $(which curl) | grep libcurl | awk ...` at lakefile-load time. Overridable via -KlibcurlSharedLib, which is the Nix escape hatch if we keep it."),
  gitPackage "SDL" `SDL
    "https://github.com/Anderssorby/SDL.lean"
    "8d15cba565d8a8208b620e2ef954be25a9feedcb"
    #[] "MIT" "2025-12-27"
    #[`SDL] (notes := "SDL2 bindings via a C shim. Needs system SDL2 + SDL2_image and invokes sdl2-config at build time, so the sdl2-config script must be on PATH. No downloads, which makes it the cleanest SDL option -- ValorZard/lean-sdl3 git-clones and cmake-builds SDL during lake build and claims the same SDL root module, so it is excluded. DEMOTED from the admission spec 2026-08-21: its include-flag detection produces garbage (-I/SDL2) under nix's sdl2-compat even with SDL2.dev's sdl2-config on PATH, so the shim cannot compile in the ix dev environment; re-admit by restoring its spec entry once the environment satisfies its lakefile."),
  gitPackage "exes" `LeanTea
    "https://github.com/Verilean/lean-tea"
    "3c96270b131f6cab3b7fa41e8b0cfe73655b5481"
    #[] "Apache-2.0" "2026-07-18"
    #[`LeanTea] (notes := "Full-stack web and TUI framework (Elm/Yesod inspired). PACKAGE NAME IS exes, not lean-tea -- a require using the repo name will not resolve. Its eight extern_libs (mysql, postgres, tls, crypto, desktop) are gated behind env vars, so the DEFAULT build touches no external library; sqlite is vendored."),
  gitPackage "flow" `Flow
    "https://github.com/predictable-machines/lean4-flow"
    "2f4357427dfdf934b02779cf1f0bd8ded1595ef7"
    #[] "MIT" "2026-07-16"
    #[`Flow] (moduleExcludes := #[`FlowTest])
    (notes := "Upstream declares a FlowTest root whose source file is absent; its real test submodules remain inventoried."),
  gitPackage "lapis" `Lapis
    "https://github.com/SrGaabriel/lapis"
    "2de2282ec7f5ecae75a3c338c02a930771e691df"
    #["UnicodeBasic", "doc-gen4"] "Apache-2.0" "2026-04-15"
    #[`Lapis] (notes := "Concurrent Language Server Protocol framework. Pure Lean itself; the risk is its deps -- upstream requires a personal FORK of UnicodeBasic that collides by package name with the upstream one. Our root pin forces the upstream UnicodeBasic, which the probe will test."),
  gitPackage "lean-grpc" `LeanGrpc
    "https://github.com/RileyBetts/lean-grpc"
    "2e7712ae2f43a26a03790b573e2d788616cef655"
    #[] "Apache-2.0" "2026-08-12"
    #[`H2, `Hpack, `Bytes, `Proto] (notes := "Pure-Lean gRPC stack on core Std.Async, zero Lake deps. Only its Grpc lib needs OpenSSL; H2/Hpack/Bytes/Proto do not, so those are what is imported here -- the OpenSSL edge is avoided by import choice rather than by patching."),
  gitPackage "lean-redis" `LeanRedis
    "https://github.com/ecyrbe/lean-redis"
    "91685c1e77c84228ba54c1ab39f15288a8179b28"
    #[] "MIT" "2026-07-14"
    #[`LeanRedis] (notes := "Full async Redis client (RESP2/RESP3, pipelining, pooling) written entirely in Lean on core Std.Async. No native code at all. Preferred over marcellop71/redis-lean, which needs hiredis and declares deps by git@ SSH URL."),
  gitPackage "lean4-base64" `Base64
    "https://github.com/predictable-machines/lean4-base64"
    "0f457b464797b5c4bde04548307f02f58ffebbd5"
    #[] "MIT" "2026-07-16"
    #[`Base64] (moduleExcludes := #[`Base64Test])
    (notes := "Upstream declares an absent Base64Test root; the Base64 library is complete."),
  gitPackage "lean_eff" `LeanEff
    "https://github.com/palladin/lean-eff"
    "453f4feb6508ec787fc325a70523d38e4378ef8f"
    #["leansqlite"] "MIT" "2026-05-17"
    #[`LeanEff] (notes := "Extensible-effects library. Odd but harmless leansqlite dep, which is itself vendored and hermetic."),
  gitPackage "lean_reducers" `LeanReducers
    "https://github.com/palladin/lean-reducers"
    "6e93e0ce326025f762d00b947716c2b98ce1fb06"
    #["plausible"] "MIT" "2026-05-30"
    #[`LeanReducers] (notes := "Parallel fused reducers. Pure Lean."),
  gitPackage "leansi" `leansi
    "https://github.com/schergen-org/Leansi"
    "a4524cea6cf5a56d6433cdbfaa04bca98fa8b1d0"
    #[] "Apache-2.0" "2026-03-22"
    #[`leansi] (notes := "ANSI terminal formatting. Pure Lean, zero deps. NOTE the root module is lowercase leansi -- easy to get wrong in an import."),
  gitPackage "leansqlite" `SQLite
    "https://github.com/leanprover/leansqlite"
    "a117edeff8db819a001455bcbafe86748635dd6b"
    #[] "Apache-2.0" "2026-08-10"
    #[`SQLite] (notes := "Official Lean FRO SQLite bindings. VENDORS the full sqlite3.c amalgamation -- no system sqlite3, no pkg-config, no downloads. Perfectly hermetic given a C compiler, current toolchain, and now on the doc-gen4 path. Beats BRonen/sqlite-lean, which claims the same SQLite root module."),
  gitPackage "LeanBridge" `LeanBridge
    "https://github.com/CBirkbeck/LeanBridge"
    "4dffaca404780f5ec439bda834fbc90a891174c2"
    #["doc-gen4", "mathlib"] "Apache-2.0" "2026-06-29"
    #[`LeanBridge] (notes := "Links LMFDB (number theory database) to Lean."),
  gitPackage "LiterateLean" `LiterateLean
    "https://github.com/tani/literate-lean"
    "a9be26ba1190072fe4d5b15d9622bdf1bf3a8234"
    #[] "Unlicense" "2026-07-14"
    #[`LiterateLean] (notes := "Literate programming for Lean 4. Zero deps."),
  gitPackage "Paperproof" `Paperproof
    "https://github.com/Paper-Proof/paperproof"
    "69401f7d9348699e1532194734b5dda0771278b7"
    #[] "MIT" "2026-07-20"
    #[`Paperproof] (subdir? := some "lean") (moduleExcludes := #[`Tests])
    (notes := "The generic test root Tests collides at the source-module layer with Loogle and Verso; public Paperproof modules remain complete."),
  gitPackage "i18n" `I18n
    "https://github.com/hhu-adam/lean-i18n"
    "1a99b00a940624c0a6c3009b756fb922acf0fe78"
    #["Cli", "batteries"] "Apache-2.0" "2026-06-27"
    #[`I18n] (notes := "Internationalisation for Lean, used by lean4game. Zero deps."),
  gitPackage "lean4export" `Export
    "https://github.com/leanprover/lean4export"
    "b18d673bd29b476466a51a3be1012df2ed322b10"
    #[] "Apache-2.0" "2026-08-10"
    #[`Export] (notes := "Environment/declaration export. Root module is Export, NOT Lean4Export. Tracks core releases exactly."),
  gitPackage "loogle" `Loogle
    "https://github.com/nomeata/loogle"
    "9f11169aaebf1ed1e7dcc4077f2aafe0fcf66fd0"
    #[] "Apache-2.0" "2026-07-09"
    #[`Loogle] (moduleExcludes := #[`Tests])
    (notes := "The generic test root Tests collides at the source-module layer with Paperproof and Verso; public Loogle modules remain complete."),
  gitPackage "subverso" `SubVerso
    "https://github.com/leanprover/subverso"
    "3a75ede05278806fd3249bb0c97a6fb5777a4f7d"
    #[] "Apache-2.0" "2026-08-12"
    #[`SubVerso] (notes := "DELIBERATELY MULTI-TOOLCHAIN: its lakefile branches on Lean.versionString, so it is the one package here designed to tolerate skew. Pinning v4.29.0-rc7 while verso consumes it is intentional, not a bug -- do not 'fix' it. srcDir src. REV IS NOT main HEAD ON PURPOSE: this is the revision verso's own lake-manifest.json pins. Our root pin overrides verso's, so taking subverso's newer main (847084e8) silently broke verso -- MultiVerso/NameMap.lean failed on an identifier that resolves only under the tested pair. When the catalog pins a package another catalogued package depends on, prefer the consumer's tested revision over upstream HEAD."),
  gitPackage "verso" `Verso
    "https://github.com/leanprover/verso"
    "74fc8d1b7bb781c3623a06ec6484f34d35eb5fba"
    #["MD4Lean", "illuminate", "plausible", "subverso"] "Apache-2.0" "2026-08-14"
    #[`Verso] (moduleExcludes := #[`Tests])
    (notes := "The generic test root Tests collides at the source-module layer; all named Verso libraries remain inventoried."),
  gitPackage "CompPoly" `CompPoly
    "https://github.com/Verified-zkEVM/CompPoly"
    "75c0681bd37567af00e8f0bd13fd59f1423e4217"
    #["mathlib"] "Apache-2.0" "2026-08-11"
    #[`CompPoly] (notes := "Computable multivariate polynomials. Sets preferReleaseBuild AND fixedToolchain, so as a dependency it fetches prebuilt oleans and tries to dictate the workspace toolchain."),
  gitPackage "TorchLean" `TorchLean
    "https://github.com/lean-dojo/TorchLean"
    "fa6bbe3bf0d93679422be8a14978c26ee55d98ff"
    #["doc-gen4", "mathlib"] "MIT" "2026-08-11"
    #[`NN] (notes := "Neural-network specification/execution/verification with autograd. Root module is NN, NOT TorchLean. CUDA and LibTorch are opt-in and OFF by default, so the stock build compiles portable C stubs -- buildable without a GPU. Probes green; excluded only for the root-namespace Context collision."),
  gitPackage "lean-semver" `SemVer
    "https://github.com/runbikeswim/lean-semver"
    "b818b68404b788acc8521ebc5d1db7913d543337"
    #[] "Apache-2.0" "2026-06-09"
    #[`SemVer] (notes := "Semantic versioning parse and compare. Zero deps, self-contained. Probes green; excluded purely for root-namespace pollution."),
  gitPackage "illuminate" `Illuminate
    "https://github.com/leanprover/illuminate"
    "76f052847294d189dc9924a33466b4b677f47e67"
    #[] "Apache-2.0" "2026-08-10"
    #[`Illuminate] (notes := "Transitive Verso dependency pinned from the resolved Lean 4.33 workspace."),
  gitPackage "doc-gen4" `DocGen4
    "https://github.com/leanprover/doc-gen4"
    "aceca4eeb5a79092eabefaa75fcb72b701d02205"
    #["BibtexQuery", "Cli", "MD4Lean", "UnicodeBasic", "leansqlite"] "Apache-2.0" "2026-08-16"
    #[`DocGen4] (notes := "Official v4.33.0 release; the earlier v4.31.0 pin was rejected by the clean source-anchor build."),
  gitPackage "cslib" `Cslib
    "https://github.com/leanprover/cslib"
    "a1faa284cc5923ac11a4b8d2452749a174ef8cf1"
    #["mathlib"] "Apache-2.0" "2026-07-29"
    #[`Cslib] (notes := "Transitive dependency pinned from the resolved Lean 4.33 workspace."),
  gitPackage "BibtexQuery" `BibtexQuery
    "https://github.com/dupuisf/BibtexQuery"
    "5d31b64fb703c5d77f6ef4d1fb958f9bdf1ea539"
    #["UnicodeBasic"] "Apache-2.0" "2026-02-10"
    #[`BibtexQuery] (notes := "Transitive doc-gen4 dependency pinned from the resolved Lean 4.33 workspace."),

  /- Corpus-growth additions (the TruthMines `to_add` wishlist). These remain
  unadmitted candidates — records without membership in `catalogSpec` — until
  a successful probe on the unified toolchain admits them (Phase 4). -/
  gitPackage "Comparator" `Comparator
    "https://github.com/leanprover/Comparator"
    "777e7f56119efc0fac34003db4efe831e0b53723"
    #["lean4export"] "Apache-2.0" "2026-08-11"
    #[`Comparator] (notes := "Direct dependency of OpenAI ten-proofs."),
  gitPackage "ten-proofs" `TenProofs
    "https://github.com/openai/ten-proofs"
    "94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6"
    #["Comparator", "mathlib"] "Apache-2.0" "2026-08-01"
    #[`All] (notes := "OpenAI's ten formal proof developments; upstream targets Lean 4.32."),
  gitPackage "cdc_lean" `CDCLean
    "https://github.com/openai/cdc-lean"
    "577e9d9ea326d520f80672ee69b830bf1d513df5"
    #["mathlib"] "NOASSERTION" "2026-07-09"
    #[`CDCLean] (notes := "OpenAI CDC formalization; upstream targets Lean 4.31 and publishes no license file."),
  gitPackage "Zeta23" `Zeta23
    "https://github.com/anthropics/zeta-23-lean"
    "3635e74826a4c1fcece7d1cd2b6fa75e43a00510"
    #["mathlib"] "Apache-2.0" "2026-08-10"
    #[`Zeta23] (notes := "Anthropic's Zeta(3) irrationality formalization; upstream targets Lean 4.33-rc2."),
  gitPackage "formal_conjectures" `FormalConjectures
    "https://github.com/google-deepmind/formal-conjectures"
    "e7f4b0e92fac48ae221532dc2f4fbd42245afe53"
    #["mathlib"] "Apache-2.0" "2026-08-16"
    #[`FormalConjecturesForMathlib, `FormalConjecturesUtil]
    (notes := "Google DeepMind's complete conjecture corpus; upstream targets Lean 4.27."),
  gitPackage "alphaproof_nexus" `AlphaProofNexus
    "https://github.com/google-deepmind/alphaproof-nexus-results"
    "0647711a71183c1ea492ad60860776617ce1ea88"
    #["formal_conjectures"] "Apache-2.0" "2026-06-05"
    #[`APNOutputs.AICollaborator.Graphs.GraphConjecture2]
    (notes := "AlphaProof Nexus output corpus; upstream targets Lean 4.27."),
  gitPackage "imo" `FormalIMO
    "https://github.com/google-deepmind/formal-imo"
    "a85d84b97c8e88a352c136b1e29c355139609bea"
    #["formal_conjectures"] "Apache-2.0" "2026-04-23"
    #[`Imo.ProblemImports] (notes := "Google DeepMind formal IMO benchmark; upstream targets Lean 4.27."),
  gitPackage "putnam_like" `FormalPutnamLike
    "https://github.com/google-deepmind/formal-putnam-like"
    "9d6f67be000cd7ccaa0eedb9325e86e67afca6c7"
    #["mathlib"] "Apache-2.0" "2026-04-22"
    #[`PutnamLike.Set1.A1] (notes := "Google DeepMind Putnam-like benchmark; upstream targets Lean 4.27."),
  gitPackage "harmonic-imo-2025" `IMO2025
    "https://github.com/harmonic-ai/IMO2025"
    "72b62405a176a7eaeadb335a7fa6ee80b6667161"
    #["mathlib"] "NOASSERTION" "2025-07-29"
    #[`HarmonicLean] (notes := "Harmonic AI IMO 2025 formalizations; upstream targets Lean 4.20 and publishes no license file."),
  gitPackage "paucity" `PaucityLatticeTriangle
    "https://github.com/AxiomMath/PaucityLatticeTriangle"
    "445e6b5aad65472fb7a0658798075ea8caa87b9a"
    #["mathlib"] "Apache-2.0" "2026-08-16"
    #[`Paucity] (notes := "AxiomMath paucity/lattice-triangle development; upstream targets Lean 4.33-rc1."),
  gitPackage "QSeriesLib" `QSeriesLib
    "https://github.com/AxiomMath/QSeriesLib"
    "17dee1264538f988d6a2c1aeb028b417601bfe84"
    #["mathlib"] "NOASSERTION" "2026-08-16"
    #[`QSeriesLib] (notes := "AxiomMath q-series library; upstream targets Lean 4.34-rc1 and publishes no license file."),
  gitPackage "hjoa3small" `HJOa3Small
    "https://github.com/AxiomMath/HJOa3Small"
    "8bac91b6479a0036a4827096a9cf1c255112bf1a"
    #["QSeriesLib"] "Apache-2.0" "2026-08-13"
    #[`HJOA3] (notes := "AxiomMath HJO a3 development; upstream targets Lean 4.33-rc2."),

  gitPackage "LeanArchitect" `LeanArchitect
    "https://github.com/hanwenzhu/LeanArchitect"
    "d9013cc08bd2b5483e837368dfa4cc7ead92a5c2"
    #["Cli", "batteries"] "Apache-2.0" "2026-07-28"
    #[`Architect] (notes := "Dependency of PrimeNumberTheoremAnd; pinned to that package's resolved revision."),
  gitPackage "AgreeToDisagree" `AgreeToDisagree
    "https://github.com/AxiomMath/AgreeToDisagree"
    "22f70edcfa9b6def011d14ee47d6e2937dc5829f"
    #["mathlib"] "MIT" "2026-05-27"
    #[`AgreeToDisagree.AgreeToDisagree] (notes := "AxiomMath/AgreeToDisagree; added from the organization-wide library inventory."),
  gitPackage "BerkovichUncu" `BerkovichUncu
    "https://github.com/AxiomMath/BerkovichUncu"
    "30b8215213bb458fc940eb23752601c65d595fb8"
    #["mathlib"] "MIT" "2026-08-06"
    #[`BerkovichUncu.problem] (notes := "AxiomMath/BerkovichUncu; added from the organization-wide library inventory."),
  gitPackage "Biswal" `Biswal
    "https://github.com/AxiomMath/Biswal"
    "870ab95365358343d4b20869ac2ad50dd671af1f"
    #["mathlib"] "MIT" "2026-04-30"
    #[`Biswal.theorem1.problem] (notes := "AxiomMath/Biswal; added from the organization-wide library inventory."),
  gitPackage "Granville" `Granville
    "https://github.com/AxiomMath/Granville"
    "6e0d1cb2fad04c5a572ec0ff2ec23722e63e352b"
    #["mathlib"] "MIT" "2026-04-16"
    #[`Granville.section2.problem] (notes := "AxiomMath/Granville; added from the organization-wide library inventory."),
  gitPackage "HigherDyson" `HigherDyson
    "https://github.com/AxiomMath/HigherDyson"
    "ee40653229a23cb7ad048f96b630f1bcc3b047f2"
    #["mathlib"] "MIT" "2026-07-08"
    #[`Batch1.Output.problem] (notes := "AxiomMath/HigherDyson; added from the organization-wide library inventory."),
  gitPackage "IMO2026" `IMO2026
    "https://github.com/AxiomMath/IMO2026"
    "c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2"
    #["mathlib"] "MIT" "2026-07-17"
    #[`IMO2026.Q1.problem] (notes := "AxiomMath/IMO2026; added from the organization-wide library inventory."),
  gitPackage "LatentError" `LatentError
    "https://github.com/AxiomMath/LatentError"
    "7996b27ac9fc7d18a9899c947ce056c98e778101"
    #["mathlib"] "MIT" "2026-07-15"
    #[`LatentError.problem] (notes := "AxiomMath/LatentError; added from the organization-wide library inventory."),
  gitPackage "PartitionElliptic" `PartitionElliptic
    "https://github.com/AxiomMath/PartitionElliptic"
    "b1e1025e50328d734f2778349163a350de6d88d3"
    #["mathlib"] "MIT" "2026-07-13"
    #[`output.solution] (notes := "AxiomMath/PartitionElliptic; added from the organization-wide library inventory."),
  gitPackage "PartitionPolynomial" `PartitionPolynomial
    "https://github.com/AxiomMath/PartitionPolynomial"
    "5b53cfcac173af6488fbeca09a8a0ece7c44a190"
    #["mathlib"] "MIT" "2026-06-08"
    #[`PartitionPolynomial.Conjecture10.problem] (notes := "AxiomMath/PartitionPolynomial; added from the organization-wide library inventory."),
  gitPackage "PrimeGapsLib" `PrimeGapsLib
    "https://github.com/AxiomMath/PrimeGapsLib"
    "cddbc9291641545da52f06392c8ef46e1d6c6b7c"
    #["PrimeNumberTheoremAnd", "mathlib"] "Apache-2.0" "2026-08-08"
    #[`PrimeGaps] (notes := "AxiomMath/PrimeGapsLib; added from the organization-wide library inventory."),
  gitPackage "PrimeNumberTheoremAnd" `PrimeNumberTheoremAnd
    "https://github.com/AxiomMath/PrimeNumberTheoremAnd"
    "2667e414c38e5a5dc9aa1946f16f13001e5cd3ed"
    #["LeanArchitect", "mathlib"] "Apache-2.0" "2026-07-29"
    #[`PrimeNumberTheoremAnd] (notes := "AxiomMath/PrimeNumberTheoremAnd; added from the organization-wide library inventory."),
  gitPackage "Putnam2025" `Putnam2025
    "https://github.com/AxiomMath/Putnam2025"
    "2653cded72f5112acdc935b4f674711a780af95d"
    #["Qq", "aesop", "batteries", "mathlib"] "MIT" "2026-01-09"
    #[`Putnam2025.A1.problem] (notes := "AxiomMath/Putnam2025; added from the organization-wide library inventory."),
  gitPackage "QBinomialTrace" `QBinomialTrace
    "https://github.com/AxiomMath/QBinomialTrace"
    "7523432840f0e0d64853f71d8e543f08628fd683"
    #["mathlib"] "MIT" "2026-08-05"
    #[`QBinomialTrace.problem] (notes := "AxiomMath/QBinomialTrace; added from the organization-wide library inventory."),
  gitPackage "RRA3" `RRA3
    "https://github.com/AxiomMath/RR_a3"
    "1e11ae28f4f34c40d0fc1bc9562b243866cce565"
    #["QSeriesLib", "mathlib"] "MIT" "2026-08-05"
    #[`RRA3.problem] (notes := "AxiomMath/RR_a3; added from the organization-wide library inventory."),
  gitPackage "RogersRamanujan" `RogersRamanujan
    "https://github.com/AxiomMath/RogersRamanujan"
    "f391e2763f47243d4c252604aad65bbb2a22751a"
    #["mathlib"] "NOASSERTION" "2026-08-06"
    #[`RogersRamanujan] (notes := "AxiomMath/RogersRamanujan; added from the organization-wide library inventory."),
  gitPackage "TanArctan" `TanArctan
    "https://github.com/AxiomMath/TanArctan"
    "5382d3c20ee3f30e2cbd84362eb07a7e93250348"
    #["mathlib"] "MIT" "2026-07-06"
    #[`output.solution] (notes := "AxiomMath/TanArctan; added from the organization-wide library inventory."),
  gitPackage "Bijection" `Bijection
    "https://github.com/AxiomMath/andrews_dhar_problem"
    "5ed1a20ba1f39d9637e2f91e6779ce83c7da098f"
    #["mathlib"] "MIT" "2026-06-08"
    #[`Bijection.thm1.problem] (notes := "AxiomMath/andrews_dhar_problem; added from the organization-wide library inventory."),
  gitPackage "Challenge_3" `Challenge3
    "https://github.com/AxiomMath/challenge_3"
    "fe8bba1b37f19db75a760630a59da7baf35697a8"
    #["mathlib"] "MIT" "2026-06-05"
    #[`Challenge_3.«lemma-b2».problem] (notes := "AxiomMath/challenge_3; added from the organization-wide library inventory."),
  gitPackage "Deadends" `Deadends
    "https://github.com/AxiomMath/dead-ends"
    "80fc9124841a1f37a167d227d00780479d04f701"
    #["mathlib"] "MIT" "2026-03-25"
    #[`Deadends.problem] (notes := "AxiomMath/dead-ends; added from the organization-wide library inventory."),
  gitPackage "Erdos" `Erdos
    "https://github.com/AxiomMath/erdos-public"
    "3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab"
    #["mathlib"] "MIT" "2026-06-18"
    #[`Erdos.Erdos1134.problem] (notes := "AxiomMath/erdos-public; added from the organization-wide library inventory."),
  gitPackage "FelConjecture" `FelConjecture
    "https://github.com/AxiomMath/fel-polynomial"
    "d22b0961e4ceafabae3d33b07d645ece7c1cf23f"
    #["mathlib"] "MIT" "2026-03-25"
    #[`FelConjecture.problem] (notes := "AxiomMath/fel-polynomial; added from the organization-wide library inventory."),
  gitPackage "GDMFormalConjecture" `GDMFormalConjecture
    "https://github.com/AxiomMath/gdm-formal-conjectures"
    "7944bd15b135bc0cecfca5d65798dd92ea707259"
    #["mathlib"] "MIT" "2026-03-26"
    #[`BorweinSineSeries.problem] (notes := "AxiomMath/gdm-formal-conjectures; added from the organization-wide library inventory."),
  gitPackage "Kaprekar4" `Kaprekar4
    "https://github.com/AxiomMath/kaprekar4"
    "1e772ddbcb6f24a3270ded635e93225bb38ed474"
    #["mathlib"] "MIT" "2026-06-11"
    #[`Kaprekar4.problem] (notes := "AxiomMath/kaprekar4; added from the organization-wide library inventory."),
  gitPackage "LatticeTriangle" `LatticeTriangle
    "https://github.com/AxiomMath/lattice-triangle"
    "cab34f26cf1ca3824c171a4bd5729179a941315f"
    #["mathlib"] "MIT" "2026-03-25"
    #[`LatticeTriangle.problem] (notes := "AxiomMath/lattice-triangle; added from the organization-wide library inventory."),
  gitPackage "ParityDifferential" `ParityDifferential
    "https://github.com/AxiomMath/parity-differential"
    "53665b5dd0c97d7f897dfbc86e40b896e0662dbc"
    #["mathlib"] "MIT" "2026-03-25"
    #[`ParityDifferential.problem] (notes := "AxiomMath/parity-differential; added from the organization-wide library inventory."),
  gitPackage "PartialRegularity" `PartialRegularity
    "https://github.com/AxiomMath/partial-regularity"
    "4f9bb24200dc424b25b0f5c267e712c835ca2153"
    #["mathlib"] "MIT" "2026-03-25"
    #[`PartialRegularity.problem] (notes := "AxiomMath/partial-regularity; added from the organization-wide library inventory."),
  gitPackage "QuadraticDinv" `QuadraticDinv
    "https://github.com/AxiomMath/quadratic-dinv"
    "2bafc2404acf85538e609fbf688bd91918d21c51"
    #["mathlib"] "MIT" "2026-04-13"
    #[`QuadraticDinv.problem] (notes := "Catalog alias avoids the upstream package-name typo `Deadends`."),
  gitPackage "RamanujanTauMissesPrimes" `RamanujanTauMissesPrimes
    "https://github.com/AxiomMath/ramanujan-tau-misses-primes"
    "9838fcaf026df5b47251a9915d34c4bf4d906cf2"
    #["mathlib"] "MIT" "2026-04-23"
    #[`RamanujanTauMissesPrimes.problem] (notes := "AxiomMath/ramanujan-tau-misses-primes; added from the organization-wide library inventory."),
  gitPackage "RecordCompositions" `RecordCompositions
    "https://github.com/AxiomMath/record-compositions"
    "42609ea4168a21090c213f252f25e6fc162965fb"
    #["mathlib"] "MIT" "2026-07-15"
    #[`RecordCompositions.problem] (notes := "AxiomMath/record-compositions; added from the organization-wide library inventory."),
  gitPackage "ZetaH123" `ZetaH123
    "https://github.com/AxiomMath/zeta-h123"
    "c466141482fafe93d018d16997505acfd6a4c377"
    #["mathlib"] "MIT" "2026-06-15"
    #[`H1.problem] (notes := "AxiomMath/zeta-h123; added from the organization-wide library inventory."),

  excludedGitPackage "certigrad" `Certigrad
    "https://github.com/dselsam/certigrad"
    "c9a06e93f1ec58196d6d3b8563b29868d916727f"
    "Apache-2.0" "2019-03-03" "Lean 3 leanpkg project; not a Lean 4 Lake package.",
  excludedGitPackage "veil" `Veil
    "https://github.com/verse-lab/veil"
    "300c305e945750ab3fb62de4a79c23161b24da39"
    "Apache-2.0" "2026-08-13"
    "Not hermetic yet: its default library builds an npm widget and requires uncatalogued smt/Loom/auto/cvc5 packages.",
  excludedGitPackage "SSA" `LeanMLIR
    "https://github.com/opencompl/lean-mlir"
    "b8c4a771319a044854a4bbb49b8821381ef86ff8"
    "Apache-2.0" "2026-07-28"
    "Nightly multi-package workspace with local subpackages and uncatalogued solver/RISC-V dependencies; not yet compatible with the unified 4.33 graph.",
  excludedGitPackage "xena" `Xena
    "https://github.com/kbuzzard/xena"
    "268b3bab45ba8fbed09b45cbbdc80a3813f73b5e"
    "NOASSERTION" "2025-02-14" "Historical Lean 3 file collection with no Lake package."
]

def catalogPackage? (lakeName : String) : Option PackageSpec :=
  catalog.find? (·.lakeName == lakeName)

def catalogQualifier? (qualifier : Lean.Name) : Option PackageSpec :=
  catalog.find? (·.qualifier == qualifier)

end TruthMinesSpec
