import Lake

open System Lake DSL

package compilatrix

/- Exact pure Ixby reference, pinned independently of its proving backends. -/
lean_lib Ixby where
  srcDir := "vendor/ixby"
  roots := #[`Ix.Ixby]

/- Exact source reference for Stage2 differential execution tests. -/
lean_lib Stage2Source where
  srcDir := "vendor/stage2"
  roots := #[`Ix.MultiStark.Verify]

/- Blake3 FFI. Keep this revision in lockstep with the flake's
`blake3-lean` input and `lake-manifest.json`. -/
require Blake3 from git
  "https://github.com/argumentcomputer/Blake3.lean" @
  "aaf530784082a2c00b0a93648741429d274102ca"

/- The portable Lean filesystem API stops at buffered flush. Compile the
small, ledgered POSIX durability boundary as a normal traced Lake input. -/
target hpt_cache_sync pkg : FilePath := do
  let source ← inputTextFile <| pkg.dir / "native/hpt_cache_sync.c"
  let object := pkg.buildDir / "native" / "hpt_cache_sync.o"
  let includeDir ← getLeanIncludeDir
  let weakArgs := #["-fPIC", "-I", includeDir.toString]
  buildO object source weakArgs #[] "cc" getLeanTrace

@[default_target]
lean_lib Compilatrix where
  roots := #[`Compilatrix]
  moreLinkObjs := #[hpt_cache_sync]

/- Runtime tests (FFI execution cannot run in elaboration-time `#guard`s). -/
lean_exe tests where
  root := `Tests

lean_exe «catalog-contact» where
  root := `CatalogContact

/- Emit deterministic ELF fixtures for the independent object/link gate. -/
lean_exe «x86-object-fixture» where
  root := `X86ObjectFixture

/- Source-stage coverage and fresh-process compiler artifact snapshots. -/
lean_exe «ixon-to-ixby» where
  root := `IxonToIxby

lean_exe «ixby-run» where
  srcDir := "scripts"
  root := `IxbyRun

lean_exe «check-ixby» where
  srcDir := "scripts"
  root := `CheckIxby

lean_exe «source-ixby» where
  root := `SourceIxby

lean_exe «source-ixby-symbolic» where
  root := `SourceIxbySymbolic

lean_exe «source-ixby-stage2» where
  root := `SourceIxbyStage2

lean_exe «stage2-source-run» where
  srcDir := "scripts"
  root := `Stage2SourceRun

lean_exe «check-ixby-stage2» where
  srcDir := "scripts"
  root := `CheckIxbyStage2

lean_exe «check-ixby-symbolic» where
  srcDir := "scripts"
  root := `CheckIxbySymbolic

lean_exe «source-coverage» where
  root := `SourceCoverage

/- Independently checked source units and dependency-edit replay. -/
lean_exe «source-modular» where
  root := `SourceModular

lean_exe «check-source-modular» where
  srcDir := "scripts"
  root := `CheckSourceModular

/- Source recursor recovery and dynamic-reuse observations. -/
lean_exe «source-recursion» where
  root := `SourceRecursion

/- Source maps and reuse across continuation-owned call credits. -/
lean_exe «source-call-reuse» where
  root := `SourceCallReuse

/- Finite physical heap and explicit control storage across allocating calls. -/
lean_exe «source-space» where
  root := `SourceSpace

/- Canonical IxIR₂ snapshots and source-produced persistence witnesses. -/
lean_exe «ixir2-fixture» where
  root := `IxIR2Fixture

/- Unique-major recursor and static-reuse source observations. -/
lean_exe «source-unique-reuse» where
  root := `SourceUniqueReuse

/- Bounded native unique reversal, compiled from checked Ixon fixtures. -/
lean_exe «source-native-unique» where
  root := `SourceNativeUnique

/- One compiled function, with caller-supplied unique list arguments. -/
lean_exe «source-native-runtime» where
  root := `SourceNativeRuntime

lean_exe «source-native-allocating» where
  root := `SourceNativeAllocating

lean_exe «source-native-upstream» where
  root := `SourceNativeUpstream

/- Runtime scalar arguments, exact Nat arithmetic, branches, joins, and calls. -/
lean_exe «source-native-scalar» where
  root := `SourceNativeScalar

lean_exe «source-native-physical-scalar» where
  root := `SourceNativePhysicalScalar

lean_exe «source-native-captured-scalar» where
  root := `SourceNativeCapturedScalar

/- Compositional leaf allocation, finite workspaces, and physical snapshots. -/
lean_exe «source-native-heap» where
  root := `SourceNativeHeap

lean_exe «heap-snapshot-object» where
  root := `HeapSnapshotObject

/- Checked borrowed calls from accepted source, with complete RC observations. -/
lean_exe «source-borrow» where
  root := `SourceBorrow

/- Borrowed direct calls with caller-supplied shared inputs. -/
lean_exe «source-borrow-runtime» where
  root := `SourceBorrowRuntime

/- Repository checks are Lean programs, including the independent tool oracles. -/
lean_exe «check-x86-encoder» where
  srcDir := "scripts"
  root := `CheckX86Encoder

lean_exe «check-x86-bytes» where
  srcDir := "scripts"
  root := `CheckX86Bytes

lean_exe «check-x86-streams» where
  srcDir := "scripts"
  root := `CheckX86Streams

lean_exe «check-x86-object» where
  srcDir := "scripts"
  root := `CheckX86Object

lean_exe «check-trusted-externs» where
  srcDir := "scripts"
  root := `CheckTrustedExterns

lean_exe «check-source-coverage» where
  srcDir := "scripts"
  root := `CheckSourceCoverage

lean_exe «check-source-recursion» where
  srcDir := "scripts"
  root := `CheckSourceRecursion

lean_exe «check-source-call-reuse» where
  srcDir := "scripts"
  root := `CheckSourceCallReuse

lean_exe «check-source-space» where
  srcDir := "scripts"
  root := `CheckSourceSpace

lean_exe «check-ixir2» where
  srcDir := "scripts"
  root := `CheckIxIR2

lean_exe «check-source-unique-reuse» where
  srcDir := "scripts"
  root := `CheckSourceUniqueReuse

lean_exe «check-source-native-unique» where
  srcDir := "scripts"
  root := `CheckSourceNativeUnique

lean_exe «check-source-native-runtime» where
  srcDir := "scripts"
  root := `CheckSourceNativeRuntime

lean_exe «check-source-native-allocating» where
  srcDir := "scripts"
  root := `CheckSourceNativeAllocating

lean_exe «check-source-native-upstream» where
  srcDir := "scripts"
  root := `CheckSourceNativeUpstream

lean_exe «check-source-native-scalar» where
  srcDir := "scripts"
  root := `CheckSourceNativeScalar

lean_exe «check-source-native-physical-scalar» where
  srcDir := "scripts"
  root := `CheckSourceNativePhysicalScalar

lean_exe «check-source-native-heap» where
  srcDir := "scripts"
  root := `CheckSourceNativeHeap

lean_exe «check-source-native-captured-scalar» where
  srcDir := "scripts"
  root := `CheckSourceNativeCapturedScalar

lean_exe «check-source-borrow» where
  srcDir := "scripts"
  root := `CheckSourceBorrow

lean_exe «check-source-borrow-runtime» where
  srcDir := "scripts"
  root := `CheckSourceBorrowRuntime

/- Deterministic datasets and native comparison-suite orchestration. -/
lean_lib Benchmark where
  srcDir := "benchmarks"

lean_exe benchmark where
  srcDir := "benchmarks"
  root := `Benchmark

/- Fresh-process compiler scaling workers and artifact replay. -/
lean_exe «compiler-scaling» where
  srcDir := "benchmarks"
  root := `CompilerScaling

lean_exe «check-tools-tests» where
  srcDir := "scripts"
  root := `CheckToolsTests

/- Fixed-limit native join emission and baseline comparison. -/
lean_exe «native-sharing» where
  srcDir := "benchmarks"
  root := `NativeSharing

lean_exe «native-graph» where
  srcDir := "benchmarks"
  root := `NativeGraph

lean_exe «check-native-graph» where
  srcDir := "scripts"
  root := `CheckNativeGraph

lean_exe «check-native-sharing» where
  srcDir := "scripts"
  root := `CheckNativeSharing

/- Modular assembly phases and exact reference addressing comparisons. -/
lean_exe «assembly-scaling» where
  srcDir := "benchmarks"
  root := `AssemblyScaling

lean_exe «check-assembly-scaling» where
  srcDir := "scripts"
  root := `CheckAssemblyScaling

lean_exe «source-evidence» where
  srcDir := "benchmarks"
  root := `SourceEvidence

lean_exe «check-source-evidence» where
  srcDir := "scripts"
  root := `CheckSourceEvidence
