{
  description = "Compilatr.ix: a certified Lean 4 toolchain for Ix";

  nixConfig = {
    extra-substituters = [
      "https://argumentcomputer.cachix.org"
    ];
    extra-trusted-public-keys = [
      "argumentcomputer.cachix.org-1:ovhbTx1V56BYDerOWInQvXKXl68LlhNwEA+n7EWk1m4="
    ];
  };

  inputs = {
    # System packages, follows lean4-nix so we stay in sync
    nixpkgs.follows = "lean4-nix/nixpkgs";

    # Lean 4 & Lake. Pinned to the exact rev lean4lean locks so the
    # toolchain derivation dedups with its builds; move deliberately.
    lean4-nix.url = "github:argumentcomputer/lean4-nix/c41a770e44a990da275dad0f70da75f22197e597";

    # flake-parts via the copy lean4-nix already locks (single node)
    flake-parts.follows = "lean4-nix/flake-parts";

    # Blake3 FFI: the flake-built package (prebuilt Rust static lib)
    # overrides the Lake dep, whose lakefile shells out to cargo — the
    # sandbox forbids that. Keep the rev in lockstep with
    # lakefile.lean/lake-manifest.json. Nested inputs (crane, fenix,
    # blake3 source, flake-parts) are pinned at lock time to ix's
    # flake.lock revs — the combination proven on this machine.
    # Share the toolchain helper so Lean modules and Rust FFI headers use
    # the same reviewed Lean release and Nix derivation.
    blake3-lean.url = "github:argumentcomputer/Blake3.lean/c9b2273fb9c2c33b94eba091dc4111163f5db2bc";
    blake3-lean.inputs.lean4-nix.follows = "lean4-nix";
  };

  outputs = inputs @ {
    flake-parts,
    lean4-nix,
    blake3-lean,
    ...
  }: let
    # Crane's own Rust helper uses nixpkgs' Cargo fetcher, independently of
    # Crane's normal static.crates.io registry. The crates.io API endpoint can
    # reject CI downloads; change only that host, retaining TLS verification,
    # the upstream lockfile/checksums, and the existing fixed-output paths.
    crane = blake3-lean.inputs.crane;
    craneWithStaticCrates =
      crane
      // {
        mkLib = pkgs:
          (crane.mkLib pkgs).overrideScope (_final: prev: {
            craneUtils = prev.craneUtils.overrideAttrs (old: {
              cargoDeps =
                (pkgs.rustPlatform.importCargoLock.override {
                  fetchurl = args:
                    pkgs.fetchurl (args
                      // {
                        url =
                          pkgs.lib.replaceStrings
                          ["https://crates.io/api/v1/crates/"]
                          ["https://static.crates.io/crates/"]
                          args.url;
                      });
                }) {
                  lockFile = old.cargoDeps.lockFile;
                };
            });
          });
      };
    # Reuse the pinned upstream flake and all its other inputs unchanged.
    blake3WithStaticCrates =
      assert builtins.readFile (blake3-lean.outPath + "/lean-toolchain")
        == builtins.readFile ./lean-toolchain;
      (import (blake3-lean.outPath + "/flake.nix")).outputs
      (blake3-lean.inputs
        // {
          self = blake3-lean;
          crane = craneWithStaticCrates;
        });
  in
    flake-parts.lib.mkFlake {inherit inputs;} {
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];

      perSystem = {
        system,
        pkgs,
        ...
      }: let
        # Pinned Lean toolchain, resolved from ./lean-toolchain.
        # Pin changes follow the compatibility gates in docs/roadmap.md.
        lean = lean4-nix.lib.${system}.fromToolchainFile ./lean-toolchain;
        lake2nix = pkgs.callPackage lean4-nix.lake {inherit lean;};
        # Restrict build inputs to Lean-relevant files so edits to
        # unrelated files don't invalidate cached Lean derivations.
        leanSrc = pkgs.lib.fileset.toSource {
          root = ./.;
          fileset = pkgs.lib.fileset.unions [
            ./lakefile.lean
            ./lake-manifest.json
            ./lean-toolchain
            ./native/hpt_cache_sync.c
            ./Compilatrix.lean
            ./Tests.lean
            ./CatalogContact.lean
            ./X86ObjectFixture.lean
            ./SourceCoverage.lean
            ./SourceIxby.lean
            ./SourceIxbySymbolic.lean
            ./SourceIxbyStage2.lean
            ./IxonToIxby.lean
            ./vendor/ixby
            ./vendor/stage2
            ./fixtures/ixby
            ./fixtures/ixby-symbolic
            ./fixtures/ixby-stage2
            ./SourceModular.lean
            ./SourceRecursion.lean
            ./SourceCallReuse.lean
            ./SourceSpace.lean
            ./IxIR2Fixture.lean
            ./SourceUniqueReuse.lean
            ./SourceNativeUnique.lean
            ./SourceNativeRuntime.lean
            ./SourceNativeAllocating.lean
            ./SourceNativeUpstream.lean
            ./SourceNativeScalar.lean
            ./SourceNativePhysicalScalar.lean
            ./SourceNativeHeap.lean
            ./HeapSnapshotObject.lean
            ./SourceNativeCapturedScalar.lean
            ./benchmarks/Benchmark
            ./benchmarks/AssemblyScaling.lean
            ./benchmarks/NativeGraph.lean
            ./benchmarks/NativeSharing.lean
            ./benchmarks/SourceEvidence.lean
            ./benchmarks/native/scaling_harness.c
            ./SourceBorrow.lean
            ./SourceBorrowRuntime.lean
            ./fixtures/ixon-std-contact
            ./fixtures/ixon-upstream
            ./fixtures/source-coverage
            ./fixtures/source-modular
            ./fixtures/assembly-scaling
            ./fixtures/source-evidence
            ./fixtures/compiler-scaling
            ./fixtures/native-sharing
            ./fixtures/native-graph
            ./fixtures/source-recursion
            ./fixtures/source-call-reuse
            ./fixtures/source-space
            ./fixtures/ixir2
            ./fixtures/source-unique-reuse
            ./fixtures/source-native-unique
            ./fixtures/source-native-runtime
            ./fixtures/source-native-allocating
            ./fixtures/source-native-upstream
            ./fixtures/source-native-scalar
            ./fixtures/source-native-physical-scalar
            ./fixtures/source-native-heap
            ./fixtures/source-native-captured-scalar
            ./fixtures/source-borrow
            ./fixtures/source-borrow-runtime
            (pkgs.lib.fileset.fileFilter (f: f.hasExt "lean") ./Compilatrix)
            (pkgs.lib.fileset.fileFilter (f: f.hasExt "lean") ./scripts)
            ./scripts/inspect_ixby.py
          ];
        };
        # The trust-ledger check reads build metadata, CI pins, and every
        # Lean import, but keeping it separate preserves the library's
        # narrow source hash/cache boundary. It must see the complete
        # .github/workflows directory (so an unpinned action in any
        # workflow fails, not just ci.yml) and .envrc (it injects
        # NIX_CONFIG for direnv users, so it is ledger-tracked).
        auditSrc = pkgs.lib.fileset.toSource {
          root = ./.;
          fileset = pkgs.lib.fileset.unions [
            ./flake.nix
            ./flake.lock
            ./lakefile.lean
            ./lake-manifest.json
            ./lean-toolchain
            ./native/hpt_cache_sync.c
            ./.envrc
            ./Compilatrix.lean
            ./Tests.lean
            ./CatalogContact.lean
            ./X86ObjectFixture.lean
            ./SourceCoverage.lean
            ./SourceIxby.lean
            ./SourceIxbySymbolic.lean
            ./SourceIxbyStage2.lean
            ./IxonToIxby.lean
            ./vendor/ixby
            ./vendor/stage2
            ./fixtures/ixby
            ./fixtures/ixby-symbolic
            ./fixtures/ixby-stage2
            ./SourceModular.lean
            ./SourceRecursion.lean
            ./SourceCallReuse.lean
            ./SourceSpace.lean
            ./IxIR2Fixture.lean
            ./SourceUniqueReuse.lean
            ./SourceNativeUnique.lean
            ./SourceNativeRuntime.lean
            ./SourceNativeAllocating.lean
            ./SourceNativeUpstream.lean
            ./SourceNativeScalar.lean
            ./SourceNativePhysicalScalar.lean
            ./SourceNativeHeap.lean
            ./HeapSnapshotObject.lean
            ./SourceNativeCapturedScalar.lean
            # Audit optional comparison sources without including their local
            # build products or retained measurement bundles.
            (pkgs.lib.fileset.difference ./benchmarks (pkgs.lib.fileset.unions [
              (pkgs.lib.fileset.maybeMissing ./benchmarks/comparisons/.lake)
              (pkgs.lib.fileset.maybeMissing ./benchmarks/runs)
            ]))
            ./SourceBorrow.lean
            ./SourceBorrowRuntime.lean
            ./fixtures/ixon-std-contact
            ./fixtures/ixon-upstream
            ./fixtures/source-coverage
            ./fixtures/source-modular
            ./fixtures/assembly-scaling
            ./fixtures/source-evidence
            ./fixtures/compiler-scaling
            ./fixtures/native-sharing
            ./fixtures/native-graph
            ./fixtures/source-recursion
            ./fixtures/source-call-reuse
            ./fixtures/source-space
            ./fixtures/ixir2
            ./fixtures/source-unique-reuse
            ./fixtures/source-native-unique
            ./fixtures/source-native-runtime
            ./fixtures/source-native-allocating
            ./fixtures/source-native-upstream
            ./fixtures/source-native-scalar
            ./fixtures/source-native-physical-scalar
            ./fixtures/source-native-heap
            ./fixtures/source-native-captured-scalar
            ./fixtures/source-borrow
            ./fixtures/source-borrow-runtime
            ./fixtures/x86/native_harness.c
            (pkgs.lib.fileset.fileFilter (f: f.hasExt "lean") ./Compilatrix)
            ./docs/trusted-externs.json
            ./docs/x86-reference-model.json
            (pkgs.lib.fileset.fileFilter (f: f.hasExt "lean") ./scripts)
            ./scripts/inspect_ixby.py
            ./.github/workflows
          ];
        };
        lakeDeps = lake2nix.buildDeps {
          src = leanSrc;
          depOverrideDeriv = {
            Blake3 = blake3WithStaticCrates.packages.${system}.rust;
          };
        };
        leanBuildInputs = [
          pkgs.gmp
          lean
          pkgs.rsync
        ];

        # The library artifact: oleans + exports + static/shared facets,
        # consumable by downstream Lake packages (the lean4lean pattern).
        compilatrixLib = lake2nix.mkPackage {
          inherit lakeDeps;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "Compilatrix";
          buildLibrary = true;
          meta = {
            description = "Compilatrix library artifact (oleans, exports, static/shared)";
          };
        };

        # Runtime tests: build the `tests` exe (linking the Blake3 static
        # lib) and run it — FFI execution can't happen in elaboration-time
        # #guards, so the run is the test.
        testsCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "tests";
          installArtifacts = false;
          postBuild = ''
            ./.lake/build/bin/tests | tee tests.out
            grep -q tests-ok tests.out
          '';
        };

        # Compile the standalone directory adapter/contact executable as its
        # own target. The byte-exact outcome is exercised by `tests`; this
        # check prevents the operational CLI root from silently going stale.
        catalogContactCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "catalog-contact";
          installArtifacts = false;
        };

        # Fail closed when source imports, native symbols, dependency
        # graphs, build pins, or CI actions drift from the reviewed ledger.
        trustedExternCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          src = leanSrc;
          buildInputs = leanBuildInputs ++ [pkgs.coreutils];
          name = "check-trusted-externs";
          installArtifacts = false;
          postBuild = ''
            lake build check-tools-tests
            ./.lake/build/bin/check-trusted-externs \
              --root ${auditSrc} \
              --dependency-root Blake3=${blake3-lean.outPath} \
              --gmp-version ${pkgs.gmp.version}
            ./.lake/build/bin/check-tools-tests \
              --root ${auditSrc} --blake3 ${blake3-lean.outPath}
          '';
        };

        # Retain GNU decoding as an external oracle alongside E1's local
        # encoding/execution proofs and compiled byte-evaluator matrix.
        x86EncoderCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          src = leanSrc;
          buildInputs = leanBuildInputs ++ [pkgs.binutils];
          name = "check-x86-encoder";
          installArtifacts = false;
          postBuild = ''
            ./.lake/build/bin/check-x86-encoder \
              --objdump ${pkgs.binutils}/bin/objdump
          '';
        };

        x86BytesCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "check-x86-bytes";
          installArtifacts = false;
          postBuild = ''
            ./.lake/build/bin/check-x86-bytes
          '';
        };

        x86StreamsCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "check-x86-streams";
          installArtifacts = false;
          postBuild = ''
            ./.lake/build/bin/check-x86-streams
          '';
        };

        # Parse each Lean-written ELF object with GNU binutils.  On the
        # matching host ABI, also link and execute all seven fixtures; other
        # supported hosts retain the deterministic parse/disassembly gate.
        x86ObjectNativeArgs =
          pkgs.lib.optionalString (system == "x86_64-linux")
          "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/x86/native_harness.c";
        x86ObjectCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          src = leanSrc;
          buildInputs =
            leanBuildInputs
            ++ [pkgs.binutils]
            ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc];
          name = "x86-object-fixture";
          installArtifacts = false;
          postBuild = ''
            lake build check-x86-object
            ./.lake/build/bin/check-x86-object \
              --fixture ./.lake/build/bin/x86-object-fixture \
              --readelf ${pkgs.binutils}/bin/readelf \
              --objdump ${pkgs.binutils}/bin/objdump ${x86ObjectNativeArgs}
          '';
        };

        # C1 compares complete source compiler artifacts across two fresh
        # processes and checks the frozen coverage/identity/counter matrix.
        sourceCoverageCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs =
            leanBuildInputs
            ++ [pkgs.binutils]
            ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc];
          name = "source-coverage";
          installArtifacts = false;
          postBuild = ''
            lake build check-source-coverage
            ./.lake/build/bin/check-source-coverage \
              --fixture ./.lake/build/bin/source-coverage \
              --contact ${auditSrc}/fixtures/ixon-std-contact \
              --upstream ${auditSrc}/fixtures/ixon-upstream \
              --expected ${auditSrc}/fixtures/source-coverage/expected.json \
              --readelf ${pkgs.binutils}/bin/readelf \
              --objdump ${pkgs.binutils}/bin/objdump ${x86ObjectNativeArgs}
          '';
        };

        # D1 checks the exact source recursion/counter matrix and compares
        # every program snapshot from two fresh compiler processes.
        sourceRecursionCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "source-recursion";
          installArtifacts = false;
          postBuild = ''
            lake build check-source-recursion
            ./.lake/build/bin/check-source-recursion \
              --fixture ./.lake/build/bin/source-recursion \
              --expected ${auditSrc}/fixtures/source-recursion/expected.json
          '';
        };

        # R5 checks source maps, suspended reservations, and all execution
        # prefixes in complete snapshots from two fresh compiler processes.
        sourceCallReuseCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "source-call-reuse";
          installArtifacts = false;
          postBuild = ''
            lake build check-source-call-reuse
            ./.lake/build/bin/check-source-call-reuse \
              --fixture ./.lake/build/bin/source-call-reuse \
              --expected ${auditSrc}/fixtures/source-call-reuse/expected.json
          '';
        };

        # F1 checks committed/live/reserved bytes and every explicit caller
        # frame, exact capacity failures, and complete result reclamation.
        sourceSpaceCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "source-space";
          installArtifacts = false;
          postBuild = ''
            lake build check-source-space
            ./.lake/build/bin/check-source-space \
              --fixture ./.lake/build/bin/source-space \
              --expected ${auditSrc}/fixtures/source-space/expected.json
          '';
        };

        # Bounded source units, exact dependency reuse, and fresh proof recovery.
        sourceModularCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "source-modular";
          installArtifacts = false;
          postBuild = ''
            lake build check-source-modular
            ./.lake/build/bin/check-source-modular \
              --fixture ./.lake/build/bin/source-modular \
              --expected ${auditSrc}/fixtures/source-modular/expected.json
          '';
        };

        # Indexed assembly, reference artifacts, source edits, and retained checks.
        assemblyScalingCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "assembly-scaling";
          installArtifacts = false;
          postBuild = ''
            lake build check-assembly-scaling
            ./.lake/build/bin/check-assembly-scaling \
              --fixture ./.lake/build/bin/assembly-scaling \
              --expected ${auditSrc}/fixtures/assembly-scaling/expected.json \
              --modular-expected ${auditSrc}/fixtures/source-modular/expected.json
          '';
        };

        # Exact canonical-address reuse, prepared source checking, and replay.
        sourceEvidenceCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "source-evidence";
          installArtifacts = false;
          postBuild = ''
            lake build check-source-evidence
            ./.lake/build/bin/check-source-evidence \
              --fixture ./.lake/build/bin/source-evidence \
              --expected ${auditSrc}/fixtures/source-evidence/expected.json \
              --modular-expected ${auditSrc}/fixtures/source-modular/expected.json
          '';
        };

        # Checked Ixon-to-Ixby compilation against the exact pinned reference machine.
        ixbyCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs ++ [pkgs.coreutils];
          name = "source-ixby";
          installArtifacts = false;
          postBuild = ''
            lake build check-ixby ixby-run ixon-to-ixby
            ./.lake/build/bin/check-ixby \
              --fixture ./.lake/build/bin/source-ixby \
              --runner ./.lake/build/bin/ixby-run \
              --compiler ./.lake/build/bin/ixon-to-ixby \
              --root ${auditSrc} \
              --expected ${auditSrc}/fixtures/ixby/expected.json \
              --upstream ${auditSrc}/fixtures/ixon-upstream
          '';
        };

        # One checked image theorem reused across fresh runtime argument arrays.
        ixbySymbolicCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "source-ixby-symbolic";
          installArtifacts = false;
          postBuild = ''
            lake build check-ixby-symbolic ixby-run ixon-to-ixby
            ./.lake/build/bin/check-ixby-symbolic \
              --fixture ./.lake/build/bin/source-ixby-symbolic \
              --runner ./.lake/build/bin/ixby-run \
              --compiler ./.lake/build/bin/ixon-to-ixby \
              --expected ${auditSrc}/fixtures/ixby-symbolic/expected.json \
              --upstream ${auditSrc}/fixtures/ixon-upstream
          '';
        };

        # Fixed Stage2 source data and its exact current admission frontier.
        ixbyStage2Check = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs ++ [pkgs.coreutils pkgs.gzip];
          name = "source-ixby-stage2";
          installArtifacts = false;
          postBuild = ''
            lake build check-ixby-stage2 stage2-source-run
            ./.lake/build/bin/check-ixby-stage2 \
              --fixture ./.lake/build/bin/source-ixby-stage2 \
              --source-runner ./.lake/build/bin/stage2-source-run \
              --root ${auditSrc} \
              --inputs ${auditSrc}/fixtures/ixby-stage2 \
              --expected ${auditSrc}/fixtures/ixby-stage2/expected.json
          '';
        };

        # Experimental typed lowering: differential tests and actual execution
        # of the pinned Stage2 proof on the unchanged reference machine.
        ixbyLeanCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs ++ [pkgs.coreutils pkgs.gzip pkgs.diffutils pkgs.python3];
          name = "check-ixby-lean";
          installArtifacts = false;
          postBuild = ''
            lake env ./.lake/build/bin/check-ixby-lean
            lake build stage2-ixby ixby-exec check-ixby-binary
            ./.lake/build/bin/check-ixby-binary binary-cases
            for image in binary-cases/*.ixby; do
              python3 scripts/inspect_ixby.py "$image" > /dev/null
            done
            cp ./.lake/build/bin/ixby-exec binary-cases/ixby-exec
            (
              cd binary-cases
              env -u LEAN_PATH ./ixby-exec identity.ixby identity.ixbi actual.ixbo
              cmp identity.ixbo actual.ixbo
            )
            lake env ./.lake/build/bin/stage2-ixby ${auditSrc}/fixtures/ixby-stage2 compile stage2.ixby
            lake env ./.lake/build/bin/stage2-ixby ${auditSrc}/fixtures/ixby-stage2 compile replay.ixby
            cmp stage2.ixby replay.ixby
            cmp stage2.ixby.json replay.ixby.json
            cmp ${auditSrc}/fixtures/ixby-stage2/stage2.ixby stage2.ixby
            diff -u ${auditSrc}/fixtures/ixby-stage2/reference-inventory.json stage2.ixby.json
            python3 scripts/inspect_ixby.py stage2.ixby --expected stage2.ixby.json
            for case in wrong-claim-kind trailing-public empty-proof malformed-proof truncated-proof trailing-proof claim-mismatch valid; do
              env -u LEAN_PATH ./.lake/build/bin/stage2-ixby ${auditSrc}/fixtures/ixby-stage2 "$case" stage2.ixby
            done
          '';
        };

        # Strict bounded IxIR₂ wire identity, source-produced snapshots,
        # independent decoding, and exact fresh-process artifact replay.
        ixir2Check = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "ixir2-fixture";
          installArtifacts = false;
          postBuild = ''
            lake build check-ixir2
            ./.lake/build/bin/check-ixir2 \
              --fixture ./.lake/build/bin/ixir2-fixture \
              --expected ${auditSrc}/fixtures/ixir2/expected.json
          '';
        };

        # Static unique source reversal, canonical mode/policy preimages,
        # checked fallbacks, exact FIP costs, and complete reclamation.
        sourceUniqueReuseCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "source-unique-reuse";
          installArtifacts = false;
          postBuild = ''
            lake build check-source-unique-reuse
            ./.lake/build/bin/check-source-unique-reuse \
              --fixture ./.lake/build/bin/source-unique-reuse \
              --expected ${auditSrc}/fixtures/source-unique-reuse/expected.json
          '';
        };

        # Checked native unique reversal from Ixon, exact source/ABI/object
        # provenance, independent byte and hardware observations, full release.
        sourceNativeUniqueCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs =
            leanBuildInputs
            ++ [pkgs.binutils]
            ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc];
          name = "source-native-unique";
          installArtifacts = false;
          postBuild = ''
            lake build check-source-native-unique
            ./.lake/build/bin/check-source-native-unique \
              --fixture ./.lake/build/bin/source-native-unique \
              --expected ${auditSrc}/fixtures/source-native-unique/expected.json \
              --readelf ${pkgs.binutils}/bin/readelf \
              --objdump ${pkgs.binutils}/bin/objdump \
              ${pkgs.lib.optionalString (system == "x86_64-linux")
                "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-unique/native_harness.c"}
          '';
        };

        # One compiled source function and one ELF pair, independently checked
        # against runtime arguments, malformed inputs, and full reclamation.
        sourceNativeRuntimeCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs =
            leanBuildInputs
            ++ [pkgs.binutils]
            ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc];
          name = "source-native-runtime";
          installArtifacts = false;
          postBuild = ''
            lake build check-source-native-runtime
            ./.lake/build/bin/check-source-native-runtime \
              --fixture ./.lake/build/bin/source-native-runtime \
              --expected ${auditSrc}/fixtures/source-native-runtime/expected.json \
              --readelf ${pkgs.binutils}/bin/readelf \
              --objdump ${pkgs.binutils}/bin/objdump \
              ${pkgs.lib.optionalString (system == "x86_64-linux")
                "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-runtime/native_harness.c"}
            ./.lake/build/bin/check-source-native-runtime \
              --fixture ./.lake/build/bin/source-native-runtime \
              --variant counter-fold \
              --expected ${auditSrc}/fixtures/source-native-runtime/expected-counter-fold.json \
              --readelf ${pkgs.binutils}/bin/readelf \
              --objdump ${pkgs.binutils}/bin/objdump \
              ${pkgs.lib.optionalString (system == "x86_64-linux")
                "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-runtime/native_harness.c"}
          '';
        };

        sourceNativeAllocatingCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs =
            leanBuildInputs
            ++ [pkgs.binutils]
            ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc];
          name = "source-native-allocating";
          installArtifacts = false;
          postBuild = ''
            lake build check-source-native-allocating
            ./.lake/build/bin/check-source-native-allocating \
              --fixture ./.lake/build/bin/source-native-allocating \
              --expected ${auditSrc}/fixtures/source-native-allocating/expected.json \
              --readelf ${pkgs.binutils}/bin/readelf \
              --objdump ${pkgs.binutils}/bin/objdump \
              ${pkgs.lib.optionalString (system == "x86_64-linux")
                "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-allocating/native_harness.c"}
            ./.lake/build/bin/check-source-native-allocating \
              --fixture ./.lake/build/bin/source-native-allocating \
              --variant counter-fold \
              --expected ${auditSrc}/fixtures/source-native-allocating/expected-counter-fold.json \
              --readelf ${pkgs.binutils}/bin/readelf \
              --objdump ${pkgs.binutils}/bin/objdump \
              ${pkgs.lib.optionalString (system == "x86_64-linux")
                "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-allocating/native_harness.c"}
          '';
        };

        sourceNativeUpstreamCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs ++ [pkgs.binutils]
            ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc];
          name = "source-native-upstream";
          installArtifacts = false;
          postBuild = ''
            lake build check-source-native-upstream
            ./.lake/build/bin/check-source-native-upstream \
              --fixture ./.lake/build/bin/source-native-upstream \
              --expected ${auditSrc}/fixtures/source-native-upstream/expected.json \
              --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump \
              ${pkgs.lib.optionalString (system == "x86_64-linux")
                "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-upstream/native_harness.c"}
          '';
        };

        sourceNativeScalarCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs ++ [pkgs.binutils]
            ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc];
          name = "source-native-scalar";
          installArtifacts = false;
          postBuild = ''
            lake build check-source-native-scalar
            ./.lake/build/bin/check-source-native-scalar \
              --fixture ./.lake/build/bin/source-native-scalar \
              --expected ${auditSrc}/fixtures/source-native-scalar/expected.json \
              --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump \
              ${pkgs.lib.optionalString (system == "x86_64-linux")
                "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-scalar/native_harness.c"}
          '';
        };

        sourceNativePhysicalScalarCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs ++ [pkgs.binutils]
            ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc];
          name = "source-native-physical-scalar";
          installArtifacts = false;
          postBuild = ''
            lake build check-source-native-physical-scalar
            ./.lake/build/bin/check-source-native-physical-scalar \
              --fixture ./.lake/build/bin/source-native-physical-scalar \
              --expected ${auditSrc}/fixtures/source-native-physical-scalar/expected.json \
              --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump \
              ${pkgs.lib.optionalString (system == "x86_64-linux")
                "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-physical-scalar/native_harness.c"}
          '';
        };

        sourceNativeHeapCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs ++ [pkgs.binutils]
            ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc];
          name = "source-native-heap";
          installArtifacts = false;
          postBuild = ''
            lake build heap-snapshot-object check-source-native-heap
            ./.lake/build/bin/check-source-native-heap \
              --fixture ./.lake/build/bin/source-native-heap \
              --consumer ./.lake/build/bin/heap-snapshot-object \
              --expected ${auditSrc}/fixtures/source-native-heap/expected.json \
              --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump \
              ${pkgs.lib.optionalString (system == "x86_64-linux")
                "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-heap/native_harness.c"}
            ./.lake/build/bin/check-source-native-heap \
              --fixture ./.lake/build/bin/source-native-heap \
              --consumer ./.lake/build/bin/heap-snapshot-object \
              --expected ${auditSrc}/fixtures/source-native-heap/expected-shared.json \
              --emission shared \
              --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump \
              ${pkgs.lib.optionalString (system == "x86_64-linux")
                "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-heap/native_harness.c"}
            ./.lake/build/bin/check-source-native-heap \
              --fixture ./.lake/build/bin/source-native-heap \
              --consumer ./.lake/build/bin/heap-snapshot-object \
              --expected ${auditSrc}/fixtures/source-native-heap/expected-graph.json \
              --emission graph \
              --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump \
              ${pkgs.lib.optionalString (system == "x86_64-linux")
                "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-heap/native_harness.c"}
          '';
        };

        sourceNativeCapturedScalarCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs ++ [pkgs.binutils]
            ++ pkgs.lib.optionals (system == "x86_64-linux") [pkgs.stdenv.cc];
          name = "source-native-captured-scalar";
          installArtifacts = false;
          postBuild = ''
            lake build check-source-native-captured-scalar
            ./.lake/build/bin/check-source-native-captured-scalar \
              --fixture ./.lake/build/bin/source-native-captured-scalar \
              --expected ${auditSrc}/fixtures/source-native-captured-scalar/expected.json \
              --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump \
              ${pkgs.lib.optionalString (system == "x86_64-linux")
                "--cc ${pkgs.stdenv.cc}/bin/cc --harness ${auditSrc}/fixtures/source-native-captured-scalar/native_harness.c"}
          '';
        };

        nativeSharingCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs ++ [pkgs.gcc pkgs.binutils];
          name = "native-sharing";
          installArtifacts = false;
          postBuild = ''
            lake build heap-snapshot-object check-native-sharing
            ./.lake/build/bin/check-native-sharing \
              --fixture ./.lake/build/bin/native-sharing \
              --consumer ./.lake/build/bin/heap-snapshot-object \
              --expected ${auditSrc}/fixtures/native-sharing/expected.json \
              --cc ${pkgs.gcc}/bin/gcc --harness ${auditSrc}/benchmarks/native/scaling_harness.c \
              --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump
          '';
        };

        nativeGraphCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs ++ [pkgs.gcc pkgs.binutils];
          name = "native-graph";
          installArtifacts = false;
          postBuild = ''
            lake build heap-snapshot-object check-native-graph
            ./.lake/build/bin/check-native-graph \
              --fixture ./.lake/build/bin/native-graph \
              --consumer ./.lake/build/bin/heap-snapshot-object \
              --expected ${auditSrc}/fixtures/native-graph/expected.json \
              --cc ${pkgs.gcc}/bin/gcc --harness ${auditSrc}/benchmarks/native/scaling_harness.c \
              --readelf ${pkgs.binutils}/bin/readelf --objdump ${pkgs.binutils}/bin/objdump
          '';
        };

        # Checked borrowed calls from Ixon, whole caller/callee reconstruction,
        # independent heap execution, RC improvement, and baseline fallbacks.
        sourceBorrowCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "source-borrow";
          installArtifacts = false;
          postBuild = ''
            lake build check-source-borrow
            ./.lake/build/bin/check-source-borrow \
              --fixture ./.lake/build/bin/source-borrow \
              --expected ${auditSrc}/fixtures/source-borrow/expected.json
          '';
        };

        # Runtime arguments are supplied after one structural source selection.
        # Independently check all call bodies, wrappers, and execution prefixes.
        sourceBorrowRuntimeCheck = lake2nix.mkPackage {
          inherit lakeDeps;
          lakeArtifacts = compilatrixLib;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "source-borrow-runtime";
          installArtifacts = false;
          postBuild = ''
            lake build check-source-borrow-runtime
            ./.lake/build/bin/check-source-borrow-runtime \
              --fixture ./.lake/build/bin/source-borrow-runtime \
              --expected ${auditSrc}/fixtures/source-borrow-runtime/expected.json
          '';
        };

        # Lint every workflow file; fail closed if the glob matches none.
        ciWorkflowCheck =
          pkgs.runCommand "ci-workflow-check" {
            nativeBuildInputs = [pkgs.actionlint];
          } ''
            shopt -s nullglob
            workflows=(${auditSrc}/.github/workflows/*.yml ${auditSrc}/.github/workflows/*.yaml)
            [ "''${#workflows[@]}" -gt 0 ]
            actionlint "''${workflows[@]}"
            touch $out
          '';
      in {
        packages = {
          default = compilatrixLib;
          compilatrix = compilatrixLib;
        };

        checks = {
          build = compilatrixLib;
          ci-workflow = ciWorkflowCheck;
          trusted-extern-ledger = trustedExternCheck;
          x86-encoder-decoder = x86EncoderCheck;
          x86-byte-execution = x86BytesCheck;
          x86-stream-objects = x86StreamsCheck;
          x86-elf-object = x86ObjectCheck;
          source-coverage = sourceCoverageCheck;
          source-recursion = sourceRecursionCheck;
          source-call-reuse = sourceCallReuseCheck;
          source-space = sourceSpaceCheck;
          source-modular = sourceModularCheck;
          assembly-scaling = assemblyScalingCheck;
          source-evidence = sourceEvidenceCheck;
          ixby = ixbyCheck;
          ixby-symbolic = ixbySymbolicCheck;
          ixby-stage2 = ixbyStage2Check;
          ixby-lean = ixbyLeanCheck;
          ixir2-identity = ixir2Check;
          source-unique-reuse = sourceUniqueReuseCheck;
          source-native-unique = sourceNativeUniqueCheck;
          source-native-runtime = sourceNativeRuntimeCheck;
          source-native-allocating = sourceNativeAllocatingCheck;
          source-native-upstream = sourceNativeUpstreamCheck;
          source-native-scalar = sourceNativeScalarCheck;
          source-native-physical-scalar = sourceNativePhysicalScalarCheck;
          source-native-heap = sourceNativeHeapCheck;
          source-native-captured-scalar = sourceNativeCapturedScalarCheck;
          source-borrow = sourceBorrowCheck;
          source-borrow-runtime = sourceBorrowRuntimeCheck;
          tests = testsCheck;
          catalog-contact = catalogContactCheck;
        } // pkgs.lib.optionalAttrs (system == "x86_64-linux") {
          native-sharing = nativeSharingCheck;
          native-graph = nativeGraphCheck;
        };

        devShells.default = pkgs.mkShell {
          # Blake3.lean's Rust binding uses bindgen through lean-ffi.
          # Point it at the pinned nixpkgs libclang so `lake exe tests`
          # works in the documented dev loop as well as in flake checks.
          LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";
          packages = [
            lean
            # Blake3.lean's lakefile shells out to `cargo build` for its
            # Rust static lib, so a devshell `lake build` needs a Rust
            # toolchain (the nix build path instead injects the
            # flake-built artifact via depOverrideDeriv).
            pkgs.clang
            pkgs.binutils
            pkgs.cargo
            pkgs.rustc
          ];
        };

        formatter = pkgs.alejandra;
      };
    };
}
