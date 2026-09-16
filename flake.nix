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
    blake3WithStaticCrates = assert builtins.readFile (blake3-lean.outPath + "/lean-toolchain")
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
            ./CompilatrixTests.lean
            ./CompilatrixTests
            ./nix
            ./CatalogContact.lean
            ./X86ObjectFixture.lean
            ./SourceCoverage.lean
            ./SourceIxby.lean
            ./SourceIxbySymbolic.lean
            ./SourceIxbyStage2.lean
            ./IxonToIxby.lean
            ./vendor/ixby
            ./vendor/aiur
            ./vendor/stage2
            ./fixtures/aiur-bytecode
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
            ./docs/aiur-wire.md
            ./docs/aiur-semantics.md
            ./docs/aiur-static.md
            ./docs/aiur-counter-analysis.md
            ./docs/x86-reference-model.json
            (pkgs.lib.fileset.fileFilter (f: f.hasExt "lean") ./scripts)
            ./scripts/inspect_ixby.py
            ./.github/workflows
          ];
        };
        build = import ./nix/build.nix {
          inherit pkgs lean lake2nix auditSrc;
          root = ./.;
          blake3 = blake3WithStaticCrates.packages.${system}.rust;
        };
        inherit (build) compilatrixLib ciPrograms proofsCheck runtimeSupport mkCheck;
        gateChecks = import ./nix/checks.nix {
          inherit pkgs system auditSrc blake3-lean mkCheck;
        };
        buildGraphCheck = mkCheck "build-graph" [] ''
          ./.lake/build/bin/check-build-graph --root ${auditSrc}
        '';
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
        requiredChecks = with gateChecks;
          {
            proofs = proofsCheck;
            build-graph = buildGraphCheck;
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
            aiur = aiurCheck;
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
          }
          // gateChecks.ixbyStage2BinaryChecks
          // pkgs.lib.optionalAttrs (system == "x86_64-linux") {
            native-sharing = nativeSharingCheck;
            native-graph = nativeGraphCheck;
          };

        ciGroups = import ./nix/groups.nix {
          inherit pkgs system;
          checks = requiredChecks;
        };
      in {
        packages =
          {
            default = compilatrixLib;
            compilatrix = compilatrixLib;
            ci-programs = ciPrograms;
            ci-runtime = ciPrograms.runtime;
            ci-runtime-support = runtimeSupport;
            proofs = proofsCheck;
          }
          // ciGroups;

        checks = requiredChecks;
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
