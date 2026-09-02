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
    # NB: no lean4-nix follows — blake3-lean uses the lenianiva
    # lean4-nix API (readToolchainFile), incompatible with our
    # argumentcomputer fork; its lean4-nix is pinned at lock time to
    # ix's rev instead.
    blake3-lean.url = "github:argumentcomputer/Blake3.lean/aaf530784082a2c00b0a93648741429d274102ca";
  };

  outputs = inputs @ {
    nixpkgs,
    flake-parts,
    lean4-nix,
    blake3-lean,
    ...
  }:
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
        # Pinned Lean toolchain, resolved from ./lean-toolchain
        # (matches lean4lean's pin, ahead of ix's — see plans/).
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
            ./SourceRecursion.lean
            ./SourceCallReuse.lean
            ./SourceUniqueReuse.lean
            ./fixtures/ixon-std-contact
            ./fixtures/source-coverage
            ./fixtures/source-recursion
            ./fixtures/source-call-reuse
            ./fixtures/source-unique-reuse
            (pkgs.lib.fileset.fileFilter (f: f.hasExt "lean") ./Compilatrix)
            (pkgs.lib.fileset.fileFilter (f: f.hasExt "lean") ./scripts)
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
            ./SourceRecursion.lean
            ./SourceCallReuse.lean
            ./SourceUniqueReuse.lean
            ./fixtures/ixon-std-contact
            ./fixtures/source-coverage
            ./fixtures/source-recursion
            ./fixtures/source-call-reuse
            ./fixtures/source-unique-reuse
            ./fixtures/x86/native_harness.c
            (pkgs.lib.fileset.fileFilter (f: f.hasExt "lean") ./Compilatrix)
            ./docs/trusted-externs.json
            (pkgs.lib.fileset.fileFilter (f: f.hasExt "lean") ./scripts)
            ./.github/workflows
          ];
        };
        lakeDeps = lake2nix.buildDeps {
          src = leanSrc;
          depOverrideDeriv = {
            Blake3 = blake3-lean.packages.${system}.rust;
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

        # E0 keeps encoding outside the proof cone, so independently decode
        # every Lean-pinned golden byte sequence with the pinned GNU decoder.
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
        _module.args.pkgs = import nixpkgs {
          inherit system;
          };

        packages = {
          default = compilatrixLib;
          compilatrix = compilatrixLib;
        };

        checks = {
          build = compilatrixLib;
          ci-workflow = ciWorkflowCheck;
          trusted-extern-ledger = trustedExternCheck;
          x86-encoder-decoder = x86EncoderCheck;
          x86-elf-object = x86ObjectCheck;
          source-coverage = sourceCoverageCheck;
          source-recursion = sourceRecursionCheck;
          source-call-reuse = sourceCallReuseCheck;
          source-unique-reuse = sourceUniqueReuseCheck;
          tests = testsCheck;
          catalog-contact = catalogContactCheck;
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
