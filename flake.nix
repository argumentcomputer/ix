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
            ./fixtures/ixon-std-contact
            (pkgs.lib.fileset.fileFilter (f: f.hasExt "lean") ./Compilatrix)
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
            ./fixtures/ixon-std-contact
            (pkgs.lib.fileset.fileFilter (f: f.hasExt "lean") ./Compilatrix)
            ./docs/trusted-externs.json
            ./scripts/check_trusted_externs.py
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
        trustedExternCheck =
          pkgs.runCommand "trusted-extern-ledger-check" {
            nativeBuildInputs = [pkgs.python3];
          } ''
            python3 ${auditSrc}/scripts/check_trusted_externs.py \
              --root ${auditSrc} \
              --dependency-root Blake3=${blake3-lean.outPath} \
              --gmp-version ${pkgs.gmp.version}
            touch $out
          '';

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
            pkgs.cargo
            pkgs.python3
            pkgs.rustc
          ];
        };

        formatter = pkgs.alejandra;
      };
    };
}
