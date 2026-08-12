{
  description = "Navigatr.ix: a certified Lean 4 toolchain for Ix";

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
    # lakefile.toml/lake-manifest.json. Nested inputs (crane, fenix,
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
            ./lakefile.toml
            ./lake-manifest.json
            ./lean-toolchain
            ./Navigatrix.lean
            ./Tests.lean
            (pkgs.lib.fileset.fileFilter (f: f.hasExt "lean") ./Navigatrix)
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
        navigatrixLib = lake2nix.mkPackage {
          inherit lakeDeps;
          src = leanSrc;
          buildInputs = leanBuildInputs;
          name = "Navigatrix";
          buildLibrary = true;
          meta = {
            description = "Navigatrix library artifact (oleans, exports, static/shared)";
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
      in {
        _module.args.pkgs = import nixpkgs {
          inherit system;
        };

        packages = {
          default = navigatrixLib;
          navigatrix = navigatrixLib;
        };

        checks = {
          build = navigatrixLib;
          tests = testsCheck;
        };

        devShells.default = pkgs.mkShell {
          packages = [
            lean
          ];
        };

        formatter = pkgs.alejandra;
      };
    };
}
