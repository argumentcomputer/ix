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
  };

  outputs = inputs @ {
    nixpkgs,
    flake-parts,
    lean4-nix,
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
            (pkgs.lib.fileset.fileFilter (f: f.hasExt "lean") ./Navigatrix)
          ];
        };
        # No Lake requires yet; buildDeps reads the (empty) manifest.
        lakeDeps = lake2nix.buildDeps {
          src = leanSrc;
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
