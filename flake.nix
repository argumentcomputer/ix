{
  description = "Ix Nix flake (Lean4 + C + Rust)";

  nixConfig = {
    extra-substituters = [
      "https://cache.garnix.io"
    ];
    extra-trusted-public-keys = [
      "cache.garnix.io:CTFPyKSLcx5RMJKfLo5EEPUObbA78b0YQ2DTCJXqr9g="
    ];
  };

  inputs = {
    # System packages, follows lean4-nix so we stay in sync
    nixpkgs.follows = "lean4-nix/nixpkgs";

    # Lean 4 & Lake
    lean4-nix.url = "github:lenianiva/lean4-nix";

    # Helper: flake-parts for easier outputs
    flake-parts.url = "github:hercules-ci/flake-parts";

    # Rust-related inputs
    fenix = {
      url = "github:nix-community/fenix";
      # Follow lean4-nix nixpkgs so we stay in sync
      inputs.nixpkgs.follows = "lean4-nix/nixpkgs";
    };

    crane.url = "github:ipetkov/crane";

    # Blake3 C bindings for Lean
    blake3-lean = {
      url = "github:argumentcomputer/Blake3.lean";
      # System packages, follows lean4-nix so we stay in sync
      inputs.lean4-nix.follows = "lean4-nix";
    };
  };

  outputs = inputs @ {
    nixpkgs,
    flake-parts,
    lean4-nix,
    fenix,
    crane,
    blake3-lean,
    ...
  }:
    flake-parts.lib.mkFlake {inherit inputs;} {
      # Systems we want to build for
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
        # Pins the Rust toolchain
        rustToolchain = fenix.packages.${system}.fromToolchainFile {
          file = ./rust-toolchain.toml;
          sha256 = "sha256-sqSWJDUxc+zaz1nBWMAJKTAGBuGWP25GCftIOlCEAtA=";
        };

        # Rust package
        craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;
        src = craneLib.cleanCargoSource ./.;
        craneArgs = {
          inherit src;
          strictDeps = true;

          buildInputs =
            []
            ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
              # Additional darwin specific inputs can be set here
              pkgs.libiconv
            ];
        };
        cargoArtifacts = craneLib.buildDepsOnly craneArgs;

        rustPkg = craneLib.buildPackage (craneArgs
          // {
            inherit cargoArtifacts;
          });

        # Lake package
        lake2nix = pkgs.callPackage lean4-nix.lake {};
        lakeDeps = lake2nix.buildDeps {
          src = ./.;
          depOverrideDeriv = {
            Blake3 = blake3-lean.packages.${system}.default;
          };
        };
        lakeBuildArgs = {
          inherit lakeDeps;
          src = ./.;
          # Don't build the `ix_rs` static lib with Lake, since we build it with Crane
          postPatch = ''
            substituteInPlace lakefile.lean --replace-fail "let args := match (ixNoPar, ixNet)" "let _args := match (ixNoPar, ixNet)"
            substituteInPlace lakefile.lean --replace-fail 'proc { cmd := "cargo"' '--proc { cmd := "cargo"'
          '';
          # Copy the `ix_rs` static lib from Crane to `target/release` so Lake can use it
          postConfigure = ''
            mkdir -p target/release
            ln -s ${rustPkg}/lib/libix_rs.a target/release/
          '';
          buildInputs = [pkgs.gmp pkgs.lean.lean-all pkgs.rsync];
        };
        ixLib = lake2nix.mkPackage (lakeBuildArgs
          // {
            name = "Ix";
            buildLibrary = true;
          });
        lakeBinArgs =
          lakeBuildArgs
          // {
            lakeArtifacts = ixLib;
            installArtifacts = false;
          };
        ixCLI = lake2nix.mkPackage (lakeBinArgs // {name = "ix";});
        ixTest = lake2nix.mkPackage (lakeBinArgs // {name = "IxTests";});
        testAiur = lake2nix.mkPackage (lakeBinArgs // {name = "test-aiur";});
        testIxVM = lake2nix.mkPackage (lakeBinArgs // {name = "test-ixvm";});
        benchAiur = lake2nix.mkPackage (lakeBinArgs // {name = "bench-aiur";});
        benchBlake3 = lake2nix.mkPackage (lakeBinArgs // {name = "bench-blake3";});
        benchShardMap = lake2nix.mkPackage (lakeBinArgs // {name = "bench-shardmap";});
      in {
        # Lean overlay
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [(lean4-nix.readToolchainFile ./lean-toolchain)];
        };

        packages = {
          default = ixLib;
          ix = ixCLI;
          test = ixTest;
          test-aiur = testAiur;
          test-ixvm = testIxVM;
          # Ix benches
          bench-aiur = benchAiur;
          bench-blake3 = benchBlake3;
          bench-shardmap = benchShardMap;
        };

        # Provide a unified dev shell with Lean + Rust
        devShells.default = pkgs.mkShell {
          packages = with pkgs; [
            pkg-config
            openssl
            clang
            rustToolchain
            rust-analyzer
            lean.lean-all # Includes Lean compiler, lake, stdlib, etc.
            gmp
          ];
        };

        formatter = pkgs.alejandra;
      };
    };
}
