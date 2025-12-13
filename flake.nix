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
    #lean4-nix.url = "github:lenianiva/lean4-nix?ref=lake/static";
    lean4-nix.url = "github:argumentcomputer/lean4-nix?ref=lake-incremental";
    #lean4-nix.url = "github:lenianiva/lean4-nix?rev=f1e91cf5779d5987c219041daf45eecb00e40b7d";

    # Helper: flake-parts for easier outputs
    flake-parts.url = "github:hercules-ci/flake-parts";

    # Rust-related inputs
    fenix = {
      url = "github:nix-community/fenix";
      # Follow lean4-nix nixpkgs so we stay in sync
      inputs.nixpkgs.follows = "lean4-nix/nixpkgs";
    };

    crane.url = "github:ipetkov/crane";

    blake3 = {
      url = "github:BLAKE3-team/BLAKE3?ref=refs/tags/1.8.2";
      flake = false;
    };

    # Blake3 C bindings for Lean
    blake3-lean = {
      url = "github:argumentcomputer/Blake3.lean?ref=nix-lake";
      #url = "path:/home/sam/repos/argument/Blake3.lean";
      # Follow lean4-nix nixpkgs so we stay in sync
      inputs.nixpkgs.follows = "lean4-nix/nixpkgs";
    };
  };

  outputs = inputs @ {
    nixpkgs,
    flake-parts,
    lean4-nix,
    fenix,
    crane,
    blake3,
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
          sha256 = "sha256-SDu4snEWjuZU475PERvu+iO50Mi39KVjqCeJeNvpguU=";
        };

        # Rust package
        craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;
        src = craneLib.cleanCargoSource ./.;
        craneArgs = {
          inherit src;
          strictDeps = true;

          buildInputs =
            [
              # Add additional build inputs here
            ]
            ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
              # Additional darwin specific inputs can be set here
              pkgs.libiconv
            ];
        };
        craneLibLLvmTools = craneLib.overrideToolchain rustToolchain;
        cargoArtifacts = craneLib.buildDepsOnly craneArgs;

        rustPkg = craneLib.buildPackage (craneArgs
          // {
            inherit cargoArtifacts;
          });

        # Lake package
        lake2nix = pkgs.callPackage lean4-nix.lake {};
        lakeArgs = {
          src = ./.;
          depOverrideDeriv = {
            Blake3 = blake3-lean.packages.${system}.default;
          };
          # Don't build the `ix_rs` static lib with Lake, since we build it with Crane
          postPatch = ''
            substituteInPlace lakefile.lean --replace-fail 'proc { cmd := "cargo"' '--proc { cmd := "cargo"'
          '';
          # Copy the `ix_rs` static lib from Crane to `target/release` so Lake can use it
          postConfigure = ''
            mkdir -p target/release
            ln -s ${rustPkg}/lib/libix_rs.a target/release/
          '';
        };
        lakeDeps = lake2nix.buildDeps {
          src = ./.;
          depOverrideDeriv = {
            Blake3 = blake3-lean.packages.${system}.default;
          };
        };
        ixLib = lake2nix.mkPackage (lakeArgs
          // {
            name = "Ix";
          });
        # Ix CLI
        ixCLI = lake2nix.mkPackage (lakeArgs
          // {
            name = "ix";
            installArtifacts = false;
          });
        ixTest = lake2nix.mkPackage (lakeArgs
          // {
            name = "IxTests";
            installArtifacts = false;
          });
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

          ## Ix benches
          #bench-aiur =
          #  ((lean4-nix.lake {inherit pkgs;}).mkPackage {
          #    src = ./.;
          #    roots = ["Benchmarks.Aiur" "Ix"];
          #    deps = [lib.leanPkg];
          #    staticLibDeps = ["${lib.rustPkg}/lib" "${lib.cPkg}/lib" "${lib.blake3C}/lib"];
          #  }).executable;

          #bench-blake3 =
          #  ((lean4-nix.lake {inherit pkgs;}).mkPackage {
          #    src = ./.;
          #    roots = ["Benchmarks.Blake3" "Ix"];
          #    deps = [lib.leanPkg];
          #    staticLibDeps = ["${lib.rustPkg}/lib" "${lib.cPkg}/lib" "${lib.blake3C}/lib"];
          #  }).executable;

          ## Rust static lib, needed for static linking downstream
          #rustStaticLib = lib.rustPkg;

          ## C static lib, needed for static linking downstream
          #cStaticLib = lib.cPkg;
        };

        # Provide a unified dev shell with Lean + Rust
        devShells.default = pkgs.mkShell {
          packages = with pkgs; [
            pkg-config
            openssl
            ocl-icd
            gcc
            clang
            rustToolchain
            rust-analyzer
            lean.lean-all # Includes Lean compiler, lake, stdlib, etc.
          ];
        };

        formatter = pkgs.alejandra;
      };
    };
}
