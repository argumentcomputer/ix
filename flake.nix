{
  description = "Ix Nix flake (Lean4 + Rust)";

  inputs = {
    # Lean + System packages
    nixpkgs.url = "github:nixos/nixpkgs/nixos-24.05";
    lean4-nix.url = "github:lenianiva/lean4-nix?ref=manifests/v4.16.0";

    # Helper: flake-parts for easier outputs
    flake-parts.url = "github:hercules-ci/flake-parts";

    # Rust-related inputs
    fenix = {
      url = "github:nix-community/fenix";
      # Follow top-level nixpkgs so we stay in sync
      inputs.nixpkgs.follows = "nixpkgs";
    };
    naersk = {
      url = "github:nix-community/naersk";
      # Follow top-level nixpkgs so we stay in sync
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = inputs @ { nixpkgs, flake-parts, lean4-nix, fenix, naersk, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      # Systems we want to build for
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];

      perSystem = { system, pkgs, ... }:
      let
        rustToolchain = fenix.packages.${system}.fromToolchainFile {
          file = ./rust-toolchain.toml;
          sha256 = "sha256-hpWM7NzUvjHg0xtIgm7ftjKCc1qcAeev45XqD3KMeQo=";
        };

        rustPkg = naersk.lib.${system}
          .override {
            cargo = rustToolchain;
            rustc = rustToolchain;
          }
          .buildPackage {
            src = pkgs.lib.cleanSource ./.;
          };

      in {
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [(lean4-nix.readToolchainFile ./lean-toolchain)];
        };

        packages = {
          # `nix build .` or `nix build .#default` => Lean4 exe
          default = ((lean4-nix.lake {inherit pkgs;}).mkPackage {
            src = ./.;
            roots = ["Main" "Ix"];
          }).executable;

          # `nix build .#rust` => Rust staticlib
          rust = rustPkg;
        };

        # Provide a unified dev shell with Lean + Rust
        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.lean.lean         # Lean compiler
            pkgs.lean.lean-all     # Includes Lake, stdlib, etc.

            pkgs.pkg-config
            pkgs.openssl
            pkgs.gcc
            pkgs.ocl-icd
            pkgs.clang

            rustToolchain
            pkgs.rust-analyzer
          ];
        };
      };
    };
}
