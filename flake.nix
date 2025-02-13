{
  description = "Ix Nix flake (Lean4 + Rust)";

  inputs = {
    # Lean + System packages
    nixpkgs.url = "github:nixos/nixpkgs/nixos-24.11";
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

        rustPkg = (naersk.lib.${system}
          .override {
            cargo = rustToolchain;
            rustc = rustToolchain;
          })
          .buildPackage {
            src = pkgs.lib.cleanSource ./.;
          };

        overlayedPkgs = import nixpkgs {
          inherit system;
          overlays = [
            (lean4-nix.readToolchainFile ./lean-toolchain)
          ];
        };

        commonPkgs = with pkgs; [
          ocl-icd
          libblake3
          pkg-config
          openssl
          overlayedPkgs.gcc
          overlayedPkgs.clang
          rustToolchain
        ];

        #ffiLib = pkgs.stdenv.mkDerivation {
        #  name = "ffi-lib";
        #  src = ./ffi.c;
        #  buildInputs = [ overlayedPkgs.clang overlayedPkgs.gcc overlayedPkgs.lean.lean-all ];
        #  phases = [ "buildPhase" "installPhase" ];
        #  buildPhase = ''
        #    clang -c $src -o ffi.o
        #    ar rcs libffi.a ffi.o
        #  '';
        #  installPhase = ''
        #    mkdir -p $out/lib
        #    cp libffi.a $out/lib/
        #  '';
        #};
        leanPkg = (lean4-nix.lake { pkgs = overlayedPkgs; }).mkPackage {
            src = ./.;
            roots = ["Main" "Ix"];
        };
      in {
        packages = {
          # `nix build .` or `nix build .#default` => Lean4 exe
          # TODO: This doesn't work
          default = leanPkg.executable;
          rust = rustPkg;
        };

        # Provide a unified dev shell with Lean + Rust
        devShells.default = pkgs.mkShell {
          packages = commonPkgs ++ [
            overlayedPkgs.lean.lean         # Lean compiler
            overlayedPkgs.lean.lean-all     # Includes Lake, stdlib, etc.
            pkgs.rust-analyzer
          ];
        };
        devShells.ci = pkgs.mkShell {
          packages = with pkgs; commonPkgs ++ [
            elan
          ];
        };
      };
    };
}
