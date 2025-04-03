{
  description = "Ix Nix flake (Lean4 + C + Rust)";

  inputs = {
    # Lean + System packages
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    lean4-nix = {
      url = "github:argumentcomputer/lean4-nix";
      # Follow top-level nixpkgs so we stay in sync
      inputs.nixpkgs.follows = "nixpkgs";
    };

    # Helper: flake-parts for easier outputs
    flake-parts.url = "github:hercules-ci/flake-parts";

    # Rust-related inputs
    fenix = {
      url = "github:nix-community/fenix";
      # Follow top-level nixpkgs so we stay in sync
      inputs.nixpkgs.follows = "nixpkgs";
    };

    crane.url = "github:ipetkov/crane";

    blake3-lean = {
      url = "github:argumentcomputer/Blake3.lean";
      # Follow top-level nixpkgs so we stay in sync
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = inputs @ { nixpkgs, flake-parts, lean4-nix, fenix, crane, blake3-lean, ... }:
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
        lib = (import ./ix.nix { inherit system pkgs fenix crane lean4-nix blake3-lean; }).lib;
      in {
        # Lean overlay
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [(lean4-nix.readToolchainFile ./lean-toolchain)];
        };

        packages = {
          # Ix CLI
          default = lib.leanPkg.executable;
          # Ix tests
          test = (lean4-nix.lake { inherit pkgs; }).mkPackage {
            src = ./.;
            roots = ["Tests.Main" "Ix"];
            deps = [ lib.leanPkg ];
            staticLibDeps = [ "${lib.rustPkg}/lib" "${lib.cPkg}/lib" "${lib.blake3C}/lib" ];
          };
          # Rust static lib, needed for static linking downstream
          rustStaticLib = lib.rustPkg;
          # C static lib, needed for static linking downstream
          cStaticLib = lib.cPkg;
        };

        # Provide a unified dev shell with Lean + Rust
        devShells.default = pkgs.mkShell {
          LEAN_SYSROOT="${pkgs.lean.lean-all}";
          packages = with pkgs; [
            pkg-config
            openssl
            ocl-icd
            gcc
            clang
            lib.rustToolchain
            rust-analyzer
            lean.lean         # Lean compiler
            lean.lean-all     # Includes Lake, stdlib, etc.
          ];
        };
      };
    };
}
