{
  description = "Ix Nix flake (Lean4 + C + Rust)";

  inputs = {
    # Lean + System packages
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    lean4-nix.url = "github:argumentcomputer/lean4-nix";

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
      # TODO: Update once https://github.com/argumentcomputer/Blake3.lean/pull/11 merges
      url = "github:argumentcomputer/Blake3.lean?rev=f3f5140fdd97776ec885e81e0b0a8f2f13a820a8";
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
      
      flake = {
        lib = import ./ix.nix;
        inputs.fenix = fenix;
        inputs.crane = crane;
        inputs.blake3-lean = blake3-lean;
      };

      perSystem = { system, pkgs, ... }:
      let
        lib = (import ./ix.nix { inherit system pkgs fenix crane lean4-nix blake3-lean; }).lib;

        devShellPkgs = with pkgs; [
          pkg-config
          openssl
          ocl-icd
          gcc
          clang
          lib.rustToolchain
        ];
      in {
        # Lean overlay
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [(lean4-nix.readToolchainFile ./lean-toolchain)];
        };

        packages = {
          default = lib.leanPkg.executable;
          test = lib.leanTest.executable;
        };

        # Provide a unified dev shell with Lean + Rust
        devShells.default = pkgs.mkShell {
          packages = with pkgs; devShellPkgs ++ [
            lean.lean         # Lean compiler
            lean.lean-all     # Includes Lake, stdlib, etc.
            pkgs.rust-analyzer
          ];
        };
        devShells.ci = pkgs.mkShell {
          packages = with pkgs; devShellPkgs ++ [
            elan
          ];
        };
      };
    };
}
