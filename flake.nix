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

    # Blake3 C dependency for static linking
    blake3-lean = {
      url = "github:argumentcomputer/Blake3.lean";
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
        lib = (import ./ix.nix {inherit system pkgs fenix crane lean4-nix blake3-lean;}).lib;
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
          test =
            ((lean4-nix.lake {inherit pkgs;}).mkPackage {
              src = ./.;
              roots = ["Tests.Main" "Ix"];
              deps = [lib.leanPkg];
              staticLibDeps = ["${lib.rustPkg}/lib" "${lib.cPkg}/lib" "${lib.blake3C}/lib"];
            }).executable;

          # Ix benches
          bench-aiur =
            ((lean4-nix.lake {inherit pkgs;}).mkPackage {
              src = ./.;
              roots = ["Benchmarks.Aiur" "Ix"];
              deps = [lib.leanPkg];
              staticLibDeps = ["${lib.rustPkg}/lib" "${lib.cPkg}/lib" "${lib.blake3C}/lib"];
            }).executable;

          bench-blake3 =
            ((lean4-nix.lake {inherit pkgs;}).mkPackage {
              src = ./.;
              roots = ["Benchmarks.Blake3" "Ix"];
              deps = [lib.leanPkg];
              staticLibDeps = ["${lib.rustPkg}/lib" "${lib.cPkg}/lib" "${lib.blake3C}/lib"];
            }).executable;

          # Rust static lib, needed for static linking downstream
          rustStaticLib = lib.rustPkg;

          # C static lib, needed for static linking downstream
          cStaticLib = lib.cPkg;
        };

        # Provide a unified dev shell with Lean + Rust
        devShells.default = pkgs.mkShell {
          packages = with pkgs; [
            pkg-config
            openssl
            ocl-icd
            gcc
            clang
            lib.rustToolchain
            rust-analyzer
            lean.lean-all # Includes Lean compiler, lake, stdlib, etc.
          ];
        };

        formatter = pkgs.alejandra;
      };
    };
}
