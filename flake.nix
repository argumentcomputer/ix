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

    crane = {
      url = "github:ipetkov/crane";
      # Follow top-level nixpkgs so we stay in sync
      inputs.nixpkgs.follows = "nixpkgs";
    };

    blake3-lean = {
      # TODO: Update once https://github.com/argumentcomputer/Blake3.lean/pull/11 merges
      url = "github:argumentcomputer/Blake3.lean?rev=29018d578b043f6638907f3425af839eec345361";
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
        rustToolchain = fenix.packages.${system}.fromToolchainFile {
          file = ./rust-toolchain.toml;
          sha256 = "sha256-hpWM7NzUvjHg0xtIgm7ftjKCc1qcAeev45XqD3KMeQo=";
        };

        # Rust package
        craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;
        src = craneLib.cleanCargoSource ./.;
        commonArgs = {
          inherit src;
          strictDeps = true;

          buildInputs = [
            # Add additional build inputs here
          ] ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
            # Additional darwin specific inputs can be set here
            pkgs.libiconv
          ];
        };
        craneLibLLvmTools = craneLib.overrideToolchain rustToolchain;
        cargoArtifacts = craneLib.buildDepsOnly commonArgs;

        rustPkg = craneLib.buildPackage (commonArgs // {
          inherit cargoArtifacts;
        });

        # C Package
        cPkg = pkgs.stdenv.mkDerivation {
          pname = "ix_c";
          version = "0.1.0";
          src = ./c;
          buildInputs = [ pkgs.gcc pkgs.lean.lean-all rustPkg ];
          # Build the C file
          buildPhase = ''
            gcc -Wall -Werror -Wextra -c binius.c -o binius.o
            gcc -Wall -Werror -Wextra -c u128.c -o u128.o
            ar rcs libix_c.a binius.o u128.o
          '';
          # Install the library
          installPhase = ''
            mkdir -p $out/lib $out/include
            cp libix_c.a $out/lib/
            cp rust.h linear.h common.h $out/include/
          '';
        };

        # Blake3.lean C FFI dependency
        blake3 = blake3-lean.inputs.blake3;
        blake3Mod = (blake3-lean.lib { inherit pkgs lean4-nix blake3; }).lib;
        blake3Lib = blake3Mod.blake3-lib;
        blake3C = blake3Mod.blake3-c;

        # Lean package
        # Fetches external dependencies
        leanPkg = (lean4-nix.lake { inherit pkgs; }).mkPackage {
            src = ./.;
            roots = ["Ix" "Main"];
        };
        # Builds FFI static libraries
        leanPkg' = (pkgs.lean.buildLeanPackage {
          name = "ix";
          src = ./.;
          deps = [ leanPkg ];
          roots = ["Ix" "Main"];
          linkFlags = [ "-L${rustPkg}/lib" "-lix_rs" "-L${cPkg}/lib" "-lix_c" "-L${blake3C}/lib" "-lblake3"];
          groupStaticLibs = true;
        });
        leanTest = (pkgs.lean.buildLeanPackage {
          name = "ix_test";
          src = ./.;
          deps = [ leanPkg' ];
          roots = ["Tests.Main" "Ix"];
          linkFlags = [ "-L${rustPkg}/lib" "-lix_rs" "-L${cPkg}/lib" "-lix_c" "-L${blake3C}/lib" "-lblake3"];
          groupStaticLibs = true;
        });

        devShellPkgs = with pkgs; [
          pkg-config
          openssl
          ocl-icd
          gcc
          clang
          rustToolchain
        ];
      in {
        # Lean overlay
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [(lean4-nix.readToolchainFile ./lean-toolchain)];
        };

        packages = {
          rust = rustPkg;
          c = cPkg;
          default = leanPkg'.executable;
          test = leanTest.executable;
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
