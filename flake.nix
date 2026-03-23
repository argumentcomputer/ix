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

          # build.rs uses LEAN_SYSROOT to locate lean/lean.h for bindgen
          LEAN_SYSROOT = "${pkgs.lean.lean-all}";
          # bindgen needs libclang to parse C headers
          LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";

          buildInputs =
            []
            ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
              # Additional darwin specific inputs can be set here
              pkgs.libiconv
            ];
        };
        cargoArtifacts = craneLib.buildDepsOnly craneArgs;

        # Test build: parallel + test-ffi (only used by ixTest)
        rustPkg = craneLib.buildPackage (craneArgs
          // {
            inherit cargoArtifacts;
            cargoExtraArgs = "--locked --features parallel,test-ffi";
          });

        # Release build without test-ffi (for distribution)
        rustPkgRelease = craneLib.buildPackage (craneArgs
          // {
            inherit cargoArtifacts;
            cargoExtraArgs = "--locked --features parallel";
          });

        # Lake package
        lake2nix = pkgs.callPackage lean4-nix.lake {};
        lakeDeps = lake2nix.buildDeps {
          src = ./.;
          depOverrideDeriv = {
            Blake3 = blake3-lean.packages.${system}.default;
          };
        };
        # Shared Lake build args: patches out the Cargo build (Crane handles it)
        mkLakeBuildArgs = rustLib: {
          inherit lakeDeps;
          src = ./.;
          # Don't build the `ix_rs` static lib with Lake, since we build it with Crane
          postPatch = ''
            substituteInPlace lakefile.lean --replace-fail 'proc { cmd := "cargo"' '--proc { cmd := "cargo"'
          '';
          # Symlink the Crane-built static lib to where Lake expects it
          postConfigure = ''
            mkdir -p target/release
            ln -s ${rustLib}/lib/libix_rs.a target/release/
          '';
          buildInputs = [pkgs.gmp pkgs.lean.lean-all pkgs.rsync];
        };

        # Release build args (no test-ffi symbols)
        lakeBuildArgs = mkLakeBuildArgs rustPkgRelease;
        # Test build args (includes test-ffi symbols)
        lakeTestBuildArgs = mkLakeBuildArgs rustPkg;

        ixLib = lake2nix.mkPackage (lakeBuildArgs
          // {
            name = "Ix";
            buildLibrary = true;
          });
        lakeBinArgs =
          lakeBuildArgs
          // {
            lakeArtifacts = ixLib;
            # Binaries that import Ix.Meta need .olean files at runtime via LEAN_PATH
            installArtifacts = true;
          };
        leanPath = pkgs.lib.concatStringsSep ":" (
          map (d: "${d}/.lake/build/lib/lean") ([ixLib] ++ builtins.attrValues lakeDeps)
        );
        wrapBin = drv:
          pkgs.runCommand drv.name {nativeBuildInputs = [pkgs.makeWrapper];} ''
            mkdir -p $out/bin
            for f in ${drv}/bin/*; do
              [ -x "$f" ] || continue
              makeWrapper "$f" "$out/bin/$(basename "$f")" \
                --set LEAN_SYSROOT "${pkgs.lean.lean-all}" \
                --set LEAN_PATH "${drv}/.lake/build/lib/lean:${leanPath}"
            done
          '';
        ixCLI = wrapBin (lake2nix.mkPackage (lakeBinArgs // {name = "ix";}));
        # Test binary links rustPkg (with test-ffi) instead of rustPkgRelease
        ixTest = wrapBin (lake2nix.mkPackage (lakeTestBuildArgs
          // {
            name = "IxTests";
            installArtifacts = true;
          }));
        ZKVotingProver = wrapBin (lake2nix.mkPackage (lakeBinArgs
          // {
            name = "Apps.ZKVoting.Prover";
            installArtifacts = true;
          }));
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
          zkv-prover = ZKVotingProver // {meta.mainProgram = "Apps-ZKVoting-Prover";};
        };

        # Provide a unified dev shell with Lean + Rust
        devShells.default = pkgs.mkShell {
          # Add libclang for FFI with rust-bindgen
          LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";
          packages = with pkgs; [
            pkg-config
            openssl
            clang
            rustToolchain
            rust-analyzer
            lean.lean-all # Includes Lean compiler, lake, stdlib, etc.
            cargo-deny
            valgrind
          ];
        };

        formatter = pkgs.alejandra;
      };
    };
}
