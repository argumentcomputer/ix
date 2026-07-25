{
  description = "Ix Nix flake (Lean4 + C + Rust)";

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

    # Blake3 Rust bindings for Lean
    blake3-lean = {
      url = "github:argumentcomputer/Blake3.lean";
      # System packages, follows lean4-nix so we stay in sync
      inputs.lean4-nix.follows = "lean4-nix";
    };

    # Zisk dev shell (cargo-zisk, ziskemu, RISC-V toolchain) for `zisk-guest`.
    zisk.url = "github:argumentcomputer/zisk.nix/fixups";

    # SP1 dev shell (cargo-prove + succinct Rust toolchain) for `sp1/guest`.
    sp1 = {
      url = "github:argumentcomputer/sp1.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    inputs@{
      nixpkgs,
      flake-parts,
      lean4-nix,
      fenix,
      crane,
      blake3-lean,
      zisk,
      sp1,
      ...
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      # Systems we want to build for
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];

      perSystem =
        {
          system,
          pkgs,
          ...
        }:
        let
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
            pname = "ix";
            version = "0.1.0";
            strictDeps = true;

            # build.rs uses LEAN_SYSROOT to locate lean/lean.h for bindgen
            LEAN_SYSROOT = "${pkgs.lean.lean-all}";
            # bindgen needs libclang to parse C headers
            LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";

            buildInputs =
              [ ]
              ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
                # Additional darwin specific inputs can be set here
                pkgs.libiconv
              ];
          };
          # Build dependencies once with every feature enabled so the `net`
          # stack (tokio/iroh) is compiled and cached here, then shared by the
          # package builds and the all-features clippy check instead of being
          # rebuilt per consumer.
          cargoArtifacts = craneLib.buildDepsOnly (
            craneArgs
            // {
              cargoExtraArgs = "--locked --all-features";
            }
          );

          # Test build: parallel + test-ffi (only used by ixTest).
          # doCheck = false: the `nextest` check is the single place cargo
          # tests run, so package builds only compile.
          rustPkgTest = craneLib.buildPackage (
            craneArgs
            // {
              inherit cargoArtifacts;
              cargoExtraArgs = "--locked --features parallel,test-ffi";
              doCheck = false;
            }
          );

          # Release build without test-ffi (for distribution)
          rustPkgRelease = craneLib.buildPackage (
            craneArgs
            // {
              inherit cargoArtifacts;
              cargoExtraArgs = "--locked --features parallel";
              doCheck = false;
            }
          );

          # Net build for the `ix` CLI (`ix serve` / `ix connect` iroh stack),
          # mirroring the lakefile's `ix_rs_net` target, which skips `net` on
          # macOS.
          rustPkgNet = craneLib.buildPackage (
            craneArgs
            // {
              inherit cargoArtifacts;
              cargoExtraArgs =
                "--locked --features parallel"
                + pkgs.lib.optionalString (!pkgs.stdenv.isDarwin) ",net";
              doCheck = false;
            }
          );

          # Lake package
          lake2nix = pkgs.callPackage lean4-nix.lake { };
          # Restrict the Lake build inputs to Lean-relevant files so edits to
          # unrelated files (flake.nix, CI, docs) don't invalidate the whole
          # Lean build. The Rust side gets the same via cleanCargoSource.
          leanSrc = pkgs.lib.fileset.toSource {
            root = ./.;
            fileset = pkgs.lib.fileset.unions [
              ./lakefile.lean
              ./lake-manifest.json
              ./lean-toolchain
              (pkgs.lib.fileset.fileFilter (f: f.hasExt "lean") ./.)
            ];
          };
          lakeDeps = lake2nix.buildDeps {
            src = leanSrc;
            depOverride = {
              # lean4-nix guesses a dep's library target by capitalizing the
              # package name ("lean4lean" -> "Lean4lean"), but this package's
              # library is `Lean4Lean`. Build the stock default targets
              # (Lean4Lean, the lean4lean exe, Theory, Verify) plus the
              # shared/static facets so consumers linking exes find the
              # module `.o` files in the read-only store path.
              lean4lean = {
                buildPhase = ''
                  runHook preBuild
                  lake build
                  lake build Lean4Lean:shared Lean4Lean:static
                  runHook postBuild
                '';
              };
            };
            depOverrideDeriv = {
              Blake3 = blake3-lean.packages.${system}.rust;
            };
          };
          # Shared Lake build args: patches out the Cargo build (Crane handles it)
          mkLakeBuildArgs = rustLib: {
            inherit lakeDeps;
            src = leanSrc;
            # Don't build the `ix_rs` static lib with Lake, since we build it with Crane
            postPatch = ''
              substituteInPlace lakefile.lean --replace-fail 'proc { cmd := "cargo"' '--proc { cmd := "cargo"'
            '';
            # Symlink the Crane-built static lib to where Lake expects it
            postConfigure = ''
              mkdir -p target/release
              ln -s ${rustLib}/lib/libix_ffi.a target/release/
            '';
            buildInputs = [
              pkgs.gmp
              pkgs.lean.lean-all
              pkgs.rsync
            ];
          };

          # Release build args (no test-ffi symbols)
          lakeBuildArgs = mkLakeBuildArgs rustPkgRelease;
          # CLI build args (net symbols for `ix serve` / `ix connect`)
          lakeNetBuildArgs = mkLakeBuildArgs rustPkgNet;
          # Test build args (includes test-ffi symbols)
          lakeTestBuildArgs = mkLakeBuildArgs rustPkgTest;

          ixLib = lake2nix.mkPackage (
            lakeBuildArgs
            // {
              name = "Ix";
              buildLibrary = true;
            }
          );
          lakeBinArgs = lakeBuildArgs // {
            lakeArtifacts = ixLib;
            # Binaries that import Ix.Meta need .olean files at runtime via LEAN_PATH
            installArtifacts = true;
          };
          leanPath = pkgs.lib.concatStringsSep ":" (
            map (d: "${d}/.lake/build/lib/lean") ([ ixLib ] ++ builtins.attrValues lakeDeps)
          );
          wrapBin =
            drv:
            pkgs.runCommand drv.name { nativeBuildInputs = [ pkgs.makeWrapper ]; } ''
              mkdir -p $out/bin
              for f in ${drv}/bin/*; do
                [ -x "$f" ] || continue
                makeWrapper "$f" "$out/bin/$(basename "$f")" \
                  --set LEAN_SYSROOT "${pkgs.lean.lean-all}" \
                  --set LEAN_PATH "${drv}/.lake/build/lib/lean:${leanPath}"
              done
            '';
          # The CLI links rustPkgNet (lakefile: `ix` uses `ix_rs_net`), reusing
          # ixLib's oleans.
          ixCLI = wrapBin (
            lake2nix.mkPackage (
              lakeNetBuildArgs
              // {
                lakeArtifacts = ixLib;
                installArtifacts = true;
                name = "ix";
              }
            )
          );
          # Test binary links rustPkg (with test-ffi) instead of rustPkgRelease
          ixTest = wrapBin (
            lake2nix.mkPackage (
              lakeTestBuildArgs
              // {
                name = "IxTests";
                installArtifacts = true;
              }
            )
          );
          ZKVotingProver = wrapBin (
            lake2nix.mkPackage (
              lakeBinArgs
              // {
                name = "Apps.ZKVoting.Prover";
                installArtifacts = true;
              }
            )
          );
        in
        {
          # Lean overlay
          _module.args.pkgs = import nixpkgs {
            inherit system;
            overlays = [ (lean4-nix.readToolchainFile ./lean-toolchain) ];
          };

          packages = {
            default = ixLib;
            ix = ixCLI;
            zkv-prover = ZKVotingProver // {
              meta.mainProgram = "Apps-ZKVoting-Prover";
            };
          };

          checks = {
            # Lint the host workspace; warnings are errors.
            clippy = craneLib.cargoClippy (
              craneArgs
              // {
                inherit cargoArtifacts;
                cargoExtraArgs = "--locked --all-features";
                cargoClippyExtraArgs = "--all-targets -- -D warnings";
              }
            );
            # Rust unit tests across the host workspace.
            nextest = craneLib.cargoNextest (
              craneArgs
              // {
                inherit cargoArtifacts;
                cargoExtraArgs = "--locked --workspace";
                cargoNextestExtraArgs = "--profile ci --run-ignored all";
              }
            );
            # Lean test suite. The suite reads fixtures and writes scratch
            # files by paths relative to the working dir, so run it from a
            # writable copy of the source tree, as if from a checkout.
            ix-tests = pkgs.runCommand "ix-tests" { } ''
              cp -r ${./.} src
              chmod -R u+w src
              cd src
              ${ixTest}/bin/IxTests
              touch $out
            '';
          };

          # Lean + Rust shell for host development (`cargo build`, `lake build`).
          devShells.default = pkgs.mkShell {
            LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";
            packages = with pkgs; [
              pkg-config
              openssl
              clang
              rustToolchain
              rust-analyzer
              lean.lean-all
              cargo-deny
              valgrind
              # Python + matplotlib for Benchmarks/Statistics (model & plot bench data)
              (python3.withPackages (ps: with ps; [matplotlib]))
            ];
          };

          # TODO: Re-enable the zkVM shells once they build in CI.
          # Zisk shell for `zisk-guest/` (cargo-zisk, ziskemu, RISC-V toolchain).
          # Kept separate from `default`: merging cross-pollinates NIX_CFLAGS_COMPILE
          # between zisk.nix's and this flake's nixpkgs, which breaks bindgen on
          # `lean.h`.
          # devShells.zisk = zisk.devShells.${system}.default;

          # SP1 shell for `sp1/host` + `sp1/guest`: host Rust toolchain plus
          # cargo-prove and the succinct Rust toolchain (~/.sp1) from sp1.nix.
          # `rustup-shim` wraps the host `rustc` to dispatch to the succinct
          # toolchain when `RUSTUP_TOOLCHAIN=succinct` (set by `sp1-build`); the
          # plain host rustc doesn't know `riscv64im-succinct-zkvm-elf`.
          # `sp1-prover-types`'s build script needs `protoc`.
          # devShells.sp1 = pkgs.mkShell {
          #   name = "sp1";
          #   inputsFrom = [ sp1.devShells.${system}.default ];
          #   LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";
          #   packages = with pkgs; [
          #     pkg-config
          #     openssl
          #     protobuf
          #     clang
          #     (sp1.packages.${system}.rustup-shim.override { inherit rustToolchain; })
          #   ];
          # };

          formatter = pkgs.alejandra;
        };
    };
}
