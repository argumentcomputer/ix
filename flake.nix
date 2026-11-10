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
    lean4-nix.url = "github:argumentcomputer/lean4-nix";

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
      url = "github:argumentcomputer/Blake3.lean/3f8b805614a0bae1c033469ff893a8f0ee85f601";
      # System packages, follows lean4-nix so we stay in sync
      inputs.lean4-nix.follows = "lean4-nix";
    };

  };

  outputs =
    inputs@{
      flake-parts,
      lean4-nix,
      fenix,
      crane,
      blake3-lean,
      ...
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      # Linux only: macOS is not supported. The `isDarwin` conditionals below
      # are kept for when it is added back.
      systems = [
        "aarch64-linux"
        "x86_64-linux"
      ];

      perSystem =
        {
          system,
          pkgs,
          ...
        }:
        let
          # Pins the Lean toolchain; a plain derivation, no overlay involved
          lean = lean4-nix.lib.${system}.fromToolchainFile ./lean-toolchain;

          # Pins the Rust toolchain
          rustToolchain = fenix.packages.${system}.fromToolchainFile {
            file = ./rust-toolchain.toml;
            sha256 = "sha256-p8h3Sl/YRByZfZTAKXdsvF6xEenXKrXSVvpphmZENH4=";
          };

          # Rust package
          craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;
          # The Cargo files the workspace builds from.
          cargoSource = pkgs.lib.fileset.fromSource (craneLib.cleanCargoSource ./.);
          # Profiles are embedded in the verifier; compression tests also read
          # binary fixtures that Cargo's source filter does not retain.
          compressionData = pkgs.lib.fileset.unions [
            ./crates/proof-compression/tests/fixtures
            ./crates/proof-compression/verifying-keys
          ];
          # Rust format, host-admission and kernel-boundary tests include
          # immutable fixtures that cleanCargoSource does not retain by extension.
          src = pkgs.lib.fileset.toSource {
            root = ./.;
            fileset = pkgs.lib.fileset.unions [
              cargoSource
              compressionData
              ./Tests/Fixtures/ixon-v4
              ./Tests/Fixtures/host-admission-v1
              ./Tests/Fixtures/role-binding-v2
              ./crates/ixon/tests/fixtures
            ];
          };
          # bindgen's libclang, shared by the Rust package build and the dev
          # shell so the package build also verifies the shell's setting.
          libclangPath = "${pkgs.llvmPackages.libclang.lib}/lib";
          # Rust code generation for the sandboxed builds. Nix builds are a
          # portable compatibility check, never a performance build: native
          # builds go through cargo and Lake in the dev shell, where
          # `.cargo/config.toml` selects `-Ctarget-cpu=native`.
          #
          # crane keeps that config file in the source, so the sandboxed build
          # overrides it with one fixed baseline. x86-64-v3 (AVX2) runs on any
          # x86-64 machine from the last decade; x86-64-v4 would need AVX-512,
          # which most current Intel client CPUs lack. Every machine builds the
          # same store path, so local builds can substitute CI's from Cachix.
          craneArgs =
            pkgs.lib.optionalAttrs pkgs.stdenv.hostPlatform.isx86_64 {
              # Environment form of the `build.rustflags` key the config file sets
              CARGO_BUILD_RUSTFLAGS = "-Ctarget-cpu=x86-64-v3";
            }
            // {
              inherit src;
              pname = "ix";
              version = "0.1.0";
              strictDeps = true;

              # build.rs uses LEAN_SYSROOT to locate lean/lean.h for bindgen
              LEAN_SYSROOT = "${lean}";
              # bindgen needs libclang to parse C headers
              LIBCLANG_PATH = libclangPath;
              # Same C standard the lakefile gives Cargo: Lean's bundled
              # link-time glibc predates the C23 `__isoc23_*` redirects.
              CFLAGS = "-std=gnu17";

              buildInputs =
                [ ]
                ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
                  # Additional darwin specific inputs can be set here
                  pkgs.libiconv
                ];
            };
          # Build dependencies once with every host feature enabled so the
          # `net` stack (tokio/iroh) is compiled and cached here, then shared
          # by the package builds. CUDA remains opt-in and is compiled
          # separately in CI with the CUDA toolkit available.
          cargoArtifacts = craneLib.buildDepsOnly (
            craneArgs
            // {
              cargoExtraArgs = "--locked -p ix-ffi --features parallel,net";
            }
          );

          # The archive the `ix` CLI links: the lakefile's `ix_rs_net` target,
          # with the iroh stack for `ix serve` / `ix connect`, which it skips
          # on macOS. The library build links nothing, so it uses the same one.
          # doCheck = false: package builds only compile. Clippy and the
          # cargo tests run in CI Jobs' rust-test job, not in the flake.
          rustPkg = craneLib.buildPackage (
            craneArgs
            // {
              inherit cargoArtifacts;
              cargoExtraArgs =
                "--locked -p ix-ffi --features parallel" + pkgs.lib.optionalString (!pkgs.stdenv.isDarwin) ",net";
              doCheck = false;
            }
          );

          # Lake package
          lake2nix = pkgs.callPackage lean4-nix.lake { inherit lean; };
          # Restrict the Lake build inputs to the files Lake reads. Crane builds
          # the Rust archive, and Lake's archive targets only hash the prebuilt
          # file, so no Rust sources are needed here.
          leanSrc = pkgs.lib.fileset.toSource {
            root = ./.;
            fileset = pkgs.lib.fileset.unions [
              # What `lake build` reads: Lean sources, manifests, FFI shims.
              (pkgs.lib.fileset.fromSource (lake2nix.cleanLakeSource ./.))
              ./IxC/lake-manifest.json
              ./IxC/lean-toolchain
              # The pinned verifying keys `FormalAiurKeys` embeds.
              ./tools/formal-aiur.keys
            ];
          };
          lakeManifest = builtins.fromJSON (builtins.readFile ./lake-manifest.json);
          # Local packages build in the workspace; buildDeps only supports Git sources.
          lakeDeps = builtins.removeAttrs (lake2nix.buildDeps {
            src = leanSrc;
            # Formal Aiur's proofs require mathlib, which brings these packages
            # into the workspace. Nothing the flake builds (the Ix library and
            # its executables) imports them, so Lake needs only their
            # sources to resolve the workspace. Building them would compile all
            # of Mathlib and its shared library, and lean4-nix's library target
            # guess (`Proofwidgets`) does not exist.
            depOverride =
              pkgs.lib.genAttrs
                [
                  "mathlib"
                  "proofwidgets"
                  "LeanSearchClient"
                  "importGraph"
                  "aesop"
                  "Qq"
                ]
                (_: {
                  buildPhase = ''
                    runHook preBuild
                    runHook postBuild
                  '';
                });
            depOverrideDeriv = {
              # Blake3.lean's `rust` package builds only its `Blake3Rust`
              # library (`Blake3.Rust` and the `Blake3` root). Ix also imports
              # `Blake3.Pure` (`Ix.Address.Pure`), and binaries that import
              # their closure at run time (`get_env!`) look for it under this
              # package's path in `LEAN_PATH`, so build it here as well.
              Blake3 = blake3-lean.packages.${system}.rust.overrideAttrs (old: {
                postBuild = (old.postBuild or "") + ''
                  lake build +Blake3.Pure
                '';
              });
            };
          }) (map (p: p.name) (builtins.filter (p: p.type == "path") lakeManifest.packages));
          lakePackageOverrides = pkgs.writers.writeJSON "lake-package-overrides.json" (
            lakeManifest
            // {
              packages = map (
                p:
                if p.type == "path" then
                  p
                else
                  {
                    inherit (p) name inherited;
                    type = "path";
                    dir = ".lake/packages/${p.name}";
                  }
              ) lakeManifest.packages;
            }
          );
          # Shared Lake build args: patches out the Cargo build (Crane handles it)
          lakeBuildArgs = {
            inherit lakeDeps;
            src = leanSrc;
            # Don't build the `ix_rs` static lib with Lake, since we build it with Crane
            # The Crane-built archive has no native executors: those are
            # generated from the certified programs, which compiling here
            # would need a writable artifact cache for. Formal jobs run on
            # the interpreter, with identical results.
            postPatch = ''
              substituteInPlace lakefile.lean --replace-fail 'cmd := "cargo"' 'cmd := "true"'
              substituteInPlace lakefile.lean \
                --replace-fail 'def nativeExecutors : Bool := true' 'def nativeExecutors : Bool := false'
            '';
            # Preserve workspace-relative paths instead of shadowing local packages.
            preConfigure = ''
              mkdir -p .lake
              ln -sf ${lakePackageOverrides} .lake/package-overrides.json
            '';
            # Symlink the Crane-built static lib to where Lake expects Cargo to
            # have left it
            postConfigure = ''
              mkdir -p target/release
              ln -s ${rustPkg}/lib/libix_ffi.a target/release/
            '';
            buildInputs = [
              pkgs.gmp
              lean
              pkgs.rsync
            ];
          };

          ixLib = lake2nix.mkPackage (
            lakeBuildArgs
            // {
              name = "Ix";
              # `Ix:shared` would fetch the kernel package's shared facets, which
              # import each other and cover the whole theory; executables compile
              # the native objects of their own import closures instead.
              buildLibrary = false;
            }
          );
          leanPath = pkgs.lib.concatStringsSep ":" (
            [ "${ixLib}/.lake/kernel/lib/lean" ]
            ++ map (d: "${d}/.lake/build/lib/lean") ([ ixLib ] ++ builtins.attrValues lakeDeps)
          );
          wrapBin =
            drv:
            pkgs.runCommand drv.name { nativeBuildInputs = [ pkgs.makeWrapper ]; } ''
              mkdir -p $out/bin
              for f in ${drv}/bin/*; do
                [ -x "$f" ] || continue
                makeWrapper "$f" "$out/bin/$(basename "$f")" \
                  --set LEAN_SYSROOT "${lean}" \
                  --set LEAN_PATH "${drv}/.lake/build/lib/lean:${drv}/.lake/kernel/lib/lean:${leanPath}"
              done
            '';
          # The CLI reuses ixLib's oleans. It imports Ix modules at run time, so
          # it installs its workspace for `wrapBin`'s LEAN_PATH.
          ixCLI = wrapBin (
            lake2nix.mkPackage (
              lakeBuildArgs
              // {
                lakeArtifacts = ixLib;
                installArtifacts = true;
                name = "ix";
              }
            )
          );

          # Lean + Rust shell for host development (`cargo build`, `lake build`).
          devShell = pkgs.mkShell {
            LIBCLANG_PATH = libclangPath;
            packages = with pkgs; [
              pkg-config
              openssl
              clang
              rustToolchain
              rust-analyzer
              lean
              cargo-deny
              valgrind
            ];
          };
          # Runs the shell's tools with the shell's own inputs and environment:
          # building the shell only proves its packages exist, not that the
          # commands developers run are on PATH and start.
          devShellTools =
            pkgs.runCommand "dev-shell-tools"
              {
                inherit (devShell) nativeBuildInputs buildInputs LIBCLANG_PATH;
              }
              ''
                lean --version
                lake --version
                rustc --version
                cargo --version
                cargo deny --version
                rust-analyzer --version
                clang --version
                pkg-config --exists openssl
                test -e "$LIBCLANG_PATH/libclang${pkgs.stdenv.hostPlatform.extensions.sharedLibrary}"
                touch $out
              '';
        in
        {
          packages = {
            default = ixLib;
            ix = ixCLI;
          };

          # The Nix build is a compatibility check: the library and the CLI
          # build, and the dev shell builds and its tools run. The tests run in
          # CI Jobs (`.github/workflows/ci.yml`), not in the flake. Building
          # the shell here also lets CI push its closure to Cachix.
          checks = {
            ix-lib = ixLib;
            ix-cli = ixCLI;
            dev-shell = devShell;
            dev-shell-tools = devShellTools;
          };

          devShells.default = devShell;

          # The treefmt wrapper around `nixfmt`, so `nix fmt .` can take a
          # directory; bare `nixfmt` only accepts individual files.
          formatter = pkgs.nixfmt-tree;
        };
    };
}
