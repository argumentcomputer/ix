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

    # CUDA-only packages, independently pinned so the ordinary build graph
    # can retain lean4-nix's older Nixpkgs revision.
    cuda-nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

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
          # CUDA is opt-in and unfree. Its dedicated package set locks CUDA
          # 13.2 without changing the default shell or ordinary package/check
          # graph.
          cudaPkgs = import inputs.cuda-nixpkgs {
            inherit system;
            config.allowUnfree = true;
          };
          cudaToolkit = cudaPkgs.symlinkJoin {
            name = "ix-cuda-13.2-toolkit";
            paths = [
              cudaPkgs.cudaPackages_13_2.cccl
              cudaPkgs.cudaPackages_13_2.cuda_crt
              cudaPkgs.cudaPackages_13_2.cuda_cudart
              cudaPkgs.cudaPackages_13_2.cuda_nvcc
              cudaPkgs.cudaPackages_13_2.libnvvm
            ];
            postBuild = ''
              ln -s lib "$out/lib64"
            '';
          };

          # Pins the Lean toolchain; a plain derivation, no overlay involved
          lean = lean4-nix.lib.${system}.fromToolchainFile ./lean-toolchain;

          # Pins the Rust toolchain
          rustToolchain = fenix.packages.${system}.fromToolchainFile {
            file = ./rust-toolchain.toml;
            sha256 = "sha256-p8h3Sl/YRByZfZTAKXdsvF6xEenXKrXSVvpphmZENH4=";
          };

          # gnark requires the 1.26.8 patch release; the newer pinned package
          # set supplies its matching bootstrap and platform patches.
          plonkGo = cudaPkgs.go_1_26.overrideAttrs (_: {
            version = "1.26.8";
            src = cudaPkgs.fetchurl {
              url = "https://go.dev/dl/go1.26.8.src.tar.gz";
              hash = "sha256-Tjm5jkL5RvoFrIvFtxh335fb23y7Gnd7VBZnrXEX/S4=";
            };
          });
          plonkSources = pkgs.lib.fileset.fileFilter (
            file: file.hasExt "go" || file.hasExt "json" || file.hasExt "bin"
              || file.name == "go.mod" || file.name == "go.sum"
          ) ./tools/plonk-wrapper;
          plonkCudaSources = pkgs.lib.fileset.fileFilter (
            file: file.hasExt "go" || file.hasExt "json" || file.hasExt "bin"
              || file.hasExt "py" || file.hasExt "patch"
              || file.name == "go.mod" || file.name == "go.sum"
          ) ./tools/plonk-wrapper;
          plonkSppark = pkgs.fetchFromGitHub {
            owner = "argumentcomputer";
            repo = "sppark";
            rev = "114feb69ebfe029e2caa5e6c2d372c695e5d4da8";
            hash = "sha256-/KXq6RuAUpRT0xJsXCSZsT1iONhbeHnXWcmTJL4ltQs=";
          };
          plonkBlst = pkgs.fetchzip {
            url = "https://static.crates.io/crates/blst/blst-0.3.16.crate";
            extension = "tar.gz";
            hash = "sha256-OHEKeKwl7RhPOiqILiRTZACmRLlmIaRuCE2qwKTfiIc=";
          };
          plonkCudaNative = pkgs.stdenv.mkDerivation {
            pname = "ix-plonk-bn254-cuda";
            version = "0.1.0";
            src = pkgs.lib.fileset.toSource {
              root = ./crates/proof-compression/cuda;
              fileset = pkgs.lib.fileset.fileFilter (
                file: builtins.any file.hasExt [ "cu" "cuh" "cpp" "h" "hpp" "py" "map" "json" "patch" ]
              ) ./crates/proof-compression/cuda;
            };
            nativeBuildInputs = [ pkgs.python3 pkgs.patch cudaToolkit ];
            CUDA_HOME = "${cudaToolkit}";
            NVCC = "${cudaToolkit}/bin/nvcc";
            IX_PLONK_CUDA_ARCHS = "120";
            dontConfigure = true;
            buildPhase = ''
              runHook preBuild
              python3 plonk/build.py --sppark ${plonkSppark} --blst ${plonkBlst}/blst --out native
              runHook postBuild
            '';
            installPhase = ''
              mkdir -p "$out/lib" "$out/include" "$out/share/ix-plonk-cuda"
              cp native/libix_plonk_bn254_cuda.so "$out/lib/"
              cp plonk/ix_plonk_bn254.h "$out/include/"
              cp native/*.json "$out/share/ix-plonk-cuda/"
            '';
            meta.platforms = [ "x86_64-linux" ];
          };
          mkPlonkHelper = { cuda ? false }: (cudaPkgs.buildGoModule.override { go = plonkGo; }) {
            pname = "ix-bn254-plonk-wrapper"
              + pkgs.lib.optionalString cuda "-cuda";
            tags = pkgs.lib.optional cuda "cuda";
            version = "0.1.0";
            src = pkgs.lib.fileset.toSource {
              root = ./tools/plonk-wrapper;
              fileset = if cuda then plonkCudaSources else plonkSources;
            };
            vendorHash = "sha256-atTpFnSORqh5A+LzECBF9gR0qCr7G2lNXpVuFFSS5to=";
            subPackages = [ "." ];
            env.CGO_ENABLED = if cuda then "1" else "0";
            env.GOTOOLCHAIN = "local";
            env.CGO_CFLAGS = pkgs.lib.optionalString cuda "-I${plonkCudaNative}/include";
            env.CGO_LDFLAGS = pkgs.lib.optionalString cuda "-L${plonkCudaNative}/lib -Wl,-rpath,${plonkCudaNative}/lib -lix_plonk_bn254_cuda";
            nativeBuildInputs = pkgs.lib.optionals cuda [ pkgs.python3 pkgs.patch ];
            buildInputs = pkgs.lib.optional cuda plonkCudaNative;
            postConfigure = pkgs.lib.optionalString cuda ''
              chmod -R u+w vendor/github.com/consensys/gnark
              python3 build_cuda.py --patch-vendor vendor/github.com/consensys/gnark
            '';
            postInstall = ''
              mv "$out/bin/plonk-wrapper" "$out/bin/ix-bn254-plonk-wrapper"
            '' + pkgs.lib.optionalString cuda ''
              mkdir -p "$out/lib"
              ln -s ${plonkCudaNative}/lib/libix_plonk_bn254_cuda.so "$out/lib/"
            '';
          };

          plonkHelper = mkPlonkHelper { };
          plonkCudaHelper = mkPlonkHelper { cuda = true; };

          # Rust package
          craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;
          # The Cargo files the workspace builds from.
          cargoSource = pkgs.lib.fileset.fromSource (craneLib.cleanCargoSource ./.);
          # Profiles are embedded in the verifier; compression tests also read
          # binary fixtures that Cargo's source filter does not retain.
          compressionData = pkgs.lib.fileset.unions [
            ./crates/proof-compression/tests/fixtures
          ];
          # The Rust tests `include_bytes!` the `.ixe` files under
          # `Tests/Fixtures`: environments serialized by Lean, read back to check
          # both sides agree on the format.
          src = pkgs.lib.fileset.toSource {
            root = ./.;
            fileset = pkgs.lib.fileset.unions [
              cargoSource
              compressionData
              ./Tests/Fixtures/ixon-v4
            ];
          };
          # Rust code generation for the sandboxed builds. `.cargo/config.toml`
          # selects `-Ctarget-cpu=native`, and crane keeps that file in the
          # source, so without an override every Rust derivation is compiled
          # for whichever host builds it while sharing one store path: Cachix
          # then hands Intel-native binaries to AMD hosts and vice versa.
          # Default to the x86-64-v4 baseline setup-rust-toolchain's `portable`
          # mode uses, so CI caches one portable set. For a build tuned to the
          # local machine (the dev shell's cargo already is, via the config
          # file):
          #
          #   IX_RUST_CODEGEN=native nix build --impure
          #
          # The flag string is part of the derivation, so a native build has
          # its own store path and is never substituted from Cachix. Pure
          # evaluation sees an empty variable and takes the default.
          rustCodegen =
            let
              requested = builtins.getEnv "IX_RUST_CODEGEN";
            in
            if requested == "native" then
              "-Ctarget-cpu=native"
            else if requested == "" || requested == "portable" then
              "-Ctarget-cpu=x86-64-v4 -Ctarget-feature=+avx512vbmi2,+gfni"
            else
              throw "IX_RUST_CODEGEN must be `portable` or `native`, got `${requested}`";
          craneArgs =
            pkgs.lib.optionalAttrs pkgs.stdenv.hostPlatform.isx86_64 {
              # Environment form of the `build.rustflags` key the config file sets
              CARGO_BUILD_RUSTFLAGS = rustCodegen;
            }
            // {
              inherit src;
              pname = "ix";
              version = "0.1.0";
              strictDeps = true;

              # build.rs uses LEAN_SYSROOT to locate lean/lean.h for bindgen
              LEAN_SYSROOT = "${lean}";
              # bindgen needs libclang to parse C headers
              LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";
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
          # by the package builds and clippy. CUDA remains opt-in and is
          # compiled separately in CI with the CUDA toolkit available.
          cargoArtifacts = craneLib.buildDepsOnly (
            craneArgs
            // {
              cargoExtraArgs = "--locked --features parallel,test-ffi,net";
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
                "--locked --features parallel" + pkgs.lib.optionalString (!pkgs.stdenv.isDarwin) ",net";
              doCheck = false;
            }
          );

          # Lake package
          lake2nix = pkgs.callPackage lean4-nix.lake { inherit lean; };
          # Restrict the Lake build inputs to files traced by the Lean and
          # Rust archive targets. Cargo itself is still handled by Crane, but
          # Lake needs the Rust sources and manifests to calculate the archive
          # dependency trace before copying the prebuilt static library.
          leanSrc = pkgs.lib.fileset.toSource {
            root = ./.;
            fileset = pkgs.lib.fileset.unions [
              # What `lake build` reads: Lean sources, manifests, FFI shims.
              (pkgs.lib.fileset.fromSource (lake2nix.cleanLakeSource ./.))
              ./IxC/lake-manifest.json
              ./IxC/lean-toolchain
              # What its Rust archive target traces, as Crane sees it.
              cargoSource
              compressionData
              plonkSources
            ];
          };
          lakeManifest = builtins.fromJSON (builtins.readFile ./lake-manifest.json);
          # Local packages build in the workspace; buildDeps only supports Git sources.
          lakeDeps = builtins.removeAttrs (lake2nix.buildDeps {
            src = leanSrc;
            depOverrideDeriv = {
              Blake3 = blake3-lean.packages.${system}.rust;
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
          mkLakeBuildArgs = rustLib: {
            inherit lakeDeps;
            src = leanSrc;
            IX_PLONK_PREBUILT = "${plonkHelper}/bin/ix-bn254-plonk-wrapper";
            # Don't build the `ix_rs` static lib with Lake, since we build it with Crane
            postPatch = ''
              substituteInPlace lakefile.lean --replace-fail 'proc { cmd := "cargo"' '--proc { cmd := "cargo"'
            '';
            # Preserve workspace-relative paths instead of shadowing local packages.
            preConfigure = ''
              mkdir -p .lake
              ln -sf ${lakePackageOverrides} .lake/package-overrides.json
            '';
            # Symlink the Crane-built static lib and the compression worker
            # executable to where Lake expects Cargo to have left them
            postConfigure = ''
              mkdir -p target/release
              ln -s ${rustLib}/lib/libix_ffi.a target/release/
              ln -s ${rustLib}/bin/ix-compression-worker target/release/
            '';
            buildInputs = [
              pkgs.gmp
              lean
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
              # `Ix:shared` would fetch the kernel package's shared facets, which
              # import each other and cover the whole theory; executables compile
              # the native objects of their own import closures instead.
              buildLibrary = false;
            }
          );
          lakeBinArgs = lakeBuildArgs // {
            lakeArtifacts = ixLib;
            # Binaries that import Ix.Meta need .olean files at runtime via LEAN_PATH
            installArtifacts = true;
          };
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
                lakeArtifacts = ixLib;
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
          packages = {
            default = ixLib;
            ix = ixCLI;
            plonk-wrapper = plonkHelper;
            plonk-wrapper-cuda = plonkCudaHelper;
            # `checks` are built by `nix flake check`; exposing this derivation
            # as a package keeps the ignored suite available on demand without
            # adding it to the default check set.
            nextest-ignored = craneLib.cargoNextest (
              craneArgs
              // {
                inherit cargoArtifacts;
                cargoExtraArgs = "--locked --workspace";
                cargoNextestExtraArgs = "--profile ci --run-ignored only";
              }
            );
            zkv-prover = ZKVotingProver // {
              meta.mainProgram = "Apps-ZKVoting-Prover";
            };
          };

          checks = {
            plonk-wrapper = plonkHelper;
            # Lint the host workspace; warnings are errors.
            clippy = craneLib.cargoClippy (
              craneArgs
              // {
                inherit cargoArtifacts;
                cargoExtraArgs = "--locked --features parallel,test-ffi,net";
                cargoClippyExtraArgs = "--all-targets -- -D warnings";
              }
            );
            # Non-ignored Rust unit tests across the host workspace.
            nextest = craneLib.cargoNextest (
              craneArgs
              // {
                inherit cargoArtifacts;
                cargoExtraArgs = "--locked --workspace";
                cargoNextestExtraArgs = "--profile ci";
              }
            );
            # Lean test suite. The suite reads fixtures and writes scratch
            # files by paths relative to the working dir, so run it from a
            # writable copy of the source tree, as if from a checkout.
            ix-tests = pkgs.runCommandCC "ix-tests" {
              nativeBuildInputs = [ rustToolchain ];
            } ''
              cp -r ${./.} src
              chmod -R u+w src
              # IxTests depends on the ix target, so its wrapped output already
              # contains the matching CLI. Recreate Lake's checkout-relative
              # path for tests that intentionally exercise that CLI.
              mkdir -p src/.lake/build/bin
              ln -s ${ixTest}/bin/ix src/.lake/build/bin/ix
              cd src
              ${ixTest}/bin/IxTests
              touch $out
            '';
          };

          devShells = {
            # Lean + Rust shell for host development (`cargo build`, `lake build`).
            default = pkgs.mkShell {
              LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";
              packages = with pkgs; [
                pkg-config
                openssl
                clang
                rustToolchain
                rust-analyzer
                lean
                cargo-deny
                valgrind
                plonkGo
              ];
            };
          }
          // pkgs.lib.optionalAttrs (system == "x86_64-linux") {
            # CUDA stays separate so CPU development does not fetch NVIDIA's
            # toolkit. Pinning NVCC/CUDA_HOME prevents a host-level
            # `/usr/local/cuda` from silently selecting an incompatible
            # compiler or runtime.
            cuda = pkgs.mkShell {
              LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";
              NVCC = "${cudaToolkit}/bin/nvcc";
              CUDA_HOME = "${cudaToolkit}";
              CUDA_PATH = "${cudaToolkit}";
              packages =
                (with pkgs; [
                  pkg-config
                  openssl
                  clang
                  rustToolchain
                  rust-analyzer
                  lean
                  cargo-deny
                  valgrind
                  plonkGo
                ])
                ++ [ cudaToolkit ];
              shellHook = ''
                export PATH="${cudaToolkit}/bin:$PATH"
                export LD_LIBRARY_PATH="${cudaToolkit}/lib:${pkgs.stdenv.cc.cc.lib}/lib''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

                # Nix's dynamic loader does not search the host driver's
                # library directory. Preload only libcuda to avoid mixing libc.
                for ixCudaDriverLib in \
                  /run/opengl-driver/lib/libcuda.so.1 \
                  /usr/lib/x86_64-linux-gnu/libcuda.so.1 \
                  /usr/lib64/libcuda.so.1; do
                  if [ -e "$ixCudaDriverLib" ]; then
                    export LD_PRELOAD="$ixCudaDriverLib''${LD_PRELOAD:+:$LD_PRELOAD}"
                    break
                  fi
                done
                unset ixCudaDriverLib
              '';
            };
          };

          # The treefmt wrapper around `nixfmt`, so `nix fmt .` can take a
          # directory; bare `nixfmt` only accepts individual files.
          formatter = pkgs.nixfmt-tree;
        };
    };
}
