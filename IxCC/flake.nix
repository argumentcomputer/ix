{
  description = "IxCC: a certified Lean 4 toolchain for Ix";

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

    # Lean 4 & Lake. Pinned to the exact rev ix and Blake3.lean lock so the
    # toolchain derivation dedups with its builds; move deliberately.
    lean4-nix.url = "github:argumentcomputer/lean4-nix/e828640c7710bb571eb052d02f1adb2ed5694c5e";

    # flake-parts via the copy lean4-nix already locks (single node)
    flake-parts.follows = "lean4-nix/flake-parts";

    # Blake3 FFI: the flake-built package (prebuilt Rust static lib)
    # overrides the Lake dep, whose lakefile shells out to cargo — the
    # sandbox forbids that. Keep the rev in lockstep with
    # lakefile.lean/lake-manifest.json. Nested inputs (crane, fenix,
    # blake3 source, flake-parts) are pinned at lock time to ix's
    # flake.lock revs — the combination proven on this machine.
    # Share the toolchain helper so Lean modules and Rust FFI headers use
    # the same reviewed Lean release and Nix derivation.
    blake3-lean.url = "github:argumentcomputer/Blake3.lean/3f8b805614a0bae1c033469ff893a8f0ee85f601";
    blake3-lean.inputs.lean4-nix.follows = "lean4-nix";

    # Ix's certified-kernel package (`IxCK/`), as source: the Lake
    # dependency «ix-ck», of which IxCC imports only the pure Ixon
    # v4 codec (`IxCK.Ixon.Canonical` and its closure). Keep the revision in
    # lockstep with lakefile.lean/lake-manifest.json and the trust ledger.
    ix-src = {
      url = "github:argumentcomputer/ix/2dd96055e68cff3dcaf1fe0c32e6a1b7df33d6c2";
      flake = false;
    };
  };

  outputs = inputs @ {
    flake-parts,
    lean4-nix,
    blake3-lean,
    ix-src,
    ...
  }: let
    # Crane's own Rust helper uses nixpkgs' Cargo fetcher, independently of
    # Crane's normal static.crates.io registry. The crates.io API endpoint can
    # reject CI downloads; change only that host, retaining TLS verification,
    # the upstream lockfile/checksums, and the existing fixed-output paths.
    crane = blake3-lean.inputs.crane;
    craneWithStaticCrates =
      crane
      // {
        mkLib = pkgs:
          (crane.mkLib pkgs).overrideScope (_final: prev: {
            craneUtils = prev.craneUtils.overrideAttrs (old: {
              cargoDeps =
                (pkgs.rustPlatform.importCargoLock.override {
                  fetchurl = args:
                    pkgs.fetchurl (args
                      // {
                        url =
                          pkgs.lib.replaceStrings
                          ["https://crates.io/api/v1/crates/"]
                          ["https://static.crates.io/crates/"]
                          args.url;
                      });
                }) {
                  lockFile = old.cargoDeps.lockFile;
                };
            });
          });
      };
    # Reuse the pinned upstream flake and all its other inputs unchanged.
    blake3WithStaticCrates = assert builtins.readFile (blake3-lean.outPath + "/lean-toolchain")
    == builtins.readFile ./lean-toolchain;
      (import (blake3-lean.outPath + "/flake.nix")).outputs
      (blake3-lean.inputs
        // {
          self = blake3-lean;
          crane = craneWithStaticCrates;
        });
  in
    flake-parts.lib.mkFlake {inherit inputs;} {
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
        # Pinned Lean toolchain, resolved from ./lean-toolchain.
        # Pin changes follow the compatibility gates in docs/roadmap.md.
        lean = lean4-nix.lib.${system}.fromToolchainFile ./lean-toolchain;
        lake2nix = pkgs.callPackage lean4-nix.lake {inherit lean;};
        # The trust audit and checks see the complete tracked source tree;
        # the compiler builds use the narrower module source sets.
        auditSrc = ./.;
        build = import ./nix/build.nix {
          inherit pkgs lean lake2nix auditSrc ix-src;
          root = ./.;
          blake3 = blake3WithStaticCrates.packages.${system}.rust;
        };
        inherit (build) ixccLib programs mkCheck;
        gateChecks = import ./nix/checks.nix {
          inherit pkgs system auditSrc blake3-lean ix-src mkCheck;
        };
      in {
        packages = {
          default = ixccLib;
          ixcc = ixccLib;
        };

        # The compiler's command line (`IxCC.Cli`), from the shared
        # program build: `nix run .#ixcc -- compile ...`.
        apps.ixcc = {
          type = "app";
          program = "${programs}/bin/ixcc";
          meta.description = "Compile an Ixon v3 closure to an x86-64 ELF object";
        };

        # The required check surface was emptied on 2026-09-29 and returns
        # gate by gate (docs/ci.md). Every check reuses one program build.
        checks = {
          build = ixccLib;
          proofs = programs;
        } // gateChecks;

        devShells.default = pkgs.mkShell {
          # Blake3.lean's Rust binding uses bindgen through lean-ffi.
          # Point it at the pinned nixpkgs libclang so `lake exe tests`
          # works in the documented dev loop.
          LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";
          packages = [
            lean
            # Blake3.lean's lakefile shells out to `cargo build` for its
            # Rust static lib, so a devshell `lake build` needs a Rust
            # toolchain (the nix build path instead injects the
            # flake-built artifact via depOverrideDeriv).
            pkgs.clang
            pkgs.binutils
            pkgs.cargo
            pkgs.rustc
          ];
        };

        formatter = pkgs.alejandra;
      };
    };
}
