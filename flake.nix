{
  description = "Compilatr.ix: a certified Lean 4 toolchain for Ix";

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

    # Lean 4 & Lake. Pinned to the exact rev lean4lean locks so the
    # toolchain derivation dedups with its builds; move deliberately.
    lean4-nix.url = "github:argumentcomputer/lean4-nix/c8bce66594bbf62073d0097ca5ddc44321f2d14e";

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
    blake3-lean.url = "github:argumentcomputer/Blake3.lean/c32002eeed36c520dfb73de32ef53483652e3aa5";
    blake3-lean.inputs.lean4-nix.follows = "lean4-nix";
  };

  outputs = inputs @ {
    flake-parts,
    lean4-nix,
    blake3-lean,
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
          inherit pkgs lean lake2nix auditSrc;
          root = ./.;
          blake3 = blake3WithStaticCrates.packages.${system}.rust;
        };
        inherit (build) compilatrixLib programs mkCheck;
        gateChecks = import ./nix/checks.nix {
          inherit pkgs system auditSrc blake3-lean mkCheck;
        };
      in {
        packages = {
          default = compilatrixLib;
          compilatrix = compilatrixLib;
        };

        # The required check surface was emptied on 2026-09-29 and returns
        # gate by gate (docs/ci.md). Every check reuses one program build.
        checks = {
          build = compilatrixLib;
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
