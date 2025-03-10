{system, pkgs, fenix, crane, lean4-nix, blake3-lean}:
let
  # Pins the Rust toolchain
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
    # Builds the C file
    buildPhase = ''
      gcc -Wall -Werror -Wextra -c binius.c -o binius.o
      gcc -Wall -Werror -Wextra -c u128.c -o u128.o
      ar rcs libix_c.a binius.o u128.o
    '';
    # Installs the library files
    installPhase = ''
      mkdir -p $out/lib $out/include
      cp libix_c.a $out/lib/
      cp rust.h linear.h common.h $out/include/
    '';
  };

  # Blake3.lean C FFI dependency, needed for explicit static lib linking
  # See issue https://github.com/argumentcomputer/lean4-nix/issues/8
  blake3 = blake3-lean.inputs.blake3;
  blake3Lib = (blake3-lean.lib { inherit pkgs lean4-nix blake3; }).lib;
  blake3C = blake3Lib.blake3-c;

  # Lean package
  # Fetches external dependencies
  leanPkgBase = (lean4-nix.lake { inherit pkgs; }).mkPackage {
      src = ./.;
      roots = ["Ix" "Main"];
  };
  # Builds final library and links to FFI static libs
  leanPkg = (pkgs.lean.buildLeanPackage {
    name = "ix";
    src = ./.;
    deps = [ leanPkgBase ];
    roots = ["Ix" "Main"];
    linkFlags = [ "-L${rustPkg}/lib" "-lix_rs" "-L${cPkg}/lib" "-lix_c" "-L${blake3C}/lib" "-lblake3"];
  });
  # Builds test package
  leanTest = (pkgs.lean.buildLeanPackage {
    name = "ix_test";
    src = ./.;
    deps = [ leanPkg ];
    roots = ["Tests.Main" "Ix"];
    linkFlags = [ "-L${rustPkg}/lib" "-lix_rs" "-L${cPkg}/lib" "-lix_c" "-L${blake3C}/lib" "-lblake3"];
  });
  lib = {
    inherit
      rustToolchain
      leanPkg
      leanTest
      cPkg
      blake3C;
  };
in
{
  inherit lib;
}
