{
  system,
  pkgs,
  fenix,
  crane,
  lean4-nix,
  blake3-lean,
}: let
  # Pins the Rust toolchain
  rustToolchain = fenix.packages.${system}.fromToolchainFile {
    file = ./rust-toolchain.toml;
    sha256 = "sha256-2eWc3xVTKqg5wKSHGwt1XoM/kUBC6y3MWfKg74Zn+fY=";
  };

  # Rust package
  craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;
  src = craneLib.cleanCargoSource ./.;
  commonArgs = {
    inherit src;
    strictDeps = true;

    buildInputs =
      [
        # Add additional build inputs here
      ]
      ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
        # Additional darwin specific inputs can be set here
        pkgs.libiconv
      ];
  };
  craneLibLLvmTools = craneLib.overrideToolchain rustToolchain;
  cargoArtifacts = craneLib.buildDepsOnly commonArgs;

  rustPkg = craneLib.buildPackage (commonArgs
    // {
      inherit cargoArtifacts;
    });

  # C Package
  cPkg = let
    # Function to get all files in `./c` ending with given extension
    getFiles = ext: builtins.filter (file: builtins.match (".*" + ext) file != null) (builtins.attrNames (builtins.readDir "${toString ./c}"));
    # Gets all C files in `./c`, without the extension
    cFiles = let ext = ".c"; in builtins.map (file: builtins.replaceStrings [ext] [""] file) (getFiles ext);
    # Creates `gcc -c` command for each C file
    buildCmd = builtins.map (file: "${pkgs.gcc}/bin/gcc -Wall -Werror -Wextra -c ${file}.c -o ${file}.o") cFiles;
    # Final `buildPhase` instructions
    buildSteps =
      buildCmd
      ++ [
        "ar rcs libix_c.a ${builtins.concatStringsSep " " (builtins.map (file: "${file}.o") cFiles)}"
      ];
    # Gets all header files in `./c`
    hFiles = getFiles ".h";
    # Final `installPhase` instructions
    installSteps = [
      "mkdir -p $out/lib $out/include"
      "cp libix_c.a $out/lib/"
      "cp ${builtins.concatStringsSep " " hFiles} $out/include/"
    ];
  in
    pkgs.stdenv.mkDerivation {
      pname = "ix_c";
      version = "0.1.0";
      src = ./c;
      buildInputs = [pkgs.gcc pkgs.lean.lean-all rustPkg];
      # Builds the C files
      buildPhase = builtins.concatStringsSep "\n" buildSteps;
      # Installs the library files
      installPhase = builtins.concatStringsSep "\n" installSteps;
    };

  # Blake3.lean C FFI dependency, needed for explicit static lib linking
  blake3C = blake3-lean.packages.${system}.staticLib;

  # Lean package, builds the Ix binary and links to FFI static libs
  # Note: downstream users of Ix as a library should import it in the lakefile,
  # only need to include the static libs as below in the final `mkPackage`
  leanPkg = (lean4-nix.lake {inherit pkgs;}).mkPackage {
    src = ./.;
    roots = ["Ix" "Main"];
    staticLibDeps = ["${rustPkg}/lib" "${cPkg}/lib" "${blake3C}/lib"];
  };

  lib = {
    inherit
      rustToolchain
      blake3C
      rustPkg
      cPkg
      leanPkg
      ;
  };
in {
  inherit lib;
}
