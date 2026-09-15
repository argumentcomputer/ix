# Optional x86-64 comparison environment. The root flake's CI checks never
# import this expression or build these comparison compilers.
let
  compiler = builtins.getFlake ("git+file://" + toString ../..);
  system = "x86_64-linux";
  pkgs = import compiler.inputs.nixpkgs {
    inherit system;
    config.allowUnfreePredicate = package: pkgs.lib.getName package == "compcert";
  };
  cakeBootstrap = pkgs.stdenv.mkDerivation {
    pname = "cakeml-benchmark-bootstrap";
    version = "3479";
    src = pkgs.fetchurl {
      url = "https://github.com/CakeML/cakeml/releases/download/v3479/cake-x64-64.tar.gz";
      sha256 = "e110bfcba19d6524ee4748608a67a275647445a048928cf623c2c9a973e31c9a";
    };
    makeFlags = ["cake" "CC=${pkgs.gcc}/bin/gcc"];
    installPhase = ''
      mkdir -p $out/bin
      cp cake basis_ffi.c $out/bin/
    '';
  };
in
  pkgs.mkShell {
    inputsFrom = [compiler.devShells.${system}.default];
    packages = with pkgs; [
      gcc
      clang
      compcert
      cakeBootstrap
      binutils
      time
      which
      git
      ripgrep
      gnutar
      gzip
      util-linux
      nix
    ];
  }
