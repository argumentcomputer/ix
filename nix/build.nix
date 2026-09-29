{
  pkgs,
  lean,
  lake2nix,
  blake3,
  root,
}: let
  sources = import ./sources.nix {
    inherit (pkgs) lib;
    inherit root;
  };
  lakeDeps = lake2nix.buildDeps {
    src = sources.dependencies;
    depOverrideDeriv.Blake3 = blake3;
  };
  compilatrixLib = lake2nix.mkPackage {
    inherit lakeDeps;
    buildInputs = [pkgs.gmp lean pkgs.rsync];
    src = sources.production;
    name = "Compilatrix";
    buildLibrary = true;
    meta.description = "Production compiler library and reusable Lake artifacts";
  };
in {
  inherit compilatrixLib;
}
