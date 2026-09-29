{
  pkgs,
  lean,
  lake2nix,
  blake3,
  root,
  auditSrc,
}: let
  sources = import ./sources.nix {
    inherit (pkgs) lib;
    inherit root;
  };
  lakeDeps = lake2nix.buildDeps {
    src = sources.dependencies;
    depOverrideDeriv.Blake3 = blake3;
  };
  buildInputs = [pkgs.gmp lean pkgs.rsync];
  compilatrixLib = lake2nix.mkPackage {
    inherit lakeDeps buildInputs;
    src = sources.production;
    name = "Compilatrix";
    buildLibrary = true;
    meta.description = "Production compiler library and reusable Lake artifacts";
  };
  # Build every executable and the proof/fence collection once, reusing the
  # library's artifacts; each check below runs the resulting programs.
  programs = lake2nix.mkPackage {
    inherit lakeDeps buildInputs;
    src = sources.programs;
    name = "compilatrix-programs";
    prePatch = ''
      mkdir -p .lake
      cp -R ${compilatrixLib}/.lake/build .lake/build
      chmod -R +w .lake/build
    '';
    buildPhase = ''
      runHook preBuild
      lake -KciLeanLibDir=${lean}/lib/lean build CompilatrixTests.Proofs \
        ${pkgs.lib.escapeShellArgs sources.programTargets}
      runHook postBuild
    '';
    installPhase = ''
      mkdir -p "$out"
      cp -R .lake/build/bin "$out/bin"
    '';
    postInstall = "";
  };
  mkCheck = name: inputs: command:
    pkgs.runCommand "${name}-check" {
      nativeBuildInputs = [pkgs.coreutils] ++ inputs;
      LEAN_SYSROOT = "${lean}";
    } ''
      set -euo pipefail
      cp -rs ${auditSrc} source
      chmod u+w source
      cd source
      mkdir -p .lake/build
      ln -s ${programs}/bin .lake/build/bin
      ${command}
      touch $out
    '';
in {
  inherit compilatrixLib programs mkCheck;
}
