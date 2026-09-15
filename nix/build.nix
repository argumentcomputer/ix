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
  # Copy project artifacts only; the helper prepares fresh dependency shadows
  # in configurePhase. Retain traces and native objects so Lake can reuse them.
  reuse = artifact: ''
    mkdir -p .lake
    cp -R ${artifact}/.lake/build .lake/build
    chmod -R +w .lake/build
  '';
  compilatrixLib = lake2nix.mkPackage {
    inherit lakeDeps buildInputs;
    src = sources.production;
    name = "Compilatrix";
    buildLibrary = true;
    meta.description = "Production compiler library and reusable Lake artifacts";
  };
  ciPrograms = lake2nix.mkPackage {
    inherit lakeDeps buildInputs;
    src = sources.programs;
    name = "compilatrix-ci-programs";
    outputs = ["out" "runtime"];
    prePatch = reuse compilatrixLib;
    buildPhase = ''
      runHook preBuild
      lake -KciLeanLibDir=${lean}/lib/lean build ${pkgs.lib.escapeShellArgs (sources.programTargets ++ sources.dynamicRoots)}
      runHook postBuild
    '';
    installPhase = ''
      mkdir -p "$out/.lake" "$runtime/lib/lean"
      rsync -a --exclude='/bin/' .lake/build/ "$out/.lake/build/"
      cp -R .lake/build/bin "$runtime/bin"
      # Dynamic frontend imports need oleans, but no compiler build traces,
      # object files, dependency source trees, or Rust toolchain in the bundle.
      rsync -a --include='*/' --include='*.olean*' --exclude='*' \
        .lake/build/lib/lean/ "$runtime/lib/lean/"
      rsync -a --include='*/' --include='*.olean*' --exclude='*' \
        ${blake3}/.lake/build/lib/lean/ "$runtime/lib/lean/"
    '';
    postInstall = "";
  };
  proofsCheck = lake2nix.mkPackage {
    inherit lakeDeps buildInputs;
    src = sources.proofs;
    name = "compilatrix-proofs";
    prePatch = reuse ciPrograms;
    buildPhase = ''
      lake build CompilatrixTests.Proofs
    '';
    installPhase = "touch $out";
    postInstall = "";
  };
  # These dependencies are available from the configured binary caches.
  # Jobs fetch them normally; only this run's project artifact is uploaded.
  runtimeSupport =
    pkgs.linkFarm "compilatrix-ci-runtime-support"
    (map (path: {
        name = pkgs.lib.getName path;
        inherit path;
      })
      ([lean pkgs.gmp] ++ pkgs.lib.optionals pkgs.stdenv.isLinux [pkgs.stdenv.cc.libc]));
  mkCheck = name: inputs: command:
    pkgs.runCommand "${name}-check" {
      nativeBuildInputs = [pkgs.coreutils] ++ inputs;
      LEAN_SYSROOT = "${lean}";
      LEAN_PATH = "${ciPrograms.runtime}/lib/lean:${lean}/lib/lean";
    } ''
      set -euo pipefail
      cp -rs ${auditSrc} source
      chmod u+w source
      cd source
      mkdir -p .lake/build
      ln -s ${ciPrograms.runtime}/bin .lake/build/bin
      ${command}
      touch $out
    '';
in {
  inherit compilatrixLib ciPrograms proofsCheck runtimeSupport mkCheck;
}
