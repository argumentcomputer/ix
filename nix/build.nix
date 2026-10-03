{
  pkgs,
  lean,
  lake2nix,
  blake3,
  ix-src,
  root,
  auditSrc,
}: let
  sources = import ./sources.nix {
    inherit (pkgs) lib;
    inherit root;
  };
  # «ix-kernel»: ix's `IxKernel/lakefile.lean` declares `srcDir := ".."` (the ix
  # checkout root), which lean4-nix cannot shadow (it copies only a
  # dependency's `subDir`), and its `IxKernel` library also holds the codec's
  # proofs and audits, which import the whole kernel: linking Compilatrix's
  # shared library would build all of it. So the pinned sources of the codec
  # closure Compilatrix imports (`Ix.Ixon.Canonical`: 11 modules under
  # `Ix/Address` and `Ix/Ixon`, unchanged) are packaged under the same package
  # name and toolchain with a library holding exactly those modules, built
  # once here with its shared and static facets. A module missing at a new
  # pin fails this build.
  ixKernelSrc = pkgs.runCommand "ix-kernel-src" {} ''
    mkdir -p $out/Ix
    cp ${ix-src}/IxKernel/lean-toolchain ${ix-src}/IxKernel/lake-manifest.json $out/
    cp -r ${ix-src}/Ix/Address ${ix-src}/Ix/Ixon $out/Ix/
    cat > $out/lakefile.lean <<'EOF'
    import Lake
    open Lake DSL

    package «ix-kernel» where
      version := v!"0.1.0"

    @[default_target]
    lean_lib IxKernel where
      roots := #[`Ix.Address.Core, `Ix.Ixon.Types.Kinds, `Ix.Ixon.Types.Modes,
        `Ix.Ixon.Types.Contract, `Ix.Ixon.Types, `Ix.Ixon.Codec, `Ix.Ixon.Wire,
        `Ix.Ixon.WireCheck, `Ix.Ixon.Bounded.Universe, `Ix.Ixon.Bounded.Constant,
        `Ix.Ixon.Canonical]
    EOF
  '';
  ixKernel = lake2nix.mkLakeDerivation {
    name = "IxKernel";
    src = ixKernelSrc;
    buildLibrary = true;
  };
  lakeDeps = lake2nix.buildDeps {
    src = sources.dependencies;
    depOverrideDeriv = {
      Blake3 = blake3;
      "«ix-kernel»" = ixKernel;
    };
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
  inherit compilatrixLib programs mkCheck ixKernel;
}
