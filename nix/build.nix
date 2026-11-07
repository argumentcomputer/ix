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
  # «ix-ck»: the libraries of ix's `IxCK/lakefile.lean` declare
  # `srcDir := ".."` (the ix checkout root), which lean4-nix cannot shadow (it
  # copies only a dependency's `subDir`), and its `IxCK.Ixon` library also
  # holds the codec's proofs and audits, which import the kernel: linking
  # IxCC's shared library would build all of it. So the pinned sources of the
  # codec closure IxCC imports (`IxCK.Ixon.Canonical`: 11 modules under
  # `IxCK/Address` and `IxCK/Ixon`, unchanged) are packaged under the same
  # package name and toolchain with a library holding exactly those modules,
  # built once here with its shared and static facets. A module missing at a
  # new pin fails this build.
  ixCKSrc = pkgs.runCommand "ix-ck-src" {} ''
    mkdir -p $out/IxCK
    cp ${ix-src}/IxCK/lean-toolchain ${ix-src}/IxCK/lake-manifest.json $out/
    cp -r ${ix-src}/IxCK/Address ${ix-src}/IxCK/Ixon $out/IxCK/
    cat > $out/lakefile.lean <<'EOF'
    import Lake
    open Lake DSL

    package «ix-ck» where
      version := v!"0.1.0"

    @[default_target]
    lean_lib IxCK where
      roots := #[`IxCK.Address.Core, `IxCK.Ixon.Types.Kinds, `IxCK.Ixon.Types.Modes,
        `IxCK.Ixon.Types.Contract, `IxCK.Ixon.Types, `IxCK.Ixon.Codec, `IxCK.Ixon.Wire,
        `IxCK.Ixon.WireCheck, `IxCK.Ixon.Bounded.Universe, `IxCK.Ixon.Bounded.Constant,
        `IxCK.Ixon.Canonical]
    EOF
  '';
  ixCK = lake2nix.mkLakeDerivation {
    name = "IxCK";
    src = ixCKSrc;
    buildLibrary = true;
  };
  lakeDeps = lake2nix.buildDeps {
    src = sources.dependencies;
    depOverrideDeriv = {
      Blake3 = blake3;
      "«ix-ck»" = ixCK;
    };
  };
  # lean4-nix shadows each dependency under `.lake/packages/<manifest name>`;
  # for `«ix-ck»` that directory name is not ASCII, and Lake mangles it
  # when it passes object paths to the linker (`.lake/packages/302253ix-ck302273/…`
  # in clang's arguments). Move it to `ix-ck`, the directory Lake itself
  # checks the package out to, and point the package overrides there.
  packageOverrides = pkgs.writers.writeJSON "package-overrides.json" (let
    manifest = builtins.fromJSON (builtins.readFile (root + "/lake-manifest.json"));
    dir = name: if name == "«ix-ck»" then "ix-ck" else name;
  in
    manifest
    // {
      packages = map (p: {
        inherit (p) name;
        inherited = p.inherited or false;
        type = "path";
        dir = ".lake/packages/${dir p.name}";
      })
      manifest.packages;
    });
  asciiPackages = ''
    mv ".lake/packages/«ix-ck»" .lake/packages/ix-ck
    rm -f .lake/package-overrides.json
    cp ${packageOverrides} .lake/package-overrides.json
  '';
  buildInputs = [pkgs.gmp lean pkgs.rsync];
  ixccLib = lake2nix.mkPackage {
    inherit lakeDeps buildInputs;
    src = sources.production;
    name = "IxCC";
    buildLibrary = true;
    meta.description = "Production compiler library and reusable Lake artifacts";
    postConfigure = asciiPackages;
  };
  # Build every executable and the proof/fence collection once, reusing the
  # library's artifacts; each check below runs the resulting programs.
  programs = lake2nix.mkPackage {
    inherit lakeDeps buildInputs;
    src = sources.programs;
    name = "ixcc-programs";
    postConfigure = asciiPackages;
    prePatch = ''
      mkdir -p .lake
      cp -R ${ixccLib}/.lake/build .lake/build
      chmod -R +w .lake/build
    '';
    buildPhase = ''
      runHook preBuild
      lake -KciLeanLibDir=${lean}/lib/lean build IxCCTests.Proofs \
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
  inherit ixccLib programs mkCheck ixCK;
}
