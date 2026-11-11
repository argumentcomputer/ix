{
  pkgs,
  lean,
  lake2nix,
  blake3,
  # The ix workspace (the repository root); see sources.nix.
  workspace,
}: let
  sources = import ./sources.nix {
    inherit (pkgs) lib;
    inherit workspace;
  };
  inherit (sources) root;
  # «ix-ck»: the libraries of ix's `IxCK/lakefile.lean` declare
  # `srcDir := ".."` (the ix checkout root), which lean4-nix cannot shadow (it
  # copies only a dependency's own directory), and its `IxCK.Ixon` library
  # also holds the codec's proofs and audits, which import the kernel: linking
  # IxCC's shared library would build all of it. So the sources of the
  # closure IxCC imports (the files the trust ledger hashes: `IxCK.Ixon.Canonical`
  # and its imports, under `IxCK/Address` and `IxCK/Ixon`, the role vocabulary
  # `IxCK.Kernel.Key`, and the kernel's tiered admission entry, prelude and
  # executed typing core with their imports under `IxCK/Kernel`, unchanged) are
  # packaged under the same package name and toolchain with a library holding
  # exactly those modules, built once here with its shared and static facets.
  # A module the closure imports but the ledger does not record fails this
  # build.
  ixCKSrc = pkgs.runCommand "ix-ck-src" {} ''
    mkdir -p $out
    cp -r ${sources.ixCK.modules}/. $out/
    chmod -R u+w $out
    cp ${sources.ixCK.toolchain} $out/lean-toolchain
    cp ${sources.ixCK.manifest} $out/lake-manifest.json
    cat > $out/lakefile.lean <<'LAKEFILE'
    import Lake
    open Lake DSL

    package «ix-ck» where
      version := v!"0.1.0"

    @[default_target]
    lean_lib IxCK where
      roots := #[${pkgs.lib.concatMapStringsSep ", " (name: "`" + name) sources.ixCK.moduleNames}]
    LAKEFILE
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
  # The grounding library, with its axiom fence, and its suite (`tests-grounding`), reusing the
  # library's artifacts like the program build; the one build that compiles the kernel's
  # model (`IxCK.Kernel.Denotes` and its imports, in the «ix-ck» closure the ledger records).
  grounding = lake2nix.mkPackage {
    inherit lakeDeps buildInputs;
    src = sources.grounding;
    name = "ixcc-grounding";
    postConfigure = asciiPackages;
    prePatch = ''
      mkdir -p .lake
      cp -R ${ixccLib}/.lake/build .lake/build
      chmod -R +w .lake/build
    '';
    buildPhase = ''
      runHook preBuild
      lake -KciLeanLibDir=${lean}/lib/lean build IxCCGrounding \
        ${pkgs.lib.escapeShellArgs sources.groundingTargets}
      runHook postBuild
    '';
    installPhase = ''
      mkdir -p "$out"
      cp -R .lake/build/bin "$out/bin"
    '';
    postInstall = "";
  };
  # The checks see the complete tracked IxCC tree; the trust-ledger check sees
  # it inside the workspace it audits (`ledgerWorkspace`, IxCC at `IxCC/`).
  auditSrc = sources.audit;
  ledgerWorkspace = sources.ledgerWorkspace;
  mkCheckWith = bin: name: inputs: command:
    pkgs.runCommand "${name}-check" {
      nativeBuildInputs = [pkgs.coreutils] ++ inputs;
      LEAN_SYSROOT = "${lean}";
    } ''
      set -euo pipefail
      cp -rs ${auditSrc} source
      chmod u+w source
      cd source
      mkdir -p .lake/build
      ln -s ${bin}/bin .lake/build/bin
      ${command}
      touch $out
    '';
  mkCheck = mkCheckWith programs;
in {
  inherit ixccLib programs grounding mkCheck mkCheckWith ixCK auditSrc ledgerWorkspace;
}
