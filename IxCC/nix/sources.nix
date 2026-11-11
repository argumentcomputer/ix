{
  lib,
  # The ix workspace (the repository root, as a path). IxCC selects its own
  # sources from it, so a change outside them leaves its derivations unchanged.
  workspace,
}: let
  root = workspace + "/IxCC";
  graph = builtins.fromJSON (builtins.readFile (root + "/nix/lean-modules.json"));
  modules = graph.modules;
  closure = roots:
    builtins.genericClosure {
      startSet = map (key: {inherit key;}) roots;
      operator = item:
        map (key: {inherit key;})
        (builtins.filter (name: builtins.hasAttr name modules) modules.${item.key}.imports);
    };
  common = map (path: root + "/${path}") [
    "lakefile.lean"
    "lake-manifest.json"
    "lean-toolchain"
  ];
  source = roots:
    lib.fileset.toSource {
      inherit root;
      fileset =
        lib.fileset.unions
        (common ++ map (item: root + "/${modules.${item.key}.path}") (closure roots));
    };
  # The grounding library's suite is built with the library by `ixcc-grounding`, not by the
  # shared program build, so editing the grounding work never rebuilds the programs.
  groundingTargets = ["tests-grounding"];
  programTargets =
    builtins.filter (name: !(builtins.elem name groundingTargets))
    (builtins.attrNames
      (lib.filterAttrs (_: target: target.kind == "lean_exe") graph.targets));
  # The trust ledger is the one record of what IxCC takes from the workspace:
  # the pure Lean dependency «ix-ck» (its directory and the import closure
  # whose every file it hashes) and the repository files it audits.
  ledger = builtins.fromJSON (builtins.readFile (root + "/docs/trusted-externs.json"));
  ixCKEntry = let
    entries = builtins.filter (entry: entry.lake_package == "«ix-ck»") ledger.lean_dependencies;
  in
    assert builtins.length entries == 1; builtins.head entries;
  ixCKRoot = root + "/${ixCKEntry.pins.workspace_path}";
  ixCKSourceRoot = ixCKRoot + "/${ixCKEntry.source_dir}";
  ixCKFiles = map (path: ixCKSourceRoot + "/${path}") (builtins.attrNames ixCKEntry.closure);
  repository = root + "/${ledger.policy.repository.root}";
in {
  inherit root programTargets groundingTargets;
  # The production library, with the vendored Aiur reference it imports.
  production = source ["IxCC"];
  # Every executable plus the complete proof and fence collection, built once.
  programs = source (["IxCCTests.Proofs"]
    ++ lib.concatMap (name: graph.targets.${name}.roots) programTargets);
  # The grounding library (which imports the kernel's model) and its suite.
  grounding = source (["IxCCGrounding"]
    ++ lib.concatMap (name: graph.targets.${name}.roots) groundingTargets);
  dependencies = lib.fileset.toSource {
    inherit root;
    fileset = lib.fileset.unions common;
  };
  # «ix-ck»: exactly the codec closure the ledger records, at the paths its
  # module names give (`IxCK/…`), with the package's toolchain and manifest
  # and the closure's module names.
  ixCK = {
    modules = lib.fileset.toSource {
      root = ixCKSourceRoot;
      fileset = lib.fileset.unions ixCKFiles;
    };
    toolchain = ixCKRoot + "/lean-toolchain";
    manifest = ixCKRoot + "/lake-manifest.json";
    moduleNames =
      map (path: lib.replaceStrings ["/"] ["."] (lib.removeSuffix ".lean" path))
      (builtins.attrNames ixCKEntry.closure);
  };
  # The complete tracked IxCC tree, which the checks run against.
  audit = lib.fileset.toSource {
    inherit root;
    fileset = root;
  };
  # The workspace as the trust ledger audits it, with IxCC at its path: the
  # IxCC tree, «ix-ck»'s lakefile and recorded closure, the repository's
  # flake.lock and lean-toolchain, the workflows the ledger scopes, the
  # repository files it pins and the repository-local actions they may use.
  ledgerWorkspace = lib.fileset.toSource {
    root = workspace;
    fileset = lib.fileset.unions ([
        root
        (ixCKRoot + "/lakefile.lean")
        (repository + "/flake.lock")
        (repository + "/lean-toolchain")
        (lib.fileset.maybeMissing (repository + "/.github/actions"))
      ]
      ++ ixCKFiles
      ++ map (path: repository + "/${path}") (ledger.policy.repository.workflows or [])
      ++ map (path: repository + "/${path}")
      (builtins.attrNames (ledger.integrity.repository_files or {})));
  };
}
