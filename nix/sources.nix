{
  lib,
  root,
}: let
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
  programTargets =
    builtins.attrNames
    (lib.filterAttrs (_: target: target.kind == "lean_exe") graph.targets);
in {
  inherit programTargets;
  # The production library, including the Aiur reference roots it builds on.
  production = source (["IxCC"] ++ graph.targets.AiurReference.roots);
  # Every executable plus the complete proof and fence collection, built once.
  programs = source (["IxCCTests.Proofs"]
    ++ lib.concatMap (name: graph.targets.${name}.roots) programTargets);
  dependencies = lib.fileset.toSource {
    inherit root;
    fileset = lib.fileset.unions common;
  };
}
