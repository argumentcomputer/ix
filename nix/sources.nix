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
    "native/hpt_cache_sync.c"
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
  # These modules are imported by name in the compiled Lean frontend checks.
  dynamicRoots = ["Ix.MultiStark.Verify.Source" "Compilatrix.Ixby.Runtime.Examples"];
in {
  inherit programTargets dynamicRoots;
  production = source ["Compilatrix"];
  programs = source (dynamicRoots ++ lib.concatMap (name: graph.targets.${name}.roots) programTargets);
  proofs = source ["CompilatrixTests.Proofs"];
  dependencies = lib.fileset.toSource {
    inherit root;
    fileset = lib.fileset.unions common;
  };
}
