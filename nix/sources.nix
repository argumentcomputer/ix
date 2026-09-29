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
in {
  # The native facet builds the whole reference library, including roots
  # outside the production API's narrower bytecode/counter imports.
  production = source (["Compilatrix"] ++ graph.targets.AiurReference.roots);
  dependencies = lib.fileset.toSource {
    inherit root;
    fileset = lib.fileset.unions common;
  };
}
