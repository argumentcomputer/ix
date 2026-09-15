{
  pkgs,
  system,
  checks,
}: let
  groups = builtins.fromJSON (builtins.readFile ./ci-groups.json);
  platformOnly = ["native-sharing" "native-graph"];
  enabled = name: system == "x86_64-linux" || !(builtins.elem name platformOnly);
  required = pkgs.lib.concatLists (builtins.attrValues groups);
  assigned = builtins.filter enabled required;
  checkNames = builtins.attrNames checks;
in
  assert pkgs.lib.assertMsg
  (builtins.length required == builtins.length (pkgs.lib.unique required))
  "Every required CI check must be assigned exactly once";
  assert pkgs.lib.assertMsg (builtins.sort builtins.lessThan assigned == checkNames)
  "CI groups must cover the complete Nix check surface";
    pkgs.lib.mapAttrs' (name: names:
      pkgs.lib.nameValuePair "ci-${name}"
      (pkgs.linkFarm "compilatrix-ci-${name}"
        (map (check: {
          name = check;
          path = checks.${check};
        }) (builtins.filter enabled names))))
    groups
