/-
  Ixon text format (`.ixon`): parser and canonical pretty-printer.

  The textual syntax denotes the *named Ix level* — a Lean-resembling
  closed grammar over `Ix.Expr`-shaped trees — never the pack-level
  tables (sharing/refs/univs are derived by the one canonical compile
  pipeline). The surface types, limits and positioned errors are in
  `Ix/IxonSyntax/AST.lean` and `Ix/IxonSyntax/Error.lean`; the parser and
  printer are in `Ix/IxonSyntax/Parser.lean` and `Ix/IxonSyntax/Print.lean`.
  `crates/ixon/src/syntax/` is the Rust twin this module mirrors behaviorally.

  This is the AST-level layer: text ↔ AST both ways, with structured
  errors and metered parsing. The `Constant` ↔ AST stages
  (resolve/ingress and the metadata-arena printer walk) build on top.
-/
module

public import Ix.IxonSyntax.AST
public import Ix.IxonSyntax.Error
public import Ix.IxonSyntax.Parser
public import Ix.IxonSyntax.Print
