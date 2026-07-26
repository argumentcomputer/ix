/-
  Ixon text format (`.ixon`): parser and canonical pretty-printer.

  The textual syntax denotes the *named Ix level* — a Lean-resembling
  closed grammar over `Ix.Expr`-shaped trees — never the pack-level
  tables (sharing/refs/univs are derived by the one canonical compile
  pipeline). See `plans/ixon-syntax.md` for the design and
  requirements (R1–R8), and `crates/ixon/src/syntax/` for the Rust
  twin this module mirrors behaviorally.

  This is the AST-level layer: text ↔ AST both ways, with structured
  errors and metered parsing. The `Constant` ↔ AST stages
  (resolve/ingress and the metadata-arena printer walk) build on top.
-/
module

public import Ix.IxonSyntax.AST
public import Ix.IxonSyntax.Error
public import Ix.IxonSyntax.Parser
public import Ix.IxonSyntax.Print
