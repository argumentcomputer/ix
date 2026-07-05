module

public import Ix.Tc.Mode
public import Ix.Tc.Id
public import Ix.Tc.Level
public import Ix.Tc.Expr
public import Ix.Tc.Error
public import Ix.Tc.Const

/-!
# Ix.Tc — pure-Lean Ix kernel over Ixon

A correctness-first, formalizable port of the Rust Ix kernel
(`crates/kernel`), operating over the Ixon content-addressed format with
separated anon and meta modes. Designed for correctness and formalization;
for performance, use the Rust kernel.

Module map (mirrors `crates/kernel/src/` file-for-file):

| Lean module      | Rust source   |
|------------------|---------------|
| `Ix.Tc.Mode`     | `mode.rs`     |
| `Ix.Tc.Id`       | `id.rs`       |
| `Ix.Tc.Error`    | `error.rs`    |
| `Ix.Tc.Level`    | `level.rs`    |
| `Ix.Tc.Expr`     | `expr.rs`     |
| `Ix.Tc.Const`    | `constant.rs` |
-/
