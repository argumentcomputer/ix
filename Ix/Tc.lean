module

public import Ix.Tc.Mode
public import Ix.Tc.Id
public import Ix.Tc.Level
public import Ix.Tc.Expr
public import Ix.Tc.Error
public import Ix.Tc.Const
public import Ix.Tc.Equiv
public import Ix.Tc.Env
public import Ix.Tc.Primitive
public import Ix.Tc.Subst
public import Ix.Tc.Lctx
public import Ix.Tc.Monad
public import Ix.Tc.Ingress
public import Ix.Tc.Driver
public import Ix.Tc.Whnf
public import Ix.Tc.Infer
public import Ix.Tc.DefEq
public import Ix.Tc.Knot
public import Ix.Tc.Check

/-!
# Ix.Tc — pure-Lean Ix kernel over Ixon

A correctness-first, formalizable port of the Rust Ix kernel
(`crates/kernel`), operating over the Ixon content-addressed format with
separated anon and meta modes. Designed for correctness and formalization;
for performance, use the Rust kernel.

Module map (mirrors `crates/kernel/src/` file-for-file):

| Lean module       | Rust source    |
|-------------------|----------------|
| `Ix.Tc.Mode`      | `mode.rs`      |
| `Ix.Tc.Id`        | `id.rs`        |
| `Ix.Tc.Error`     | `error.rs`     |
| `Ix.Tc.Level`     | `level.rs`     |
| `Ix.Tc.Expr`      | `expr.rs`      |
| `Ix.Tc.Const`     | `constant.rs`  |
| `Ix.Tc.Equiv`     | `equiv.rs`     |
| `Ix.Tc.Env`       | `env.rs`       |
| `Ix.Tc.Primitive` | `primitive.rs` |
| `Ix.Tc.Subst`     | `subst.rs`     |
| `Ix.Tc.Lctx`      | `lctx.rs`      |
| `Ix.Tc.Monad`     | `tc.rs`        |
-/
