module

public import Ix.Kernel.Mode
public import Ix.Kernel.Id
public import Ix.Kernel.Level
public import Ix.Kernel.Expr
public import Ix.Kernel.Error
public import Ix.Kernel.Const
public import Ix.Kernel.Equiv
public import Ix.Kernel.Env
public import Ix.Kernel.Primitive
public import Ix.Kernel.Subst
public import Ix.Kernel.Lctx
public import Ix.Kernel.Monad
public import Ix.Kernel.Ingress
public import Ix.Kernel.IngressMeta
public import Ix.Kernel.Egress
public import Ix.Kernel.EgressLean
public import Ix.Kernel.Driver
public import Ix.Kernel.ParCheck
public import Ix.Kernel.Validate
public import Ix.Kernel.Whnf
public import Ix.Kernel.Infer
public import Ix.Kernel.DefEq
public import Ix.Kernel.Knot
public import Ix.Kernel.CanonicalCheck
public import Ix.Kernel.Inductive
public import Ix.Kernel.Check

/-!
# Ix.Kernel — pure-Lean Ix kernel over Ixon

A correctness-first, formalizable port of the Rust Ix kernel
(`crates/kernel`), operating over the Ixon content-addressed format with
separated anon and meta modes. Designed for correctness and formalization;
for performance, use the Rust kernel.

Module map (mirrors `crates/kernel/src/` file-for-file):

| Lean module       | Rust source    |
|-------------------|----------------|
| `Ix.Kernel.Mode`      | `mode.rs`      |
| `Ix.Kernel.Id`        | `id.rs`        |
| `Ix.Kernel.Error`     | `error.rs`     |
| `Ix.Kernel.Level`     | `level.rs`     |
| `Ix.Kernel.Expr`      | `expr.rs`      |
| `Ix.Kernel.Const`     | `constant.rs`  |
| `Ix.Kernel.Equiv`     | `equiv.rs`     |
| `Ix.Kernel.Env`       | `env.rs`       |
| `Ix.Kernel.Primitive` | `primitive.rs` |
| `Ix.Kernel.Subst`     | `subst.rs`     |
| `Ix.Kernel.Lctx`      | `lctx.rs`      |
| `Ix.Kernel.Monad`     | `tc.rs`        |
-/
