pub mod canonical_check;
pub mod check;
pub mod congruence;
pub mod constant;
pub mod def_eq;
pub mod egress;
pub mod env;
pub mod equiv;
pub mod error;
pub mod expr;
pub mod id;
pub mod inductive;
pub mod infer;
pub mod ingress;
pub mod level;
pub mod mode;
pub mod perf;
pub mod primitive;
pub mod subst;
pub mod tc;
pub mod whnf;

#[cfg(test)]
pub mod testing;
#[cfg(test)]
mod tutorial;
