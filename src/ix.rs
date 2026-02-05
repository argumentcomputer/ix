//! Ix: content-addressed representation of Lean kernel types.
//!
//! This module contains the Lean type representation (`env`), the Ixon
//! serialization format (`ixon`), and the compilation/decompilation pipeline
//! that transforms between them.

pub mod address;
pub mod compile;
pub mod condense;
pub mod decompile;
pub mod env;
pub mod graph;
pub mod ground;
pub mod ixon;
pub mod mutual;
pub mod store;
pub mod strong_ordering;
