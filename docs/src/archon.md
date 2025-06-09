# Archon

Archon is a Rust module that serves as a frontend for the Binius proving system
and as a backend for Aiur. It works as a stable FFI bridge between Lean and Rust.
But stability is not the only motivation for Archon.

Aiur needs a way to construct circuits that are completely agnostic to the witness.
These circuits must be self-contained (sharing no columns or constraints) and
compiled into a unified constraint system. To support this, Archon introduces the
abstraction of a *circuit module*.

Each circuit module can be created independently, with its own oracles, constraints,
flushes, and exponentiation relations. Once a module is finalized, it can spawn a
corresponding *witness module*, which is then populated with witness data. Multiple  
witness modules can later be compiled into a unified witness structure for proof
generation.

Once the committed oracles of a witness module are filled in, Archon can compute
and populate the remaining derived oracles automatically, completing the witness
population process.

Both circuit and witness compilation rely on Binius core data structures, along
with a logic for offsetting oracles, treating all modules as if their columns
were laid out side by side in a single horizontal structure. Flushes, however,
use global channels, so their channel IDs remain unshifted and consistent across
modules.
