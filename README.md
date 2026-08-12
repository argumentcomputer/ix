# Navigatr.ix

> Navigation machines, built by Ix to replace the Guild's Navigators.
> *Navigatrix* is the feminine agent noun of *navigator* — computers are
> feminine. Styled **Navigatr.ix**; repo name `navigatrix`.

An exploration of a certified compiler toolchain for
[ix](https://github.com/argumentcomputer/ix), aiming to replace the entire
Lean 4 reference implementation:

- **Frontend**: Lean 4 parsing, macro expansion, and elaboration in Rust,
  starting from [lean-rs](https://github.com/xiyuzhai/lean-rs).
- **Backend**: a certified compiler from Ixon (the ix object notation) down
  to machine code (RISC-V, x86-64), in the tradition of
  [CakeML](https://cakeml.org/) and [CompCert](https://compcert.org/).

The certification substrate is an open design question: proofs about the
Rust via [Aeneas](https://github.com/AeneasVerif/aeneas), proofs written in
Lean 4 itself, or a translation-validation hybrid. Design notes live in the
untracked `plans/` directory.

> :warning: **Pre-alpha exploration; nothing here should be used for any
> purpose.**

## License

Dual-licensed under Apache 2.0 and MIT, matching ix.
