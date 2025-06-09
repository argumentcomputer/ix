# Introduction

**Ix** is a Lean 4 library for constructing and verifying zero-knowledge proofs
of claims such as:

* The type correctness of Lean terms
* The reduction (evaluation) of Lean terms

These claims are encoded in a content-addressable format – **Ixon** – and processed
by the **IxVM**, a zero-knowledge virtual machine (zkVM) designed to handle such
structured data.

The **IxVM** is implemented in **Aiur**, a Turing-complete DSL for writing programs
that compile into constraint systems suitable for zero-knowledge proofs.

Aiur uses **Archon** for this compilation process, a customized frontend for the
[Binius](https://www.binius.xyz/) proving system.

This book introduces each of these components in dedicated chapters. It also covers
how we bridge Lean and Rust via FFI, and concludes with a guide on using the Ix
library to construct claims and build zero-knowledge applications.
