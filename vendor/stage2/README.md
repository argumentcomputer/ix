# Stage2 source reference

This directory retains the 35 unchanged pure Lean modules imported by
`MultiStark.Verify.claimBytesWrapper`, with both upstream licenses. Exact file
digests and source provenance are recorded in [upstream.json](upstream.json).
The existing vendored Ixby Goldilocks and BLAKE3 modules are byte-identical to
the two external import boundaries of this source closure.

The source reference supplies reproducible valid and invalid proof tests and
the definition to which future compiler reflection must connect. A successful
native source test is not execution of an Ixby image, an Ixon erasure
certificate, or a source-to-image reflection theorem.
