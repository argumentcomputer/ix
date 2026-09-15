# Frozen certified adapter evidence

`c7-handoff.tar.gz` preserves the 53 original certified adapter source files,
their authenticated patches and source identities, and the historical
reports and regression corpora. Its SHA-256 and the source-to-local mappings
are recorded in [`ImportManifest.lean`](../../Certified/ImportManifest.lean).

Run `lake run check-certified` from the repository root. The gate checks the
archive and maintained host source identities, the exact declaration audit, six
native test programs and three command-line corpora. Generated source and
envelope bytes and process output must match the frozen evidence. JSON
requests and aggregate CLI records are compared as parsed values because the
maintained Lean driver uses different whitespace and object-key ordering.

The historical VM pilot and packet producer stay in the archive for a later
change. Host reports are compared after removing only the `pilotDeclined`
and `pilotDeclines` fields. All source/envelope fixtures and CLI outcomes
retain their original comparisons.

The archive's historical Python and shell drivers are provenance, not test
dependencies. Current tests use Lean. Execution requires the usual Linux
build tools, including `tar`, `sha256sum` and `timeout`.

The complete historical Ix base commit is not included. The preserved patch
sequence is sufficient to reconstruct the selected adapter files because
each first appears as a new file. The historical reproduction script still
requires its original base checkouts; current Ix validation is self-contained.
