# Erased typing fixtures

These four anonymous bundles were extracted with the upstream `ix pack`
command from its v3 primitive environment. No consumer encoder generated
their expected object bytes. The three larger bundles passed the Rust
kernel's complete anonymous checks: 15, 278 and 4 declaration targets.

[`provenance.json`](provenance.json) records the extraction command, source
environment and executable digests, known primitive roots, and file hashes.
The producer executable and its primitive environment were rebuilt with Lake
from an unmodified workspace at the recorded source revision; this is not a
Nix build. The regenerated bundles are byte-identical to the previous
extraction, and the primitive inventory matches the committed handoff
inventory.

The required v3 suite checks complete byte admission for each bundle, then
adds positive Nat/String literals, a proof of `20 + 22 = 42`, and rejection
cases for incorrect literal typing, UTF-8, primitive profiles and arithmetic.
Upstream MIT/Apache licenses are retained in the parent directory.
