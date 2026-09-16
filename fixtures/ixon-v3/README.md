# Frozen ix frontend handoff

Unchanged files from `argumentcomputer/ix`, branch `jcb/aiur-frontend`, commit
`2afb4eac340cd4cbe94ed9e507561f3ad8375ebd`, directory
`Tests/Fixtures/ixon-v3/`. `README.md` and the copied license notices are
Compilatrix packaging additions. Do not regenerate expected bytes from the
consumer codec. The upstream handoff manifest records the original BLAKE3
file and subject/profile/claim hashes.

Run `lake exe tests-ixon-v3` from the repository root. See
[`docs/ixon-v3.md`](../../docs/ixon-v3.md) for admitted behavior, budgets,
the independent Aiur target pin, combined typing/resource admission, and
remaining backend obligations. The additional `typing/` bundles have their
own extraction provenance; they are not part of the original portable package.
The `catalog/` fixtures record producer assembly and an independently checked
chunk partition over those same primitive bytes.
