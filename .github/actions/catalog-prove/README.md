# catalog-prove

Builds the caller's Lake libraries, exports them with `ix`, and proves the
result incrementally on a persistent self-hosted GPU runner. Each run uses
the last catalog proved for the same repository as its base, so only new or
changed declarations are proved.

```yaml
on: [push, pull_request]

jobs:
  proof:
    runs-on: [self-hosted, gpu-prover]
    timeout-minutes: 120
    permissions:
      contents: read
      pull-requests: write
    steps:
      - uses: actions/checkout@v7
        with:
          clean: false # keep .lake build outputs between runs
      - uses: argumentcomputer/ix/.github/actions/catalog-prove@cslib-demo
        with:
          libraries: Cslib
          image: ix-prover:<tag from build-image.sh>
```

The result is printed to the job log and summary and, for pull requests,
posted as a single PR comment that is updated on each run.

## Downloading proofs

Each run uploads its root proof, the serialized `Ixon.Proof` wrapper, to the
public bucket `argument-ix-certificates-063002298335-us-east-1-an` at
`<owner>/<repo>/<commit>/<root proof address>.ixon`, and prints `curl`
download instructions in the job log and summary. The file's BLAKE3 hash is
its address.

Upload credentials live on the runner, not in calling repositories: the
action mounts the runner user's `~/.aws/credentials` read-only into the
container, and skips the upload when that file does not exist.

## Prover image

Everything except the checkout runs in a local Docker image holding a CUDA
build of `ix` and the Lean toolchain it was built with. Build `ix` with the
host toolchain (not Nix, so it links against the same glibc as the image),
then package it:

```sh
IX_CUDA_TRACE_CODEGEN=1 MULTI_STARK_CUDA_ARCHS=120 CFLAGS=-std=gnu17 lake build ix
.github/actions/catalog-prove/build-image.sh .
```

The script prints the tag to pass as `image:`, `ix-prover:<sha256 prefix of
ix>`. The image is not pushed anywhere; the action runs it with `docker run`,
so it only has to exist on the runner. The libraries' Lean version must match
the image's.

The image enables generated device traces with trace-only lookups, and
`prove.sh` proves and verifies with `--structural-above 0`. The `ix`
executable and that threshold are part of the proving profile, and every run
uses the repository's `latest` catalog as its base, so after switching to an
image with a different binary or changing the threshold, proving fails with
"incompatible proving profile". To start a new baseline, move the runner
user's `~/.ix-prover/ix-catalogs/<owner>/<repo>/latest` link aside and delete
the failed commit's `<sha>.base` file there, which pins a retry to its
original base. A catalog
proved elsewhere can seed the runner's state only if it used the same binary,
threshold, and axiom policy.

## Runner requirements

- Docker with the NVIDIA Container Toolkit, and the runner user in the
  `docker` group. Docker access is equivalent to root on the host.
- Nothing else: Lean, `ix`, `jq`, and `gh` come from the image, which runs as
  the runner's own user.

## State

The runner user's `~/.ix-prover` is the container's home directory:

- `~/.ix-prover/.ix/` holds the proof store and caches. Do not prune it:
  retained catalogs reference proofs of any age.
- `~/.ix-prover/ix-catalogs/<owner>/<repo>/<sha>.ixc` holds one catalog per
  proved commit, and `latest` points at the most recent verified one.
- The caller's checkout, including `.lake`, stays in the runner's work
  directory.

## Axioms

The axiom policy comes from the libraries. A repository's first run allows
every axiom in its export; later runs inherit the base catalog's policy. If a
commit adds an axiom, proving fails and lists the new axiom addresses.
