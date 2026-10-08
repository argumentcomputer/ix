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

The result is written to the job summary and, for pull requests, to a single
PR comment that is updated on each run.

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
so it only has to exist on the runner. The proving profile pins the `ix`
executable, so switching to an image with a different binary starts a new
baseline. The libraries' Lean version must match the image's.

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
