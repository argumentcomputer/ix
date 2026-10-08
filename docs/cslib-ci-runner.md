# CSLib proving runner

How the self-hosted GPU runner behind the
[`catalog-prove`](../.github/actions/catalog-prove/README.md) action is set
up, what state it depends on, and what was learned running it for
`argumentcomputer/cslib`. The demo itself is in
[cslib-incremental-demo.md](cslib-incremental-demo.md).

Runs: <https://github.com/argumentcomputer/cslib/actions/workflows/ix-proof.yml>

## Moving parts

| Piece | Where |
| --- | --- |
| Action (composite) | ix `cslib-demo`: `.github/actions/catalog-prove/` (`action.yml`, `run.sh`, `prove.sh`, `Axioms.lean`, `Dockerfile`, `build-image.sh`) |
| Caller workflow | cslib `dev`: `.github/workflows/ix-proof.yml` plus the "Certified by ix" README badge, one commit on top of upstream tag `v4.34.1` |
| Runner | org runner `ix-gpu-prover`, labels `self-hosted, Linux, X64, ix-gpu-prover`, runner group Default |
| Runner user | `ghrunner` (system user, home `/srv/ghrunner`, member of `docker`, no sudo) |
| Service | `actions.runner.argumentcomputer.ix-gpu-prover.service`, drop-in `…service.d/share.conf` |
| Prover image | `ix-prover:7ef9884d53cdacea` (local only, never pushed) |
| Prover state | `/srv/ghrunner/.ix-prover`: `.ix/store`, `.ix/cache`, `ix-catalogs/argumentcomputer/cslib/` |
| Upload credentials | `/srv/ghrunner/.aws/credentials`, mode 600 |
| Public proofs | `s3://argument-ix-certificates-063002298335-us-east-1-an/<owner>/<repo>/<commit>/<root>.ixon` |
| Seed baseline | CSLib v4.34.1 catalog A from `.lake/benches/cslib-dev-20261008/A.ixc` in this worktree |

## What has to survive

The proving profile pins the BLAKE3 hash of the `ix` executable, the
`--structural-above` threshold (0), the object format and the allowed
axioms. Every stored catalog and retained proof is only reusable by the exact
same binary bytes. In order of how expensive they are to lose:

1. **The `ix` binary.** sha256 prefix `7ef9884d53cdacea` (the image tag),
   BLAKE3 `385c1868…`, 383 MB, at `.lake/build/bin/ix` in this worktree and
   inside the image. It was built from `1a732d4a` (the last commit on
   `cslib-demo` outside `.github/` and `docs/`) for `sm_120`. A rebuild from
   the same commit is not guaranteed to be byte-identical, and a different
   binary means a new baseline: about 15 minutes and 664–696 GB peak RAM for
   CSLib. Keep the binary itself, or `docker save` the image.
2. **Prover state**, `/srv/ghrunner/.ix-prover`. It holds the store, the GPU
   lanes cache and one catalog per proved commit. It is seeded from about
   1.7 GB of store and cache plus the 1.6 GB `A.ixc`. Without it the next run
   is a baseline again.
3. **Bench data**, `.lake/benches/cslib-dev-20261008/` (9.9 GB, mostly
   regenerable `.ixe` exports): the A, S1–S4 and R1 catalogs, timings and GPU
   traces.
4. Everything else can be recreated by following the steps below: the runner
   registration, the image (given the binary) and the workspace `.lake`.

**Stopping the instance is safe.** All of the above is on the 500 GB EBS root
volume. Only the two instance-store NVMe disks are wiped by a stop, and
nothing uses them. Terminating the instance, or moving to another one, loses
everything unless it is copied off first. For example (use a private
location, not the public proof bucket):

```sh
docker save ix-prover:7ef9884d53cdacea | zstd -T0 > ix-prover-7ef9884d53cdacea.tar.zst
sudo tar -C /srv/ghrunner -I 'zstd -T0' -cf ix-prover-state.tar.zst .ix-prover
tar -C ~/repos/ix-l40s-proof-handoff/.lake/benches -I 'zstd -T0' \
  --exclude='*.ixe' -cf cslib-bench-20261008.tar.zst cslib-dev-20261008
```

Restore the state with `sudo tar -C /srv/ghrunner -xf … && sudo chown -R
ghrunner:ghrunner /srv/ghrunner/.ix-prover`, and the image with `zstd -dc … |
docker load`.

## Setting up a runner from scratch

The host needs an NVIDIA driver, Docker and the NVIDIA Container Toolkit.
Check them with `docker run --rm --gpus all nvidia/cuda:13.3.1-base-ubuntu26.04
nvidia-smi`. Everything else comes from the image.

1. **User.** Its home must be on persistent disk.

   ```sh
   sudo useradd --system --create-home --home-dir /srv/ghrunner --shell /bin/bash ghrunner
   sudo usermod -aG docker ghrunner   # docker access is root-equivalent
   ```

2. **Register the runner** with a token from the org's Settings → Actions →
   Runners → New runner (tokens expire after about an hour). Download and
   extract the runner tarball as that page shows, into
   `/srv/ghrunner/actions-runner`, as `ghrunner`, then:

   ```sh
   sudo -u ghrunner -H bash -c 'cd /srv/ghrunner/actions-runner && ./config.sh \
     --url https://github.com/argumentcomputer --token <token> \
     --name ix-gpu-prover --labels ix-gpu-prover --unattended'
   ```

   `--labels` adds to the default `self-hosted, Linux, X64`. Workflows must
   select `[self-hosted, ix-gpu-prover]`; a label no runner has leaves jobs
   queued with no error.

3. **Install it as a service.** `ghrunner` has no sudo, so run this from
   an admin account:

   ```sh
   sudo bash -c 'cd /srv/ghrunner/actions-runner && ./svc.sh install ghrunner && ./svc.sh start'
   ```

   The unit is named after the runner name passed to `config.sh`. The
   optional drop-in
   `/etc/systemd/system/actions.runner.argumentcomputer.ix-gpu-prover.service.d/share.conf`
   only affects the runner's own processes, not the prover (see the lessons
   below).

4. **Build the image.** Build `ix` with the host toolchain, not Nix, so it
   links against the image's glibc:

   ```sh
   IX_CUDA_TRACE_CODEGEN=1 MULTI_STARK_CUDA_ARCHS=120 CFLAGS=-std=gnu17 lake build ix
   sudo -u ghrunner .github/actions/catalog-prove/build-image.sh .   # or any docker-group user
   ```

   To reuse saved state, `docker load` the saved image instead, or copy the
   saved binary to `.lake/build/bin/ix` and run `build-image.sh`; the tag
   must come out as `7ef9884d53cdacea`.

5. **Upload credentials.** Write `/srv/ghrunner/.aws/credentials` (a
   `[default]` profile with `aws_access_key_id` and
   `aws_secret_access_key`), owned by `ghrunner`, mode 600. Without the file,
   the action skips the upload. Credentials stored as repository secrets do
   not work here: a composite action only sees its caller's secrets, and the
   caller (cslib) should not hold them.

6. **Seed the state** (optional; without it the first run is a baseline):
   either restore a saved `.ix-prover`, or copy a store and a catalog proved
   by the same binary:

   ```sh
   S=/srv/ghrunner/.ix-prover
   C=$S/ix-catalogs/argumentcomputer/cslib
   sudo install -d -o ghrunner -g ghrunner "$S" "$S/.ix" "$S/ix-catalogs" \
     "$S/ix-catalogs/argumentcomputer" "$C"
   sudo rsync -a --chown=ghrunner:ghrunner ~/.ix/store ~/.ix/cache "$S/.ix/"
   sudo rsync -a --chown=ghrunner:ghrunner <bench>/A.ixc/ "$C/<commit sha>.ixc/"
   sudo -u ghrunner ln -sfn "<commit sha>.ixc" "$C/latest"
   ```

   The catalog directory is named after the full commit SHA it was assembled
   from. `rsync --mkpath` leaves the directories it creates owned by root,
   which is why they are created first with `install -d`.

7. **Caller workflow.** See the action README.

## Lessons

- **Containers escape the service's cgroup.** `docker run` processes belong
  to the Docker daemon's cgroup, so systemd `MemoryMax`, `CPUWeight` and
  `IOWeight` on the runner service never reach the prover. Limits go on
  `docker run`. `run.sh` sets only `--memory=950g`, and `ix`'s memory
  budgeting reads that cgroup limit. CPU and IO are not weighted: the box is
  dedicated to proving while the runner is on.
- **elan installs toolchains lazily**, which fails for the image's non-root
  runtime user. The Dockerfile runs `elan toolchain install` explicitly.
- **The GPU needs `--gpus all` even to verify.** The CUDA build fails with
  CUDA error 35 without it.
- **Profile identity is the binary hash.** A new image (even a rebuild of the
  same commit) or a changed `--structural-above` fails with "incompatible
  proving profile" against an old `latest`. `<sha>.base` pins a commit's
  base so interrupted runs resume against the same plan; delete it together
  with moving `latest` aside to start a new baseline.
- **Identical content reuses the base root.** A commit whose export matches
  the base (the first push of `dev`, a revert) reports
  `"reusedBaseRoot": true`, `"newSubjects": 0`, and the earlier root, with
  no proving. Addresses ignore names, so a renamed but otherwise identical
  declaration also proves nothing new.
- **Timings on 4× RTX PRO 6000 (96 GB), 96 vCPU, about 1 TiB RAM:**
  - CSLib baseline: 14:39 wall, 664–696 GB peak.
  - Incremental commits: 1.5–2 min to prove. Cherry-picking upstream
    `17ff855` gave 45 new subjects, 67 retained claims, 1:52.
  - The first workflow run (seed reuse, fresh workspace) took 4:40, most of
    it fetching the Mathlib cache and building CSLib. Later runs keep `.lake`
    because the checkout uses `clean: false`.
  - A root proof is about 5.5 MB.
- **Settings that matter:** `AIUR_GPU_TRACE=generated`,
  `AIUR_TRACE_ONLY_LOOKUPS=1` and `AIUR_MAX_PIECE_LOG_HEIGHT=24`, set in the
  image. The GPU lanes cache must stay under `$HOME/.ix` so it persists.
- **Runner registration pitfalls:** `svc.sh install` has to run from an
  account with sudo, and the drop-in directory must match the unit name,
  which comes from the runner name.

## Verifying a downloaded proof

The `.ixon` file is an `Ixon.Proof`: its claim plus the STARK, and its BLAKE3
hash is its address. The CSLib root claims `CheckEnv(<corpus root>, none)`.
That claim is about the retained corpus and partition, so tying it to a
CSLib commit currently needs the runner's catalog (the coverage lines printed
by `verify-proof`).

`ix verify --aggregate` takes a store address, not a file, so place the file
in a throwaway store first. This needs a GPU and an `ix` with the same
verifying keys as the prover (the same binary is safest):

```sh
h=<root address>
home=$(mktemp -d)
dir=$home/.ix/store/${h:0:2}/${h:2:2}/${h:4:2}
mkdir -p "$dir" && cp "$h.ixon" "$dir/${h:6}"
HOME=$home ix verify --aggregate "$h"
```

## Open items

- `ix catalog gc`, to drop proofs no retained catalog references. It needs
  `proving.json` to record the join proof addresses. Until then the store
  only grows: about 1.7 GB, including leftovers from the S1–S3 bench runs.
- `ix verify` accepting a file path and printing the claim.
- A portable `Catalog` claim that binds the root to the export without the
  runner's corpus.
- A dedicated upload-only IAM user for the bucket, replacing the personal
  key on the runner. The unused `AWS_ACCESS_KEY` and `AWS_SECRET_KEY` secrets
  in the ix repository can be deleted.
- Reusing proofs across Lean versions:
  [cross-version-proof-reuse.md](cross-version-proof-reuse.md).
