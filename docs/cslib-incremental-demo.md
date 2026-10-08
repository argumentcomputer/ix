# CSLib incremental proving demo

This runbook shows `ix` certifying CSLib on every push to the
`argumentcomputer/cslib` `dev` branch, proving only the declarations each
commit adds or changes. Proving runs on the org self-hosted runner
`ix-gpu-prover` (label `gpu-prover`) through the
[`catalog-prove`](../.github/actions/catalog-prove/README.md) action, inside
the local image `ix-prover:7ef9884d53cdacea`.

The runner's prover state is `/srv/ghrunner/.ix-prover`: the proof store in
`.ix/` and one catalog per proved commit in
`ix-catalogs/argumentcomputer/cslib/<sha>.ixc`, with `latest` pointing at the
most recent verified one. It is seeded with a verified catalog of CSLib
v4.34.1 (commit `56d4962`, root proof `ce57d25a…`), which took 14:39 wall and
about 664 GiB peak host RAM to prove from scratch.

## Before the demo

- [ ] ix branch `cslib-demo` pushed with `.github/actions/catalog-prove`
      committed (the workflow uses `catalog-prove@cslib-demo`).
- [ ] cslib `dev` pushed. The first time, `dev` replaces the remote branch:
      `git -C /home/sam/repos/cslib-dev push --force-with-lease origin dev`.
      Hold this push for step 2 if you want to show the first run live.
- [ ] `ix-gpu-prover` shows Idle on the org Settings > Actions > Runners page.
- [ ] No other GPU job is running on the box (`nvidia-smi`).

## 1. Starting state

```sh
systemctl status actions.runner.argumentcomputer.ix-gpu-prover
docker image ls ix-prover
sudo ls -l /srv/ghrunner/.ix-prover/ix-catalogs/argumentcomputer/cslib/
```

Expect the service active, the image `ix-prover:7ef9884d53cdacea`, and the
catalog directory holding `56d4962….ixc` with `latest` pointing at it.

## 2. First push: reuse the seeded certificate

Push `dev` (see the checklist) and open the `ix proof` run under the
repository's Actions tab.

The `dev` commit has the same Lean content as the seeded baseline, so
nothing is proved. The job is dominated by fetching the Mathlib cache and
building Cslib from scratch in a fresh checkout; then export (about 40 s),
planning (about 1 min) and verification (about 30 s). In the job summary,
expect `Base: 56d4962….ixc`, root proof `ce57d25a…`, and in the proving
record `"reusedBaseRoot": true` and `"newSubjects": 0`.

## 3. Upstream change: incremental proof

Cherry-pick a real upstream commit from CSLib `main` onto `dev`: `17ff855`,
"feat(Automata): Two-way automata accept exactly the regular languages
(#888)". It changes only `Cslib.lean`, three files under
`Cslib/Computability/Automata/TwoWayNA/` and
`Cslib/Computability/Languages/RegularLanguage.lean` (+440/-10).

```sh
cd /home/sam/repos/cslib-dev
git fetch origin main
git cherry-pick 17ff855
# keep dev's Lean v4.34.1 pins if a picked commit changed them
git checkout HEAD~1 -- lean-toolchain lake-manifest.json lakefile.toml
git diff --cached --quiet || git commit --amend --no-edit
git push origin dev
```

`17ff855` leaves the pins alone, so the amend is skipped. Other `main`
commits written against v4.34-era APIs can be picked the same way. A commit
that needs a newer Lean or Mathlib fails to build: run
`git cherry-pick --abort` and pick another one.

The Lean build is incremental (`.lake` is kept between runs), so the job
takes a few minutes: export about 40 s, `ix catalog prove` about 2 min
including planning, verify about 30 s. This commit was proved on this box
before, against a different base, with 45 new subjects, 67 retained claims
and a 1:52 prove wall time. Expect similar numbers here; the earlier proofs
are not guaranteed to be reused. In the job summary point out:

- `Base:` is the previous commit's catalog.
- In the proving record, `newSubjects` counts the new or changed
  declarations and `retainedClaims` the claims reused unchanged from the
  base.
- `Root proof:` is the new root address, about 5.5 MB.
- The `curl` and `b3sum` download instructions.

## 4. Download and check the proof

Copy the two commands from the job summary. They have this form:

```sh
curl -fsSLO https://argument-ix-certificates-063002298335-us-east-1-an.s3.us-east-1.amazonaws.com/argumentcomputer/cslib/<commit>/<root>.ixon
b3sum --no-names <root>.ixon  # expect <root>
```

The printed hash equals the root proof address.

## 5. Optional: revert

```sh
cd /home/sam/repos/cslib-dev
git revert --no-edit HEAD && git push origin dev
```

The content now matches an already-certified catalog: expect
`"reusedBaseRoot": true`, `"newSubjects": 0`, and the earlier root proof
address, with no proving.

## 6. Optional: pull request

Push a branch with another small change and open a PR into `dev`. The run
posts the same summary as a PR comment, and later pushes to the PR update
that one comment instead of adding new ones.

## If something goes wrong

- Logs: the Actions job log, and on the box
  `journalctl -u actions.runner.argumentcomputer.ix-gpu-prover`.
- A job stuck in "Waiting for a runner" means the runner is offline or busy;
  only one job runs at a time.
- `Unable to find image` means the `image:` tag in
  `.github/workflows/ix-proof.yml` does not match a locally built image;
  `docker image ls ix-prover` lists what exists.
- A different `ix` binary (new image tag) or a different `--structural-above`
  changes the proving profile. Catalogs proved under the old profile cannot
  be a base, so while `latest` points at one, `ix catalog prove` fails with
  `incompatible proving profile`. To start a new baseline (a full proof,
  about 15 min), move `latest` aside as the runner user, together with the
  failed commit's `<sha>.base` file, which pins the base for retries:

  ```sh
  dir=/srv/ghrunner/.ix-prover/ix-catalogs/argumentcomputer/cslib
  sudo -u ghrunner mv "$dir/latest" "$dir/latest.old"
  sudo -u ghrunner rm -f "$dir/<sha>.base"
  ```
