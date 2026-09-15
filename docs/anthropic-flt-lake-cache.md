# Build and cache Anthropic's Fermat's Last Theorem library

This guide builds [anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem)
and uploads/downloads its Lean artifacts using Lake's built-in cache format.
Uploads go to your own storage account: use `lake cache put` for R2's S3 API or
the AWS CLI alternative for Amazon S3. Downloads use `lake cache get`.

## Versions and the existing checkout

The following versions were checked on 2026-09-15:

| Item | Value |
| --- | --- |
| Upstream branch | `main` |
| FLT commit | `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef` |
| Lean toolchain | `leanprover/lean4:v4.33.1` |
| Lake package | `flt_e2e` |
| Default library target | `FinalCheck` |
| Original Mathlib commit | `db584cd6d46c92f209a44c0f1c829460d327499d` |

See the pinned [package configuration](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/lakefile.lean)
and [dependency manifest](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/lake-manifest.json).

The existing checkout is:

```text
/home/sam/repos/ix/Benchmarks/Compile/.lake/packages/flt_e2e
```

Its commit matches upstream `main`. The neighboring `flt` directory is the
separate Imperial College London project.

The surrounding Ix benchmark workspace overrides Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). Building inside that
workspace therefore differs from building Anthropic's original dependency set.
The recipe below uses a separate working checkout and the original pins.

## Which cache command?

| Command | Purpose |
| --- | --- |
| `lake cache get` / `put` | Lake's general artifact cache; suitable for FLT and its dependencies. |
| `lake exe cache get` / `put` | Mathlib's own executable, with its own storage and authentication. |

Mathlib's executable does not cache the downstream FLT package. Furthermore,
the original Mathlib pin declares Lean **4.33.0**, while FLT builds it with Lean
**4.33.1**. Its ordinary public cache is not a substitute for that build.
Anthropic's instructions explicitly build this Mathlib revision from source.
See the [pinned Mathlib toolchain](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/lean-toolchain)
and [FLT build instructions](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/README.md#check-it-yourself).

### Which files does Mathlib publish?

Mathlib's `Cache.IO.mkBuildPaths` defines an explicit list for each module.
The list matches across current upstream (`dbc2b2ba8bdecf880fc07bf897333d139ae33843`),
FLT's original Mathlib pin, and Ix's override:

| Location relative to the package | Required files | Included when present |
| --- | --- | --- |
| `.lake/build/lib/lean/<module>` | `.trace`, `.olean`, `.olean.hash`, `.ilean`, `.ilean.hash` | `.olean.server`, `.olean.private`, `.ir.sig`, `.ir`, and each one's `.hash`; `.extra` |
| `.lake/build/ir/<module>` | `.c`, `.c.hash` | — |

For `Mathlib.Algebra.Group.Basic`, `<module>` means
`Mathlib/Algebra/Group/Basic`. `packCache` passes the existing listed files to
`leantar` to create one archive per module. It skips modules missing a required
file. This list excludes native `.o`, `.a`, and `.so` files, executables,
`.setup.json`, Lake configuration, source checkouts, and Git metadata.
[Current file selection and packer](https://github.com/leanprover-community/mathlib4/blob/dbc2b2ba8bdecf880fc07bf897333d139ae33843/Cache/IO.lean#L316),
[FLT's pinned version](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Cache/IO.lean#L256).

Module selection is separate from file selection. With no arguments, Mathlib's
`cache get` starts at `Mathlib.lean` and follows imports from its allowed module
namespaces. A module argument restricts the download to that module and its
transitive imports. FLT needs its own module selection, as provided by the Lake
build targets in this guide.
[Default root and download selection](https://github.com/leanprover-community/mathlib4/blob/dbc2b2ba8bdecf880fc07bf897333d139ae33843/Cache/Main.lean#L235),
[Import traversal](https://github.com/leanprover-community/mathlib4/blob/dbc2b2ba8bdecf880fc07bf897333d139ae33843/Cache/Hashing.lean#L40).

### Trace contents and public caches

`leantar` 0.1.20, bundled with Lean 4.33.1, rewrites the trace while packing:

- It discards the `inputs` field and log messages at level `trace`, including
  ordinary compiler command lines.
- It retains messages at levels `info`, `warning`, and `error`, plus output
  descriptors and the dependency hash. Diagnostics can therefore still expose
  paths or other build information.
- Lake's additional `-s` option removes the dependency hash from the archive;
  Lake supplies it again during extraction. It does not remove more log levels.

Thus, the original on-disk `.trace` is not an accurate preview of the uploaded
trace. A packing/extraction check using Ix's `Main.trace` removed its command
line and `/home/sam/...` paths in both Mathlib and Lake modes. A separate check
with all four log levels confirmed that informational messages and warnings
survive. These checks covered trace handling, not a complete artifact audit.
[Trace schema](https://github.com/digama0/leangz/blob/v0.1.20/src/ltar.rs#L251),
[Packing and log filtering](https://github.com/digama0/leangz/blob/v0.1.20/src/ltar.rs#L657).

The `build -o` workflow below produces Lake's own per-module archives with the
same main Lean artifacts. The formats are not identical: Lake stores hashes in
output descriptors instead of packing the separate `.hash` files, omits
Mathlib's optional `.extra`, and includes LLVM `.bc` when enabled. Both use the
same trace filtering in `leantar`. Keep publication scoped to the mappings;
do not upload the whole `.lake` directory. A public read endpoint with writes
restricted to trusted builders is appropriate for public library artifacts.
[Lake's archive contents](https://github.com/leanprover/lean4/blob/v4.33.1/src/lake/Lake/Build/Module.lean#L898),
[Mapping generation](https://github.com/leanprover/lean4/blob/v4.33.1/src/lake/Lake/Build/Module.lean#L1091).

## Resource requirements

This is a substantial build. Anthropic reports 5 h 32 min at 96 jobs, a peak
of 153 GB RAM, about 67 GB under `.lake/`, and roughly 220 GB of generated C.
Individual modules can need up to 36 GB RAM. The examples use two jobs; expect
a much longer build and allow additional disk space for the artifact cache.
These are upstream measurements, not estimates for this host.
[Upstream resource measurements](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/README.md#check-it-yourself).

Use Linux or macOS, Bash, Git, Elan, Python 3, and curl. Node.js/npm may also be
needed to build ProofWidgets' JavaScript assets. Building an `olean` facet still
emits Lean's companion artifacts, including C; keep them until cache publication
has finished.

## 1. Prepare a working checkout

Use a new destination. If it already exists, verify its revision and clean
working tree instead of repeating the clone commands. Keep research clones and
Ix's managed dependency checkout as source references.

```bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
export FLT_REV=aa2d8b34692b16c70f699536de0d8e75b9a3e9ef
export FLT_WORK="$HOME/repos/forks/fermats-last-theorem"
FLT_SOURCE="$HOME/repos/ix/Benchmarks/Compile/.lake/packages/flt_e2e"
mkdir -p "$HOME/repos/forks"

if test -d "$FLT_SOURCE/.git"; then
  git clone --no-hardlinks "$FLT_SOURCE" "$FLT_WORK"
  git -C "$FLT_WORK" remote set-url origin \
    https://github.com/anthropics/fermats-last-theorem.git
else
  git clone --no-checkout --depth 1 --single-branch --branch main \
    https://github.com/anthropics/fermats-last-theorem.git "$FLT_WORK"
  git -C "$FLT_WORK" fetch --no-tags --depth 1 origin "$FLT_REV"
fi

cd "$FLT_WORK"
git checkout --detach "$FLT_REV"
test "$(git rev-parse HEAD)" = "$FLT_REV"
test -z "$(git status --porcelain)"

export LEAN_NUM_THREADS=2
export LAKE_ARTIFACT_CACHE=true
export LAKE_RESTORE_ARTIFACTS=true
export MATHLIB_NO_CACHE_ON_UPDATE=1

lake +leanprover/lean4:v4.33.1 --version
lake +leanprover/lean4:v4.33.1 resolve-deps
mkdir -p .lake/cache
df -h "$FLT_WORK"
```

`resolve-deps` materializes the committed dependency manifest. Do not run
`lake update` for this recipe: it can change dependency pins or the toolchain.
The explicit toolchain argument below also ensures that commands targeting
Mathlib still use Lean 4.33.1.

### Reuse the same dependencies when changing the root package

Lake 4.33.1's `build -o` records outputs only for the root package. To publish
the dependencies as well, build each as a root with the same resolved source
directories. Generate path overrides without changing any tracked manifests:

```bash
python3 - <<'PY'
import json
from pathlib import Path

root = Path.cwd()
manifest = json.loads((root / "lake-manifest.json").read_text())
entries = []
for package in manifest["packages"]:
    directory = root / manifest["packagesDir"] / package["name"]
    entries.append({
        "name": package["name"],
        "scope": package.get("scope", ""),
        "type": "path",
        "dir": str(directory.resolve()),
        "inherited": False,
        "configFile": package["configFile"],
        "manifestFile": package["manifestFile"],
    })
overrides = {"version": manifest["version"], "packages": entries}
(root / ".lake/cache/overrides.json").write_text(json.dumps(overrides, indent=2))
PY

cat > .lake/cache/dependencies.txt <<'EOF'
Cli Cli
batteries Batteries
Qq Qq
aesop Aesop
proofwidgets ProofWidgets
importGraph ImportGraph
LeanSearchClient LeanSearchClient
plausible Plausible
mathlib Mathlib
EOF

flt_lake() {
  lake +leanprover/lean4:v4.33.1 \
    --packages="$FLT_WORK/.lake/cache/overrides.json" "$@"
}
```

The second column names a library target, avoiding unrelated default executable
targets. Absolute paths in `overrides.json` are machine-local; regenerate this
file on every checkout. The format is Lake's
[package override manifest](https://github.com/leanprover/lean4/blob/v4.33.1/src/lake/Lake/Load/Manifest.lean).

## 2. Configure the remote cache

The main example uses a Cloudflare R2 bucket, with its S3 API for authenticated
uploads and an HTTP endpoint for downloads. Replace `ACCOUNT_ID`, `BUCKET`, and
`cache.example.com` with your storage details. Both endpoints must address the
same bucket contents; `/a0` and `/r0` are object-key prefixes.
For Amazon S3, use the AWS CLI upload alternative in section 4B and its read
endpoint configuration.

Create `.lake/cache/services.toml`:

```toml
[[cache.service]]
name = "flt-write"
kind = "s3"
artifactEndpoint = "https://ACCOUNT_ID.r2.cloudflarestorage.com/BUCKET/a0"
revisionEndpoint = "https://ACCOUNT_ID.r2.cloudflarestorage.com/BUCKET/r0"

[[cache.service]]
name = "flt-read"
kind = "s3"
artifactEndpoint = "https://cache.example.com/a0"
revisionEndpoint = "https://cache.example.com/r0"
```

Then, in the same Bash session:

```bash
export LAKE_CONFIG="$FLT_WORK/.lake/cache/services.toml"
export FLT_CACHE_SCOPE="anthropic-flt/$FLT_REV/lean-4.33.1/x86_64-unknown-linux-gnu"
flt_lake cache services
```

Use the platform printed by `lean +leanprover/lean4:v4.33.1 --version` in place
of `x86_64-unknown-linux-gnu` on another platform. Publisher and downloader must
use the same scope and matching build inputs. Use a new scope for builds with
changed pins or options, including Ix's Mathlib override.

The explicit scope includes the toolchain even for dependencies such as Mathlib
that set `fixedToolchain := true`; Lake would otherwise omit the toolchain from
their automatic repository scope. [Mathlib's package settings](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/lakefile.lean#L50).

Lake 4.33.1 signs uploads with AWS SigV4 using region `auto`, which matches R2.
Downloads are ordinary HTTP requests, so the read endpoint must be accessible
without the upload secret. [Lake transfer implementation](https://github.com/leanprover/lean4/blob/v4.33.1/src/lake/Lake/Config/Cache.lean),
[R2 region](https://developers.cloudflare.com/r2/api/s3/api/#bucket-region),
[R2 public endpoints](https://developers.cloudflare.com/r2/buckets/public-buckets/).

No storage bucket is provisioned by these commands. A machine that only
downloads needs the `flt-read` service and no upload credentials.

## 3. Build `.ltar` archives and collect mappings — publisher only

Run this section when producing the cache. To consume an existing cache, skip
to section 5 after completing sections 1 and 2.

First build the dependency libraries and collect a separate mapping for each.
This covers all of Mathlib, including modules beyond FLT's import closure:

```bash
cd "$FLT_WORK"
while read -r package target; do
  flt_lake -d "$FLT_WORK/.lake/packages/$package" build "$target" \
    -o "$FLT_WORK/.lake/cache/$package.jsonl"
done < "$FLT_WORK/.lake/cache/dependencies.txt"

flt_lake build FinalCheck -o "$FLT_WORK/.lake/cache/flt_e2e.jsonl"
flt_lake --no-build build FinalCheck
```

The `-o` option makes Lake create a `.ltar` archive for each built module in the
root package and record its content hash in the `.jsonl` mapping. No separate
invocation of `leantar` is needed. The mapping and its archives must be published
together so another checkout can find the correct outputs.
[Archive generation for mappings](https://github.com/leanprover/lean4/blob/v4.33.1/src/lake/Lake/Build/Module.lean#L1091).

`FinalCheck` builds the theorem's import closure and checks its axioms. It is
the repository's default target. A successful fresh build reports the axioms
of `flt_mathlib` as `propext`, `Classical.choice`, and `Quot.sound`.
[FinalCheck source](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/FinalCheck.lean).

The final `--no-build` command checks freshness without permitting additional
compilation. The mappings include companion artifacts, not just `.olean`
files; preserve the local artifact cache until the uploads finish.
[Lake build/mapping behavior](https://github.com/leanprover/lean4/blob/v4.33.1/src/lake/Lake/CLI/Help.lean#L107).

### 3A. Collect the archives into an upload directory

This is optional for `lake cache put` and required for the AWS CLI alternative
below. Staging copies the selected archives, so allow disk space for another
copy of the compressed artifacts. Use a fresh directory to avoid including
files from a previous build:

```bash
FLT_STAGE=$(mktemp -d "$FLT_WORK/.lake/cache/staged.XXXXXX")
export FLT_STAGE

while read -r package target; do
  flt_lake -d "$FLT_WORK/.lake/packages/$package" cache stage \
    "$FLT_WORK/.lake/cache/$package.jsonl" "$FLT_STAGE/$package"
done < "$FLT_WORK/.lake/cache/dependencies.txt"

flt_lake cache stage "$FLT_WORK/.lake/cache/flt_e2e.jsonl" \
  "$FLT_STAGE/flt_e2e"
```

Each package directory contains `outputs.jsonl` and the corresponding
`<content-hash>.ltar` files. These are the upload inputs; the other contents of
the project and `.lake` are not staged.
[Staging implementation](https://github.com/leanprover/lean4/blob/v4.33.1/src/lake/Lake/CLI/Main.lean#L694).

## 4. Upload — publisher only

Choose section 4A for R2 or section 4B for Amazon S3.

### 4A. R2 through Lake's S3 uploader

Supply an R2 access-key ID and secret with write access to the bucket. The
following prompt avoids putting the credential in shell history:

```bash
read -r -s -p 'Cache credential (ACCESS_KEY_ID:SECRET_ACCESS_KEY): ' LAKE_CACHE_KEY
printf '\n'
export LAKE_CACHE_KEY

while read -r package target; do
  flt_lake -d "$FLT_WORK/.lake/packages/$package" cache put \
    "$FLT_WORK/.lake/cache/$package.jsonl" \
    --service=flt-write --scope="$FLT_CACHE_SCOPE/$package"
done < "$FLT_WORK/.lake/cache/dependencies.txt"

flt_lake cache put "$FLT_WORK/.lake/cache/flt_e2e.jsonl" \
  --service=flt-write --scope="$FLT_CACHE_SCOPE/flt_e2e"

unset LAKE_CACHE_KEY
```

Each upload sends the artifacts and then the mapping for that package's current
Git commit. Publish from unchanged source checkouts so those revision labels
describe the build. Dependencies and FLT have separate mappings and scopes.
[Upload implementation](https://github.com/leanprover/lean4/blob/v4.33.1/src/lake/Lake/CLI/Main.lean#L591).

### 4B. Amazon S3 through the AWS CLI

Use an existing bucket and AWS CLI credentials authorized to upload to it.
Lake 4.33.1's built-in uploader signs with region `auto`; the AWS CLI uses your
bucket's AWS region. Complete section 3A, then set:

```bash
export FLT_S3_BUCKET="argument-lake-cache-063002298335-us-east-1-an"
export FLT_S3_REGION="us-east-1"
```

Replace the region with the bucket's actual region. Set the `flt-read` service
in `.lake/cache/services.toml` to the bucket's public HTTP endpoint, or a public
CDN endpoint that serves the same object keys:

```toml
[[cache.service]]
name = "flt-read"
kind = "s3"
artifactEndpoint = "https://argument-lake-cache-063002298335-us-east-1-an.s3.us-east-1.amazonaws.com/a0"
revisionEndpoint = "https://argument-lake-cache-063002298335-us-east-1-an.s3.us-east-1.amazonaws.com/r0"
```

The endpoint must permit unauthenticated reads of the published objects; keep
write access restricted to your publisher. A private bucket behind a public
CloudFront distribution can also provide that read endpoint.
[S3 endpoint format](https://docs.aws.amazon.com/AmazonS3/latest/userguide/VirtualHosting.html),
[CloudFront access to a private S3 origin](https://docs.aws.amazon.com/AmazonCloudFront/latest/DeveloperGuide/private-content-restricting-access-to-s3.html).

Prepare Lake's object-key layout. Its remote artifact names end in `.art`, even
though the contents are `.ltar` archives. This script creates hard links within
the staging directory, so it does not duplicate archive contents again. It
requires a fresh `s3` subdirectory and rejects unexpected artifact types:

```bash
python3 - <<'PY'
import os
import re
import subprocess
from pathlib import Path

root = Path(os.environ["FLT_WORK"])
staged = Path(os.environ["FLT_STAGE"])
scope = os.environ["FLT_CACHE_SCOPE"]
upload = staged / "s3"
upload.mkdir()
packages = [line.split()[0] for line in
            (root / ".lake/cache/dependencies.txt").read_text().splitlines()
            if line.strip()]
packages.append("flt_e2e")

for package in packages:
    package_root = root if package == "flt_e2e" else root / ".lake/packages" / package
    revision = subprocess.check_output(
        ["git", "-C", str(package_root), "rev-parse", "HEAD"], text=True
    ).strip()
    artifacts = upload / "a0" / scope / package
    revisions = upload / "r0" / scope / package
    artifacts.mkdir(parents=True)
    revisions.mkdir(parents=True)
    count = 0
    for archive in (staged / package).iterdir():
        if archive.name == "outputs.jsonl":
            continue
        if not archive.is_file() or not re.fullmatch(r"[0-9a-f]{16}\.ltar", archive.name):
            raise SystemExit(f"Unexpected staged artifact: {archive}")
        os.link(archive, artifacts / (archive.stem + ".art"))
        count += 1
    if count == 0:
        raise SystemExit(f"No module archives staged for {package}")
    os.link(staged / package / "outputs.jsonl", revisions / (revision + ".jsonl"))
    print(f"{package}: {count} archives, revision {revision}")
PY

aws s3 cp "$FLT_STAGE/s3/a0/" "s3://$FLT_S3_BUCKET/a0/" \
  --recursive --region "$FLT_S3_REGION" \
  --content-type application/vnd.reservoir.artifact

aws s3 cp "$FLT_STAGE/s3/r0/" "s3://$FLT_S3_BUCKET/r0/" \
  --recursive --region "$FLT_S3_REGION" \
  --content-type application/vnd.reservoir.outputs+json-lines
```

Keep the `set -euo pipefail` setting from section 1. The first upload must
succeed before publishing the revision mappings. Do not change source revisions
between building, staging, and uploading. Section 5's `lake cache get` commands
then work with this S3 cache using the same scopes.
[Lake artifact and revision URLs](https://github.com/leanprover/lean4/blob/v4.33.1/src/lake/Lake/Config/Cache.lean),
[AWS CLI upload command](https://docs.aws.amazon.com/cli/latest/reference/s3/cp.html).

## 5. Download and restore — another machine or checkout

Complete sections 1 and 2 on the receiving machine, retaining the exact FLT
commit, manifest, Lean toolchain, platform, and scope. For Amazon S3, use the
`flt-read` endpoint configuration from section 4B. The dependency sources must
exist even when all compilation results are cached.

```bash
cd "$FLT_WORK"
while read -r package target; do
  flt_lake -d "$FLT_WORK/.lake/packages/$package" cache get \
    --service=flt-read --scope="$FLT_CACHE_SCOPE/$package" --rev=HEAD
done < "$FLT_WORK/.lake/cache/dependencies.txt"

flt_lake cache get \
  --service=flt-read --scope="$FLT_CACHE_SCOPE/flt_e2e" --rev=HEAD

flt_lake --no-build build FinalCheck
```

`get` downloads into Lake's shared local cache. The final command asks Lake to
restore/use matching outputs while refusing missing compilation work.
`LAKE_RESTORE_ARTIFACTS=true` keeps conventional build paths populated, such as
`.lake/build/lib/lean/FinalCheck.olean`.
[Module restoration](https://github.com/leanprover/lean4/blob/v4.33.1/src/lake/Lake/Build/Module.lean).

If the final command reports missing or stale targets, inspect the target name.
The artifact cache does not capture every custom target's side effects: for
example, ProofWidgets may still require its JavaScript files. To generate those
with Node.js/npm available:

```bash
flt_lake -d "$FLT_WORK/.lake/packages/proofwidgets" build widgetJsAll
flt_lake --no-build build FinalCheck
```

If Lean artifacts are still missing, running `flt_lake build FinalCheck` permits
compilation of the gaps using the two-job limit. This can be expensive; first
check the cache scope and dependency/toolchain matches. Cache reuse alone does
not repeat an independent kernel audit of imported artifacts.

## Useful checks and common mistakes

- **Exact revision:** `--rev=HEAD` avoids silently looking for an older mapping.
  Without it, Lake can search up to 100 revisions back.
- **Wrong root:** `lake build -o ...` in `Benchmarks/Compile` records that
  workspace's root outputs, not all FLT outputs. Use FLT as the root when
  producing its mapping.
- **Wrong selector:** Lake 4.33.1 has no `cache get --package=...`; the commands
  above select a root with `-d` instead. Run `lake cache help get` for the CLI
  supported by the installed toolchain.
- **Partial publication:** downloading only `flt_e2e` does not also download
  Mathlib. Keep the dependency loop when preparing a fresh machine.
- **Changed cache location:** `LAKE_ARTIFACT_CACHE=true` must be set during the
  publishing builds, and `put` must see the same local cache.
- **Different scopes on one machine:** this Lake version stores downloaded
  revision mappings by package/revision locally. If a stale mapping is reused
  after changing services or scopes, replace `--rev=HEAD` with
  `--max-revs=1 --force-download` for that retry. In 4.33.1, the explicit
  `--rev` path does not forward the force flag to the mapping lookup. This
  workaround also redownloads artifacts. [CLI lookup implementation](https://github.com/leanprover/lean4/blob/v4.33.1/src/lake/Lake/CLI/Main.lean#L496).

## Using FLT through Ix instead

For Ix's configured dependency set, use its existing benchmark driver:

```bash
cd "$HOME/repos/ix/Benchmarks/Compile"
LEAN_NUM_THREADS=2 lake build +CompileAnthropicFLT:olean
```

This uses Ix's Mathlib override and does not reproduce the standalone build
above. A cache populated from one configuration may miss in the other. Use a
separate scope and generate FLT's mappings with the benchmark workspace's
resolved dependency overrides if publishing that variant.

See [the benchmark configuration](../Benchmarks/Compile/lakefile.toml) and
[the compile guide](../Benchmarks/Compile/README.md).
