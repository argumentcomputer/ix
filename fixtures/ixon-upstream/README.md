# Pinned upstream executable closures

These five original anonymous Ixon v2 pieces were produced from
[`CompilatrixUpstream.lean`](CompilatrixUpstream.lean) by ix revision
`6f18ea907b78d06f7dc0917c43beb385561c35f4`, clean tree
`c09cfe3df1ee6ff92009672cc9077b4b7e2db63a`, using
`leanprover/lean4:v4.33.1`. The writer was built from a clean archive of that
revision with its locked Nix inputs. Each `pack` sets `MAIN` and includes the
complete dependency closure, with no assumption cuts. Compilatrix consumes
these bytes directly through `Catalog.load`.

| Entry | Constants | Piece bytes | Upstream kernel | Compilatrix outcome |
| --- | ---: | ---: | --- | --- |
| `applyClosed` | 6 | 662 | 5/5 accepted | Certified ELF, Nat 3 |
| `captureClosed` | 6 | 666 | 5/5 accepted | Certified ELF with a static Nat capture, Nat 2 |
| `letClosed` | 6 | 670 | 5/5 accepted | Certified ELF, Nat 4 |
| `addClosed` | 19 | 3072 | 16/16 accepted | Addressed IxIR₀; erasure validation lacks dependency `Covered` |
| `recClosed` | 6 | 796 | 5/5 accepted | Erasure validation lacks a `Covered` certificate |

Kernel counts are checked work constants; catalog counts also include block
and projection records. `catalog verify --deep` accepted all five catalogs.
A second empty project directory reproduced every piece and manifest byte.
The Lean module's BLAKE3 is
`f110212098135fe1087b898312c6736e673080a6de70b858424e4715b129a4bc`.
Complete roots, piece hashes, provenance, and stage observations are pinned in
[`../source-coverage/expected.json`](../source-coverage/expected.json).

The accepted examples exercise fresh higher-order arguments, a shared outer
capture, and a let-bound closure. They use explicit `Nat.zero`/`Nat.succ`
source terms. Literal ownership, unique captures, affine/linear callable
parameters, and unique callable results retain their separate restrictions.
The `Nat.add` and `Nat.rec` bodies are ordinary upstream definitions; their
later rejections are preserved as neighboring negative evidence.

To reproduce, copy the four project files in this directory into an empty
directory, enter the pinned ix development environment, and use the pinned
writer and Lean 4.33.1 `lake` on `PATH`:

```sh
ix compile CompilatrixUpstream.lean \
  --consts CompilatrixUpstream.applyClosed,CompilatrixUpstream.captureClosed,CompilatrixUpstream.letClosed,CompilatrixUpstream.addClosed,CompilatrixUpstream.recClosed \
  --out CompilatrixUpstream.ixe --report CompilatrixUpstream.report.json

for case in applyClosed captureClosed letClosed addClosed recClosed; do
  ix pack CompilatrixUpstream.ixe "CompilatrixUpstream.$case" \
    --anon --out "$case.ixe"
  ix catalog assemble "$case.ixc" "$case.ixe" \
    --labels "CompilatrixUpstream.$case" \
    --toolchains leanprover/lean4:v4.33.1 \
    --pins git:ix@6f18ea907b78d06f7dc0917c43beb385561c35f4
  ix catalog verify "$case.ixc" --deep
  ix check-rs "$case.ixe" --anon
  od -An -v -tx1 "$case.ixe" > "$case.ixe.hex"
  od -An -v -tx1 "$case.ixc/manifest" > "$case.manifest.hex"
done
```

Compare the ten generated hex files against this directory. The checked
coverage producer reads whitespace-insensitive hex with bounded file sizes;
it neither regenerates nor rewrites the source constants.
