# Mutual and nested inductive blocks, for constructor fields written erased

[`Blocks.lean`](Blocks.lean) holds, in namespace `ErasedBlocks`, programs whose recursor runs
through a block with more than one inductive. Such a recursor takes the minor premises of every
constructor of the block and has rules only for its own inductive's constructors:

| Root | What it runs | Meaning |
| --- | --- | --- |
| `mainB` | `B.rec` of `mutual A \| a0 \| a1 (h : True) (b : B); B \| b0 \| b1 (y : E)`, its minor for `b1` the η-short `useE` | `c₁` |
| `mainM2` | `A2.rec` of `mutual A2 \| a1 (b : B2); B2 \| b0 \| b1`, whose rule for `a1` calls `B2.rec` on the field | `c₂` |
| `mainN`, `mainN1` | `Tree.rec` and the auxiliary `Tree.rec_1` of `Tree \| leaf \| node (O Tree)`, nested through `O \| none \| some α` | `c₂` |
| `mainR` | `Rose.rec` of `Rose \| leaf \| node (L Rose)`, nested through `L \| nil \| cons α (L α)` | `c₁` |
| `r0`, `r1`, `r2` | the constructors of `E`, so that every one is emitted | |

No mode is written in the source. `tests-recheck` (`IxCCTests/Recheck/ErasedBlocks.lean`) writes a
constructor field erased below the kernel and checks that the relevance check refuses each
program by name (C3 with each minor paired with the rule that dispatches it; the forwarding
clause of `checkCanonical`), and that the honest `mainB` compiles to `c₁`.

`blocks.ixe` is the anonymous role-bound closure of the roots, `blocks.equations.json` its
`ixcc/k1-equations/1` sidecar (the roots, no equations), from `lake exe pin-src-tables
--erased-blocks fixtures/ixon-v4/erased-blocks` with the ix of this repository (`tools/regenerate.sh`
runs it); `blocks.provenance.json` records its version, the commands and the file hashes.
