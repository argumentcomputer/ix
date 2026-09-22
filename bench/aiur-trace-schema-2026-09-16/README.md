# Typed seed schema: static inventory

The trace planner now assigns every seed word a storage width, `u8`, `u16`,
`u32` or full, from a bounds analysis over the bytecode library. This
directory records what that schema does to seed sizes across all three
production programs, statically. **Static sites only:** the reports carry no
row weights, so nothing here is weighted by how often a function's rows
occur in a real proof. It ranks what generation could save per row, not
what it will save per proof.

Reproduce with a built `ix` CLI from this revision:

```sh
for t in ixvm multi-stark ix-aggr; do
  lake exe ix codegen --trace-report --target $t > report-$t.json
  python3 summarize.py report-$t.json functions-$t.json > summary-$t.md
done
```

`functions-<program>.json` holds the per-function rows (index, name, seed
words, canonical and typed bytes, main row bytes, words per width) that the
summaries are computed from. The full reports are 4 to 8 MB each and are
not checked in.

## Results

Typed against canonical seed bytes, summed over the constrained functions
of each program. "First" is the analysis with byte operations, constants,
exhaustive matches, assertions, continuation merges and callee bounds.
"Final" adds library-wide memory-table bounds and u32 pointer speculation.

| Program | Functions | Canonical bytes | Typed, first | Typed, final | Final / canonical | Final / main row |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| ixvm | 757 | 129,600 | 114,616 | 98,248 | 0.758 | 0.577 |
| multi-stark | 223 | 50,296 | 41,120 | 35,288 | 0.702 | 0.550 |
| ix-aggr | 240 | 53,232 | 44,552 | 38,592 | 0.725 | 0.572 |

| Program | No narrowing, first | No narrowing, final | Typed at most half of canonical, final | Words u8 / u16 / u32 / full, final |
| --- | ---: | ---: | ---: | --- |
| ixvm | 390 | 120 | 65 | 2,524 / 1 / 4,127 / 9,548 of 16,200 |
| multi-stark | 162 | 32 | 14 | 1,423 / 1 / 1,445 / 3,418 of 6,287 |
| ix-aggr | 172 | 33 | 14 | 1,355 / 1 / 1,486 / 3,812 of 6,654 |

The per-program summaries, with the fifteen functions that save the most
bytes per row and the ten whose typed seed is still nearly as wide as their
row, are in `summary-<program>.md`.

## What the numbers say

- **BLAKE3 is the outlier by far.** `blake3_compress` drops from 1,296 to
  176 bytes per row, 7.4x, against a 4,264-byte row. Its neighbours
  (`blake3_compress_block`, `blake3_next_layer`, `blake3_finish`) drop about
  3x. The klimbs arithmetic family (`klimbs_add_carry`, `klimbs_mul_single`,
  `klimbs_land`/`lor`/`xor_op`) drops 2.5x to 4.4x. No other function saves
  more than about a third.
- **Most functions move field elements, not bytes.** Even after memory-table
  and pointer bounds, 59% of IxVM seed words are full width: 3,822 of 5,779
  load results, 3,827 of 6,461 call results and 1,929 of 3,672 inputs. These
  are addresses, hashes and field values, and no analysis narrows a value
  that genuinely ranges over the field.
- **Memory-table bounds pay when a table is homogeneous.** Width-3 tables
  (a byte, a byte, a pointer, typically) narrow well; width-32 and width-47
  tables, whose slots mix bytes and field elements across store sites, stay
  wide in the slots where any store is wide.
- **The typed seed is still 55 to 58% of the main row.** For most functions
  generation would upload a seed about half as large as the row it replaces,
  and pay the host preparation pass on top. Whether that is a win depends
  entirely on row counts, which this inventory does not have.

## Reading this against the handoff order

Step 4 of the handoff ranks circuits by seed bytes and retained host
arithmetic, weighted by real rows from one merged program record. This
inventory supplies the static half of that ranking; the row weights still
require the cached FLT join. Until then the static ranking suggests the
first coverage expansion should be the BLAKE3 neighbours and the klimbs
family, which are the only functions whose typed seed is small relative to
their row.

## Generated BLAKE3 timing

`blake3-generated-timing.log` is the opt-in `blake3_generated_timing` test
on one 65,536-row tile, one RTX PRO 6000, after the handwritten provider was
removed. Both encodings are uploaded in the chunks the canonical stride
requires (six launches), so the launch count is equal.

| Case | Median |
| --- | ---: |
| Upload and generate, canonical seeds (1,296 bytes per row) | 9.59 ms |
| Upload and generate, typed seeds (176 bytes per row) | 2.89 ms |
| Materialize the same rows on the host, one thread | 110.3 ms |
| Generated seed preparation, one thread | 8.88 ms |

The retired handwritten kernel measured 2.30 ms upload in one launch and
7.45 to 7.84 ms preparation on this tile; the generated path measured 2.28
and 7.64 to 7.80 ms against it before removal.
