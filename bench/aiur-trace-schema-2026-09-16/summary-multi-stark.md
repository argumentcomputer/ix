## multi-stark: 223 constrained functions

| Measure | Value |
| --- | ---: |
| Canonical seed bytes, summed over static functions | 50,296 |
| Typed seed bytes, summed | 35,288 |
| Typed / canonical, summed | 0.702 |
| Main row bytes, summed | 64,128 |
| Typed seed / main row, summed | 0.550 |
| Functions with typed <= 0.5 x canonical | 14 |
| Functions with typed <= 0.25 x canonical | 2 |
| Functions with typed <= 0.125 x canonical | 0 |
| Functions with no narrowing at all | 32 |
| Functions whose typed seed still exceeds half the row | 165 |
| Seed words: u8 / u16 / u32 / full | 1,423 / 1 / 1,445 / 3,418 of 6,287 |

Largest static savings, canonical minus typed bytes per row:

| Function | Words | Canonical | Typed | Row | u8/u16/u32/full |
| --- | ---: | ---: | ---: | ---: | --- |
| 86 `blake3_compress` | 162 | 1296 | 176 | 4264 | 160/0/0/2 |
| 117 `b3_rows_chunks` | 209 | 1672 | 608 | 1872 | 139/0/23/47 |
| 82 `blake3_compress_block` | 174 | 1392 | 408 | 1416 | 137/0/8/29 |
| 76 `blake3_next_layer` | 170 | 1360 | 432 | 1400 | 131/0/3/36 |
| 274 `join_two` | 346 | 2768 | 1920 | 2776 | 66/0/98/182 |
| 275 `join_two_structural` | 345 | 2760 | 1912 | 2768 | 67/0/96/182 |
| 81 `blake3_finish` | 154 | 1232 | 424 | 1344 | 113/0/5/36 |
| 79 `bytes_to_block` | 194 | 1552 | 848 | 1560 | 64/0/64/66 |
| 111 `mmcs_compress` | 100 | 800 | 120 | 808 | 96/0/3/1 |
| 276 `verify_multi_stark_proof` | 221 | 1768 | 1160 | 1776 | 59/0/50/112 |
| 241 `join_read_address` | 99 | 792 | 440 | 800 | 32/0/33/34 |
| 232 `verify_shard` | 120 | 960 | 696 | 1192 | 15/1/40/64 |
| 77 `blake3_compress_layer` | 137 | 1096 | 840 | 1128 | 35/0/3/99 |
| 103 `read_sys_circuits_n` | 69 | 552 | 304 | 904 | 22/0/25/22 |
| 175 `ch_sample8` | 78 | 624 | 472 | 640 | 9/0/23/46 |

Widest typed seeds relative to the row (least to gain from generation):

| Function | Words | Canonical | Typed | Row | u8/u16/u32/full |
| --- | ---: | ---: | ---: | ---: | --- |
| 243 `join_pack_address` | 34 | 272 | 272 | 280 | 0/0/1/33 |
| 2 `address_eq` | 68 | 544 | 536 | 560 | 1/0/2/65 |
| 269 `join_assert_digest` | 17 | 136 | 136 | 144 | 0/0/0/17 |
| 31 `read_count_at` | 12 | 96 | 96 | 104 | 1/0/0/11 |
| 93 `read_field` | 11 | 88 | 88 | 96 | 0/0/1/10 |
| 267 `join_claim_field` | 11 | 88 | 88 | 96 | 0/0/0/11 |
| 268 `join_claim_digest` | 11 | 88 | 88 | 96 | 0/0/0/11 |
| 196 `logup_fingerprint` | 33 | 264 | 256 | 280 | 1/0/2/30 |
| 41 `read_digest_vec_at_n` | 43 | 344 | 336 | 368 | 0/0/3/40 |
| 194 `fold_roots` | 29 | 232 | 224 | 248 | 1/0/2/26 |

