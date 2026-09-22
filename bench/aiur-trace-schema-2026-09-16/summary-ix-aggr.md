## ix-aggr: 240 constrained functions

| Measure | Value |
| --- | ---: |
| Canonical seed bytes, summed over static functions | 53,232 |
| Typed seed bytes, summed | 38,592 |
| Typed / canonical, summed | 0.725 |
| Main row bytes, summed | 67,488 |
| Typed seed / main row, summed | 0.572 |
| Functions with typed <= 0.5 x canonical | 14 |
| Functions with typed <= 0.25 x canonical | 2 |
| Functions with typed <= 0.125 x canonical | 0 |
| Functions with no narrowing at all | 33 |
| Functions whose typed seed still exceeds half the row | 181 |
| Seed words: u8 / u16 / u32 / full | 1,355 / 1 / 1,486 / 3,812 of 6,654 |

Largest static savings, canonical minus typed bytes per row:

| Function | Words | Canonical | Typed | Row | u8/u16/u32/full |
| --- | ---: | ---: | ---: | ---: | --- |
| 86 `blake3_compress` | 162 | 1296 | 176 | 4264 | 160/0/0/2 |
| 117 `b3_rows_chunks` | 209 | 1672 | 608 | 1872 | 139/0/23/47 |
| 82 `blake3_compress_block` | 174 | 1392 | 408 | 1416 | 137/0/8/29 |
| 76 `blake3_next_layer` | 170 | 1360 | 432 | 1400 | 131/0/3/36 |
| 81 `blake3_finish` | 154 | 1232 | 424 | 1344 | 113/0/5/36 |
| 79 `bytes_to_block` | 194 | 1552 | 848 | 1560 | 64/0/64/66 |
| 111 `mmcs_compress` | 100 | 800 | 120 | 808 | 96/0/3/1 |
| 271 `aggr_load_sys` | 159 | 1272 | 784 | 1304 | 52/0/32/75 |
| 241 `aggr_read_address` | 99 | 792 | 440 | 800 | 32/0/33/34 |
| 232 `verify_shard` | 120 | 960 | 696 | 1192 | 15/1/40/64 |
| 77 `blake3_compress_layer` | 137 | 1096 | 840 | 1128 | 35/0/3/99 |
| 103 `read_sys_circuits_n` | 69 | 552 | 304 | 904 | 22/0/25/22 |
| 293 `ix_aggr` | 122 | 976 | 784 | 1080 | 11/0/30/81 |
| 290 `aggr_range_leaf` | 74 | 592 | 408 | 640 | 21/0/11/42 |
| 277 `aggr_parse_range` | 73 | 584 | 416 | 592 | 4/0/36/33 |

Widest typed seeds relative to the row (least to gain from generation):

| Function | Words | Canonical | Typed | Row | u8/u16/u32/full |
| --- | ---: | ---: | ---: | ---: | --- |
| 274 `aggr_wrap` | 44 | 352 | 352 | 360 | 0/0/0/44 |
| 243 `aggr_pack_address` | 34 | 272 | 272 | 280 | 0/0/1/33 |
| 289 `aggr_child_range` | 56 | 448 | 440 | 456 | 0/0/2/54 |
| 2 `address_eq` | 68 | 544 | 536 | 560 | 1/0/2/65 |
| 269 `aggr_assert_digest` | 17 | 136 | 136 | 144 | 0/0/0/17 |
| 288 `aggr_output_range` | 68 | 544 | 512 | 552 | 0/0/9/59 |
| 31 `read_count_at` | 12 | 96 | 96 | 104 | 1/0/0/11 |
| 93 `read_field` | 11 | 88 | 88 | 96 | 0/0/1/10 |
| 267 `aggr_claim_field` | 11 | 88 | 88 | 96 | 0/0/0/11 |
| 268 `aggr_claim_digest` | 11 | 88 | 88 | 96 | 0/0/0/11 |

