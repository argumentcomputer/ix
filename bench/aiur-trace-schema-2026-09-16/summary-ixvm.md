## ixvm: 757 constrained functions

| Measure | Value |
| --- | ---: |
| Canonical seed bytes, summed over static functions | 129,600 |
| Typed seed bytes, summed | 98,248 |
| Typed / canonical, summed | 0.758 |
| Main row bytes, summed | 170,280 |
| Typed seed / main row, summed | 0.577 |
| Functions with typed <= 0.5 x canonical | 65 |
| Functions with typed <= 0.25 x canonical | 10 |
| Functions with typed <= 0.125 x canonical | 0 |
| Functions with no narrowing at all | 120 |
| Functions whose typed seed still exceeds half the row | 475 |
| Seed words: u8 / u16 / u32 / full | 2,524 / 1 / 4,127 / 9,548 of 16,200 |

Largest static savings, canonical minus typed bytes per row:

| Function | Words | Canonical | Typed | Row | u8/u16/u32/full |
| --- | ---: | ---: | ---: | ---: | --- |
| 33 `blake3_compress` | 162 | 1296 | 176 | 4264 | 160/0/0/2 |
| 29 `blake3_compress_block` | 174 | 1392 | 408 | 1416 | 137/0/8/29 |
| 23 `blake3_next_layer` | 170 | 1360 | 432 | 1400 | 131/0/3/36 |
| 28 `blake3_finish` | 154 | 1232 | 424 | 1344 | 113/0/5/36 |
| 26 `bytes_to_block` | 194 | 1552 | 848 | 1560 | 64/0/64/66 |
| 89 `get_address` | 99 | 792 | 440 | 800 | 32/0/33/34 |
| 131 `klimbs_mul_single` | 63 | 504 | 208 | 544 | 38/0/8/17 |
| 117 `klimbs_add_carry` | 44 | 352 | 80 | 392 | 35/0/7/2 |
| 24 `blake3_compress_layer` | 137 | 1096 | 840 | 1128 | 35/0/3/99 |
| 390 `prim_family` | 39 | 312 | 104 | 688 | 20/1/17/1 |
| 142 `klimbs_land` | 33 | 264 | 64 | 288 | 24/0/8/1 |
| 143 `klimbs_lor` | 33 | 264 | 64 | 288 | 26/0/5/2 |
| 144 `klimbs_xor_op` | 33 | 264 | 64 | 288 | 26/0/5/2 |
| 766 `check_muts_components` | 112 | 896 | 696 | 912 | 20/0/15/77 |
| 767 `run_reveal` | 104 | 832 | 632 | 904 | 19/0/18/67 |

Widest typed seeds relative to the row (least to gain from generation):

| Function | Words | Canonical | Typed | Row | u8/u16/u32/full |
| --- | ---: | ---: | ---: | ---: | --- |
| 732 `check_owned` | 34 | 272 | 272 | 280 | 1/0/0/33 |
| 2 `address_eq` | 68 | 544 | 536 | 560 | 1/0/2/65 |
| 758 `check_opt_addr` | 68 | 544 | 536 | 560 | 1/0/2/65 |
| 786 `list_lookup_u64.Constructor` | 89 | 712 | 696 | 728 | 2/0/2/85 |
| 277 `ctor_at` | 73 | 584 | 576 | 608 | 1/0/2/70 |
| 780 `list_length_u64.Constructor` | 54 | 432 | 424 | 448 | 1/0/2/51 |
| 42 `app_telescope_count` | 53 | 424 | 416 | 440 | 1/0/2/50 |
| 43 `lam_telescope_count` | 53 | 424 | 416 | 440 | 1/0/2/50 |
| 44 `all_telescope_count` | 53 | 424 | 416 | 440 | 1/0/2/50 |
| 21 `verify_bytes_against` | 71 | 568 | 544 | 576 | 0/0/6/65 |

