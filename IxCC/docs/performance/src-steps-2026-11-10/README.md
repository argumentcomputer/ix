# SrcEval step counts on the committed fixtures

Recorded 2026-11-10 on this tree (the commit of the change that adds
`src-steps`), on a 64-core x86-64 Linux build host. The unit, a *charged step*
(one application of a rule that spends SrcEval's clock), and the other counts
are defined in [source steps](../../source-steps.md).

**Question.** How many SrcEval steps does each case of every committed corpus
family and benchmark fixture take, and how deep do the charged steps nest (the
least clock)? These are the reference numbers for any other implementation of
SrcEval's rules.

**Scope.** Every case of every root of the six registered `ixcc/corpus/1`
families (`bench-k1`, `phase1-scalar`, `phase1-boundary`, `phase1-resource`,
`phase1-decline`, `phase1-abi`) that the corpus suite runs at the source
level, through `ixcc`'s front end without erased typing (the corpus census
covers typing), at clock 2,000,000. Raw results, one `ixcc/src-steps/1` object
per line: [`steps.jsonl`](steps.jsonl). Every counted run agreed with `Src.run`
at its clock, at its least clock, and timed out one below.

**Replay.** From `IxCC/`, in the development shell:

```sh
lake build src-steps
.lake/build/bin/src-steps --manifests --no-typecheck > steps.jsonl
```

## By family

The front end declines nine roots, as their fixtures record: `typeFormerPolymorphism`
(relevance, C2), `Limits.fields255` and `Limits.tags126` (ingress decode limits),
and six roots of the decline family (admission). The 456 skipped cases are those
the corpus suite does not run at the source level: 447 with an argument of at
least `2⁶³`, 5 on which Lean's interpreter fails, and 4 with no source value.

| family | cases run | ok | timeout | stuck | trap | skipped cases | declined roots | charged steps, all runs | largest run |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| bench-k1 | 62 | 62 | 0 | 0 | 0 | 5 | 0 | 52156145 | 12500161 |
| phase1-abi | 243 | 243 | 0 | 0 | 0 | 135 | 0 | 34277 | 253 |
| phase1-boundary | 299 | 299 | 0 | 0 | 0 | 275 | 2 | 16673 | 1675 |
| phase1-decline | 20 | 20 | 0 | 0 | 0 | 0 | 6 | 6042 | 4669 |
| phase1-resource | 24 | 24 | 0 | 0 | 0 | 4 | 0 | 2781377 | 1310159 |
| phase1-scalar | 303 | 303 | 0 | 0 | 0 | 37 | 1 | 53698586 | 29280525 |

## The benchmark fixtures

Every case of `fixtures/ixon-v4/bench-k1` (the `entry` root of each program), in
manifest order. *Charged* is the step count; δ, β, ι, `case` and forcing are its
parts (`Quot.lift` is zero throughout); the least clock is the nesting depth of
charged steps; term nodes are calls of `eval`.

| fixture | args | result | charged | δ | β | ι | case | force | least clock | term nodes |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| fib | 13 | {"nat":233} | 25911 | 6398 | 16789 | 0 | 1362 | 1362 | 93 | 72745 |
| fib | 25 | {"nat":75025} | 8358359 | 2063670 | 5416285 | 0 | 439202 | 439202 | 177 | 23468313 |
| fib | 0 | {"nat":0} | 20 | 6 | 12 | 0 | 1 | 1 | 7 | 50 |
| fib | 15 | {"nat":610} | 67912 | 16768 | 44006 | 0 | 3569 | 3569 | 107 | 190674 |
| fib | 19 | {"nat":4181} | 465751 | 114994 | 301809 | 0 | 24474 | 24474 | 135 | 1307713 |
| fib | 15 | {"nat":610} | 67912 | 16768 | 44006 | 0 | 3569 | 3569 | 107 | 190674 |
| fib | 10 | {"nat":55} | 6081 | 1502 | 3939 | 0 | 320 | 320 | 72 | 17067 |
| sum-loop | 5000 | {"nat":12497500} | 625161 | 130040 | 425109 | 0 | 25004 | 45008 | 50018 | 1825522 |
| sum-loop | 100000 | {"nat":4999950000} | 12500161 | 2600040 | 8500109 | 0 | 500004 | 900008 | 1000018 | 36500522 |
| sum-loop | 0 | {"nat":0} | 161 | 40 | 109 | 0 | 4 | 8 | 18 | 522 |
| sum-loop | 11485 | {"nat":65946870} | 1435786 | 298650 | 976334 | 0 | 57429 | 103373 | 114868 | 4192547 |
| sum-loop | 18077 | {"nat":163379926} | 2259786 | 470042 | 1536654 | 0 | 90389 | 162701 | 180788 | 6598627 |
| sum-loop | 13629 | {"nat":92868006} | 1703786 | 354394 | 1158574 | 0 | 68149 | 122669 | 136308 | 4975107 |
| sum-loop | 14958 | {"nat":111863403} | 1869911 | 388948 | 1271539 | 0 | 74794 | 134630 | 149598 | 5460192 |
| ackermann | 3 3 | {"nat":61} | 85567 | 19229 | 58986 | 0 | 3676 | 3676 | 442 | 244480 |
| ackermann | 3 6 | {"nat":509} | 6107495 | 1375857 | 4214438 | 0 | 258600 | 258600 | 3578 | 17460814 |
| ackermann | 2 100 | {"nat":203} | 733651 | 165233 | 506202 | 0 | 31108 | 31108 | 1429 | 2097322 |
| ackermann | 1 1000 | {"nat":1002} | 71058 | 16013 | 49039 | 0 | 3003 | 3003 | 7015 | 203159 |
| ackermann | 0 9223372036854775806 | {"nat":9223372036854775807} | 36 | 9 | 25 | 0 | 1 | 1 | 8 | 99 |
| ackermann | 0 9223372036854775807 | {"nat":9223372036854775808} | 36 | 9 | 25 | 0 | 1 | 1 | 8 | 99 |
| ackermann | 1 3 | {"nat":5} | 271 | 61 | 186 | 0 | 12 | 12 | 36 | 768 |
| ackermann | 1 5 | {"nat":7} | 413 | 93 | 284 | 0 | 18 | 18 | 50 | 1174 |
| ackermann | 2 1 | {"nat":5} | 457 | 101 | 312 | 0 | 22 | 22 | 43 | 1294 |
| ackermann | 0 4 | {"nat":5} | 36 | 9 | 25 | 0 | 1 | 1 | 8 | 99 |
| tak | 12 12 8 4 | {"nat":5} | 140363 | 25125 | 90976 | 0 | 8665 | 15597 | 118 | 364755 |
| tak | 18 18 12 6 | {"nat":7} | 5152319 | 922327 | 3339466 | 0 | 318045 | 572481 | 172 | 13389653 |
| tak | 0 3 2 1 | {"nat":1} | 23 | 3 | 18 | 0 | 1 | 1 | 6 | 54 |
| tak | 4 3 3 6 | {"nat":6} | 71 | 11 | 46 | 0 | 5 | 9 | 19 | 169 |
| tak | 7 2 6 4 | {"nat":4} | 71 | 11 | 46 | 0 | 5 | 9 | 19 | 169 |
| tak | 8 4 8 3 | {"nat":3} | 71 | 11 | 46 | 0 | 5 | 9 | 19 | 169 |
| tak | 1 6 6 0 | {"nat":0} | 71 | 11 | 46 | 0 | 5 | 9 | 19 | 169 |
| gcd | 1071 462 | {"nat":21} | 177 | 41 | 112 | 0 | 8 | 16 | 21 | 468 |
| gcd | 4660046610375530309 2880067194370816120 | {"nat":1} | 4219 | 987 | 2692 | 0 | 180 | 360 | 365 | 11390 |
| gcd | 9223372036854775807 0 | {"nat":9223372036854775807} | 36 | 8 | 22 | 0 | 2 | 4 | 9 | 87 |
| gcd | 0 9223372036854775807 | {"nat":9223372036854775807} | 83 | 19 | 52 | 0 | 4 | 8 | 13 | 214 |
| gcd | 7134611160154358618 4654242949169100536 | {"nat":2} | 2057 | 481 | 1312 | 0 | 88 | 176 | 181 | 5548 |
| gcd | 4292726422858613063 1832488697174800709 | {"nat":1} | 1869 | 437 | 1192 | 0 | 80 | 160 | 165 | 5040 |
| gcd | 3467252261107883461 7020995479949754436 | {"nat":1} | 1587 | 371 | 1012 | 0 | 68 | 136 | 141 | 4278 |
| gcd | 8957066056171264801 204786321411665707 | {"nat":7} | 1634 | 382 | 1042 | 0 | 70 | 140 | 145 | 4405 |
| gcd | 7866638711627835880 1908141438795372387 | {"nat":1} | 1822 | 426 | 1162 | 0 | 78 | 156 | 161 | 4913 |
| gcd | 8309798722296661671 2521712920250132284 | {"nat":1} | 1775 | 415 | 1132 | 0 | 76 | 152 | 157 | 4786 |
| collatz | 30 | {"nat":423} | 88068 | 19755 | 56491 | 0 | 4524 | 7298 | 1285 | 240823 |
| collatz | 300 | {"nat":14151} | 2815122 | 634923 | 1803889 | 0 | 144504 | 231806 | 4059 | 7691875 |
| collatz | 77 | {"nat":2116} | 426947 | 96123 | 273668 | 0 | 21924 | 35232 | 1781 | 1166806 |
| collatz | 155 | {"nat":5839} | 1167421 | 263133 | 748150 | 0 | 59934 | 96204 | 2530 | 3190011 |
| collatz | 132 | {"nat":4788} | 958298 | 215979 | 614151 | 0 | 49194 | 78974 | 2395 | 2618652 |
| prime-count | 30 | {"nat":10} | 14217 | 2957 | 8894 | 29 | 852 | 1485 | 356 | 38162 |
| prime-count | 1000 | {"nat":168} | 1102570 | 234036 | 692718 | 999 | 65712 | 109105 | 10374 | 2947147 |
| prime-count | 279 | {"nat":59} | 221914 | 46774 | 139178 | 278 | 13295 | 22389 | 2979 | 593414 |
| prime-count | 432 | {"nat":83} | 381337 | 80572 | 239303 | 431 | 22811 | 38220 | 4571 | 1019519 |
| prime-count | 390 | {"nat":77} | 337219 | 71218 | 211595 | 389 | 20177 | 33840 | 4138 | 901607 |
| even-odd | 7 | {"nat":0} | 125 | 25 | 76 | 0 | 11 | 13 | 43 | 297 |
| even-odd | 100001 | {"nat":0} | 1100059 | 200013 | 700034 | 0 | 100005 | 100007 | 500013 | 2600141 |
| even-odd | 100000 | {"nat":1} | 1100048 | 200011 | 700027 | 0 | 100004 | 100006 | 500008 | 2600115 |
| even-odd | 4567 | {"nat":0} | 50285 | 9145 | 31996 | 0 | 4571 | 4573 | 22843 | 118857 |
| even-odd | 5009 | {"nat":0} | 55147 | 10029 | 35090 | 0 | 5013 | 5015 | 25053 | 130349 |
| even-odd | 1396 | {"nat":1} | 15404 | 2803 | 9799 | 0 | 1400 | 1402 | 6988 | 36411 |
| sfib | 10 | {"nat":258574} | 1120 | 254 | 724 | 0 | 51 | 91 | 101 | 3057 |
| sfib | 1000 | {"nat":258574} | 107050 | 24014 | 69034 | 0 | 5001 | 9001 | 9011 | 291642 |
| sfib | 604 | {"nat":258574} | 64678 | 14510 | 41710 | 0 | 3021 | 5437 | 5447 | 176208 |
| sfib | 1291 | {"nat":4} | 138166 | 30992 | 89098 | 0 | 6456 | 11620 | 11630 | 376404 |
| sfib | 2962 | {"nat":258574} | 316984 | 71102 | 204412 | 0 | 14811 | 26659 | 26669 | 863565 |
