# Canonical sharing: integration map (workstream W4)

Integration inventory for plan gates P5–P6 of [`sharing-minimum.md`](sharing-minimum.md) and for
the PR checklist. Owner decisions in force (§12.8, §12.11–§12.13, §13 and the PR plan §0/§0b):

- the canonical sharing of a constant is `Ix.Sharing.Exact.canonicalSharingTiered .tagN` (Rust
  `canonical_sharing_tiered(ShareLayout::TagN, ..)`). Phase 1 keeps the best of three widths and
  phase 2 orders entries beyond the first tier by Kahn priority (W1/W2, inside the construction;
  neither changes its entry point or the routing of §3.2);
- TagN with flag widths 0, 2 and 4 replaces Tag0, Tag2 and Tag4 at every site of the grammar and
  is the only integer code: no dual-format gate, no old-format test infrastructure;
- backward references stay. The format version becomes 4 once, together with the object-format
  byte (4), the resource validator ID (`"ixon-v4/resource-v1"`) and `wireFormatId` (`"ixon-v4"`).
  The env header is TagN(4, `0xE`, version) with no special case (`0xE4`, read by context);
- the compiler route becomes the tiered construction only, and the heuristic sharing
  (`Ix/Sharing.lean`, `crates/ixon/src/sharing.rs`) and its proofs are removed. The default stays
  the heuristic until the route switch, which wires the compiler endpoint theorems to W1's
  `FormatOK` theorem (§4.3);
- compiler limits are a safety net: metering and fail-closed errors stay, the defaults sit far
  above every corpus maximum, there is a CLI override, and the production route counts work
  identically in Lean and Rust;
- metadata gets the extended index space of `sharing-minimum.md` §13 (W1 specifies the
  construction, W2 mirrors it; W4 owns the readers, §5.3);
- the IxVM circuit codec changes in the same PR, after the Lean and Rust codecs are stable.

**Status on branch `ix-sharing-w4`** (details in §8):

| Item | State |
|---|---|
| TagN at every Lean and Rust site; old encoders, decoders and canonical-integer checks deleted | done, `93e2895c` |
| The 4-byte rung (§12.16: widths 1, 2, 3, 4, 5, 9; codes `c = 0..3` select 2, 3, 4, 8 bytes) | done in the Lean and Rust codecs and pricing, `480923f2`; Rust `tiered.rs` `tagn_width` (W2) and `TagN.lean` proofs (W1) pending |
| Exact-sharing and heuristic pricing at TagN widths; TagN tie-break bytes; count threshold (finding 7) | done, `93e2895c` |
| Header subadditivity in the certain-excluded rule (finding 9): sound below `R5` nodes, proof needs the bound | pending (W1) |
| Tests on TagN only (`tiered-tag4` mode, Share-codec recode hooks and v3 vectors gone) | done, `93e2895c`, `15001658` |
| `ShareLayout.tag4` and the `ShareCodec` shims | pending: `Tiered.lean`/`tiered.rs` (W1/W2) |
| Codec proofs restated with `tagNBytes` | pending (W1); `IxCompileVerify` stops at `Codec.lean` (§4) |
| Single compiler route, limits, endpoint theorems wired to `FormatOK`, heuristic removed | pending (W4, after the codec proofs) |
| Version 4, format IDs, fixtures and pins regenerated | pending (W4, §6) |
| IxVM codec | pending (assigned separately) |
| Metadata extended index space, readers | pending (W4, after W1's construction) |

Marks below say which integer family an item concerns:

- **[Share]**: the Share integer (TagN `f = 4`, flag `0xB`);
- **[Tag4]**: every other 4-bit-flag integer;
- **[all]**: the 2- and 0-bit-flag integers (formerly `Tag2` and `Tag0`);
- **[-]**: independent of the integer code (construction, version, metadata, fixtures).

Line numbers in §1–§7 are those of commit `3ddda798` (the base of branch `ix-sharing-w4`) unless
a row says otherwise; Appendix A uses commit `01e05b00` (the same at `9c6384be`). Every entry was read in the source;
entries taken from a delegated sweep and not re-read are marked *(sweep)*.

## 1. Key findings

1. **TagN equals the old code exactly on its first rung.** `Tag4` values 0–7, `Tag2` values 0–31
   and `Tag0` values 0–127 are written identically in both codes; every larger value changes
   bytes. So every fixture with a count, index or size above those bounds changes (the handoff
   `.ixe` files certainly do), not only those with large Share indices.
1a. **"No integer gets longer" (§12.12) holds below the fifth rung end.** With the 4-byte rung of
   §12.16 (widths 1, 2, 3, 4, 5, 9), for values from `R5` (4,311,811,080 for `f = 4`,
   4,311,826,560 for `f = 0`) up to `2^56`, TagN takes 9 bytes where the old code took 6–8. Below
   `R5`, TagN is never longer (for `f = 0` it is one byte shorter on `[2^24, R4)` and
   `[2^32, R5)`).
1b. **The cost model prices the wire bytes.** `Ix/Sharing/Exact/Basic.lean` `tag0Size :=
   Ixon.tagNByteWidth 0` and `tag4Size := Ixon.tagNByteWidth 4` (hence `shareWidth`, `sizeInfo`,
   `exprSize`); Rust `sharing_exact/cost.rs` `tag0_len`/`tag4_len` are `TagN::byte_width`. The
   tie-break header bytes are TagN encodings in both languages (Lean `Dictionary.lean`
   `tag4Bytes` runs `putTagN 4`; Rust `tag4_bytes_cmp` compares `TagN::put` outputs). TagN is a
   prefix code, so distinct header values still differ inside the shorter encoding and the
   tie-break rule is unchanged. Lean's tiered self-check (`serExpr` bytes = price) passes on every
   fixture and generated input, and Lean and Rust agree byte for byte on them (§8).
2. **The plan's source map misses a third codec: the IxVM circuit.** `Ix/IxVM/IxonDeserialize.lean`
   reads every expression header with `get_tag4` (line 221) and maps `0xB => Expr.Share(size)`
   (294); `Ix/IxVM/IxonSerialize.lean:60` writes `put_tag4(0xB, idx, rest)`. The Rust file
   `crates/ixvm-codegen/src/aiur_ixvm.rs` is generated from these (`lake exe ix codegen`; CI runs
   `lake exe ix codegen --check`, `.github/workflows/ci.yml:45`). Until it is updated, the circuit
   misreads every constant with a header value past the first rung (it still reads Tag0/Tag2/Tag4).
3. **Metadata never references the primary table by index today.**
   `CallSiteEntry.collapsed.sharingIdx` and `callSite.origHead` index the per-constant
   `ConstantMeta.metaSharing` vector, arena roots follow the unshared logical tree, and every
   consumer expands `Share` transparently. Re-sharing a constant leaves its metadata valid (§5).
   The owner's extended index space (§13 of the plan doc) makes a metadata `Share(i)` with
   `i < p` (primary count) denote a primary entry and `i ≥ p` denote `metaSharing[i − p]`; both
   decompilers already resolve a metadata Share against the primary table, which is the `i < p`
   case (§5.3).
4. **The compiler endpoint theorems still consume heuristic facts.** All compiler endpoint
   theorems are stated against `Ix.CompileM.buildConstantWithSharing`, and
   `buildConstantWithSharing_wireWF` consumes `applySharing_wireWF` and `applySharing_capacity`.
   W1's `Ix.Compile.Verify.Tiered.canonicalSharingTiered_format` (`TieredWire.lean:185`; also
   `canonicalSharingTieredTable_format` :195 and `canonicalTiered_format` :164) gives `FormatOK
   sharing roots` for the tiered output: every entry and root `wireWF`, `sharing.size <
   UInt64.size`, entry `k` references only `Share(i)` with `i < k`, roots only `i < sharing.size`.
   The route switch rewires the endpoints to it (§4.3).
5. **Backwardness (`DecodeCtx.SharingWF`, `Ix/Compile/Verify/Catalog.lean:324`) is now available
   for the tiered output** through `FormatOK`'s last two conjuncts; no theorem establishes it for
   the heuristic.
6. **Version header aliasing (decided: keep).** The env header and the claim tags share flag `0xE`.
   Version 3 (`0xE3`) equals the Eval-claim tag and version 4 (`0xE4`) the Check-claim tag
   (`crates/ixon/src/proof.rs:216-217`). The owner keeps the context-dependent reading; the env
   header is TagN(4, `0xE`, version) with no special case. `docs/Ixon.md` states this next to the
   claim table.
7. **The uniform optimizer assumed the table count grows by at most one byte.** `uniformStage`
   (Lean `Uniform.lean`, Rust `uniform.rs`) used the certain-stored threshold θ = 2 because one
   more table entry grew the `Tag0` count by at most a byte. The TagN (`f = 0`) count grows by one
   byte at every rung end except the last: by 4 bytes at 4,311,826,560 entries (5 → 9). So θ = 2
   is sound for fewer candidates than that, which `maxNodes` ensures while it stays below `R5`
   (default 2^20), but not in general. On this branch θmax = `tag0StepBound n + 1` with `n` the candidate count
   (2 below 4,311,826,560, so nothing changes in practice), in both languages, and
   `tag0BracketStart` returns the TagN rung start. Proof impact: `UniformExchange.lean`
   `tag0Size_succ_le` (`tag0Size (n + 1) ≤ tag0Size n + 1`) is false at `n + 1 = R5` (used by
   `UniformGain.lean` and `UniformClasses.lean`), and `UniformOptimality.lean` `stage_cls_theta`
   and `UniformOptimal.lean` `GlobalWF.theta` state θ ∈ {1, 2}; they become θ ∈ {1, θmax}, or
   take a hypothesis `n < R5`.
8. **Claim tags past the first rung change.** Catalog and Resource claims (TagN `f = 4`, flag
   `0xE`, values 8 and 9) are written `E8 00` and `E8 01` (rung 2 stores `value − 8` in one byte;
   the old code wrote `E8 08` and `E8 09`). Their digests, `claims.tsv` and the in-circuit claim
   readers (`Ix/IxVM/Kernel/Claim.lean`, `Ix/Aggr/Circuit.lean`) change (§6).
9. **Telescope headers are no longer subadditive.** The uniform optimizer's certain-excluded
   rule (`Uniform.lean` module doc: "at a telescope continuation the merged header is
   subadditive") and its proof (`UniformClasses.lean` `tag4Size_add_le`, used by
   `PrepWF.unshare_spec`) assume `tag4Size (a + b) ≤ tag4Size a + tag4Size b` for `a, b ≥ 1`. The
   old code grew one byte per boundary, so it held. TagN (`f = 4`) grows by one byte at every rung
   end except the last, by 4 at `R5` = 4,311,811,080: `tag4Size (R5 − 1 + 1) = 9 > 5 + 1`. It holds
   whenever `a + b < R5`. A telescope's spine nodes are distinct terms, so while `maxNodes` stays
   below `R5` (default 2^20) no merged telescope reaches `R5` and the rule is sound; in general,
   unsharing a term into a telescope can cost up to 3 bytes more per merge than the rule
   accounts for. Not changed on this branch: the proof needs the bound as a hypothesis (or the
   rule a correction term) (W1/W2).

## 2. Where the plan and the code disagree

| Plan statement | Code |
|---|---|
| §8.3 "The expression byte grammar need not change." | True for the construction alone. False after §12.8: the Share grammar changes for indices ≥ 8 (TagN rung 2 starts at 8). |
| §8.2 "Metadata expressions may also contain Share references." | Neither compiler emits Share into `metaSharing` (Lean: `.share` is constructed only by `Ix/Sharing.lean:363` and `Ix/Resource/Addressed.lean:197`; Rust: `compile.rs` emits no Share outside `apply_sharing_*` *(sweep)*). The documented "extended sharing table" (`Ix/Ixon.lean` `ConstantMeta.metaSharing` doc; `crates/ixon/src/metadata.rs:237-250`) is not implemented by any reader (§5.3). |
| Plan §0 and task brief: `docs/Ixon.md` §"Versioning". | No such heading. The policy text is in "Environment Serialization", `docs/Ixon.md:867-888`. |
| §2 source map: Lean, Rust, FFI. | Also the IxVM circuit codec and its generated Rust (finding 2). |
| Task brief: "the 16 expected-bytes vectors" of `tagNUnits`. | `Tests/Ix/Ixon.lean` `tagNUnits` has 11 expected-encoding vectors, 9 rejection vectors and 3 rung-end vectors, plus boundary roundtrips and the short-string canonicity sweep. All of them are ported to Rust on this branch (`crates/ixon/src/tag.rs`). |
| §8.1 "Derive roots from ConstantInfo … do not use out-of-range fallbacks." | Lean `buildConstantWithSharing` (`Ix/CompileM.lean:2444-2470`) takes a separate root array and writes rewritten roots back with `getD` fallbacks. Rust `apply_sharing_to_*` derive roots from the payload. |

## 3. Call sites and consumers

### 3.1 Share codec: writers and readers

| Site | Today | Change | Scope |
|---|---|---|---|
| Lean `Ix/Ixon.lean:1209` `putExpr` Share arm | `putTag4 ⟨FLAG_SHARE, idx⟩` | `putTagN 4 FLAG_SHARE idx` | [Share] |
| Lean `Ix/Ixon.lean:1345-1347` `getExprFuel` | `getTag4 >>= getExprFromTag ..` | dispatch Share headers to `getTagN 4` (the high nibble is `0xB` in both codes) | [Share] |
| Lean `Ix/Ixon.lean:1339` `getExprFromTag` `0xB` arm | `.share tag.size` | unchanged (receives the decoded index) | [Share] |
| Lean `Ix/Ixon.lean:1167-1208` other `putExpr` headers, `getTag4` at 1347 | Tag4 | TagN headers | [Tag4] |
| Lean `putTag0`/`getTag0` in `putExpr` (ref/univ indices) and constant/metadata/env counts | Tag0 | TagN `f = 0` | [all] |
| Lean `Ixon.putUniv`/`getUniv` | Tag2 | TagN `f = 2` | [all] |
| Rust `crates/ixon/src/serialize.rs:368` `put_expr` Share arm | `Tag4::new(FLAG_SHARE, n).put` | `TagN::put(4, FLAG_SHARE, n)` | [Share] |
| Rust `serialize.rs:470,476` `get_expr` | `Tag4::get` then dispatch | Share header via `TagN::get(4, ..)` | [Share] |
| Rust `serialize.rs:708-722` `put_sharing`/`get_sharing`, and every `put`/`get` of `Definition`, `RecursorRule`, `Recursor`, `Axiom`, `Quotient`, `Constructor`, `Inductive`, `MutConst`, `ConstantInfo`, `Constant` (724-1076) | call `put_expr`/`get_expr` | follow the codec | [Share] |
| Metadata `metaSharing`: Lean `Ix/Ixon.lean:2196,2300`, Rust `metadata.rs:404-407,447-451` | `putExpr`/`getExpr` | follow the codec (no Share occurs there today) | [Share] |
| IxVM `Ix/IxVM/IxonDeserialize.lean:221,294`, `IxonSerialize.lean:60`; generated `crates/ixvm-codegen/src/aiur_ixvm.rs` | Tag4 | TagN Share; then `lake exe ix codegen` | [Share] |
| IxVM `get_tag4` (`IxonDeserialize.lean:92`) and `put_tag4` (`IxonSerialize.lean:102`) for every other header | Tag4 | TagN | [Tag4] |
| Tag4 outside expressions: constant headers `0xC`/`0xD` (`Ix/Ixon.lean:1596-1626`, `serialize.rs:1031,1039,1049`), Env header (`Ix/Ixon.lean:2854`, `serialize.rs:113`), claims, comm and assumption trees (`Ix/Claim.lean:531,560`, `Ix/AssumptionTree.lean:163,180`, `proof.rs:1010,1145`, `comm.rs:62`, `assumption_tree.rs:206` *(sweep)*), `LazyConstant` header peeks (`lazy.rs:276-310` *(sweep)*) | Tag4 | only if "every Tag4 integer" includes non-expression uses | [Tag4] |

Every Lean and Rust row of this table is done on this branch (`93e2895c`); the IxVM rows are not.
Each site calls `putTagN f`/`getTagN f` (Rust `TagN::put`/`TagN::get`/`TagN::byte_width`); the
old encoders, decoders and the three canonical-integer checks are deleted. Hand-rolled readers
and writers of the old code were replaced as well: Lean `Ixon.DeserCursor.tag0?`,
`Ix.DecompileM.BlobCursor.readTagN0` (was `readTag0`) and the CompileM syntax-blob writer
`Ix.CompileM.tagN0Bytes` (was `putTag0`); Rust `decompile.rs` `read_tagn0` and `metadata.rs`
`deser_tag0`. `LazyConstant` header peeks (`Ix/Ixon.lean`, `lazy.rs`) are unchanged: a non-Muts
constant header is a rung-1 TagN, the same byte as before.

The Rust `get_expr` at `serialize.rs:470` is the only byte-level expression decoder in Rust
*(sweep: `lazy.rs`, `catalog.rs`, `proof.rs`, `diff.rs` and `resource.rs` decode expressions only
through `get_expr` and skip constants by length prefix; a grep for `Tag4::get` confirms no other
expression-header decoder)*.

### 3.2 Sharing construction: callers that must route through the canonical construction

**Lean** (all pure; none can fail today):

| Site | Builds |
|---|---|
| `Ix/CompileM.lean:2444` `buildConstantWithSharing` (calls `Sharing.applySharing` at 2446) | every block |
| `Ix/CompileM.lean:3148` `buildCompiledMutualBlock`, standalone branch | collapsed one-class mutual block |
| `Ix/CompileM.lean:3153` `buildCompiledMutualBlock`, `.muts` branch | mutual block |
| `Ix/CompileM.lean:3233` `finishInductiveFamilyBlock` | standalone inductive family |
| `Ix/CompileM.lean:3247` `finishConstantWithSharing` (and `finishConstantInfoWithSharing` through it) | definition, theorem, opaque, axiom, quotient, recursor |
| `Ix/AuxGen/CompileAux.lean:216` | aux-gen standalone `defn`/`recr` |
| `Ix/AuxGen/CompileAux.lean:238` | aux-gen mutual block |

**Rust** (`crates/compile/src`):

| Site | Enclosing function; can it fail? |
|---|---|
| `compile.rs:2447` `apply_sharing_with_stats` → `analyze_block`/`decide_sharing`/`build_sharing_vec` | returns `SharingResult`; no |
| `compile.rs:2524, 2548, 2566, 2587, 2632` `apply_sharing_to_{definition,axiom,quotient,recursor}_with_stats`, `apply_sharing_to_mutual_block` | no |
| `compile.rs:3204/3212` `compile_mutual_block` | returns `CompiledMutualBlock`; no |
| `compile.rs:4163` | `compile_single_def`: `Result<_, CompileError>` |
| `compile.rs:4248, 4279, 4317` | `compile_const_inner`: `Result<_, CompileError>` |
| `compile.rs:4503, 4510, 4550` | `compile_mutual`: `Result<_, CompileError>` |
| `compile/mutual.rs:212, 219, 253` | `compile_aux_block_with_rename`: `Result<(), CompileError>` |
| `kernel_egress.rs:1057` | `egress_muts_block`: `Result<(), String>` |
| `kernel_egress.rs:1189, 1201, 1208, 1215` | `egress_standalone`: `Result<(), String>` |
| `decompile.rs:3137, 3145, 3159` | `roundtrip_block`: `Result<_, DecompileError>`. The recompiled address must equal `Named.original` (`decompile.rs:3390-3405`), so recompile must use exactly the compile route. |
| `decompile.rs:3353, 3361` | debug probe under `IX_ROUNDTRIP_DEBUG` |

`canonical_sharing_tiered` (`crates/ixon/src/sharing_exact/tiered.rs:515`) has no caller outside its
module; the FFI test hooks call `normalize_constant_bytes_tiered`
(`crates/ffi/src/lean_ixon/sharing.rs:224-244`).

**Status (route).** Every Lean site above and every Rust site goes through one switch per language
(`Ix.CompileM.compilerSharing`, Rust `COMPILER_SHARING`, commit `6100f9f2`): `heuristic` today, and
`tiered tagN` runs under explicit limits with roots derived from the payload, a checked
reassembly (`withRoots`) and propagated errors (`CompileError.resourceLimit`,
`CompileError.sharingConstruction`). Lean and Rust build the same bytes on both routes (153
unshared Constants × 2 routes in `exact-sharing-ffi`). What remains for the single route (§8):
flip the switch and delete it, set the limits of §0b-4, wire the endpoint theorems to
`FormatOK` (§4.3), then remove the heuristic.

### 3.3 Share consumers that are independent of the encoding

These expand `Share(i)` against `Constant.sharing` logically and need no change for any TagN scope:
Lean `Ix/DecompileM.lean:369-384, 388-394, 438-451`; `Ix/Tc/Ingress.lean:262-268`;
`Ix/Tc/IngressMeta.lean:354-370` (fuel-bounded cycle check); `Ix/SemanticContract.lean:161-172`;
`Ix/Resource/Addressed.lean:197` (offsets Share into a program-wide table); Rust
`crates/compile/src/decompile.rs:807-835, 861-874, 1103-1115`; `crates/kernel/src/ingress.rs:746-756,
1028-1037, 1048-1056`; `crates/compile/src/semantic_contract.rs:305-331`; `crates/ixon/src/resource.rs`,
`resource/addressed.rs:264-276`, `diff.rs:186-207`; FFI `crates/ffi/src/compile.rs:962-1001`,
`lean_env.rs:2759-2780` *(sweep for the last five)*. The IxVM `Ingress`/`Convert` modules also
consume the table logically.

### 3.4 Pricing and tie-break bytes in the construction

| Site | Change | State |
|---|---|---|
| `Ix/Sharing/Exact/Basic.lean:45` `shareWidth := tag4Size`, `:113` `sizeInfo`, `:117` `exprSize`; Rust `sharing_exact/cost.rs:69-81, 115-121` | Tag4 widths → TagN widths (`Ixon.tagNByteWidth`, `TagN::byte_width`) | done [Share] |
| `Basic.lean` `tag4Size` for every header and `tag0Size` for refs, univs and the table count; the uniform model (`Uniform.lean`, `uniform.rs`) | Tag4/Tag0 → TagN widths; `tag0BracketStart`/`tag0_bracket_start` at the TagN rung starts; the certain-stored threshold θmax (finding 7) | done [Tag4] [all] |
| `Ix/Sharing/Exact/Tiered.lean:316-318` measured length and the wire-layout check; Rust `tiered.rs:474-483` | measured with the wire codec, checked when the layout is the wire layout | done; the wire layout is `.tagN` through the `ShareCodec` shim, and `ShareLayout.tag4` remains to delete (W1/W2) [Share] |
| `Ix/Sharing/Exact/Dictionary.lean:264` Share option bytes `tag4Bytes FLAG_SHARE i` | none needed: a Share option only ties against inline or cut options, whose first byte has a flag nibble `0x0..0xA < 0xB`, so it loses every tie in either code; `tag4Bytes` now runs `putTagN 4` | follows the codec [Share] |
| `Dictionary.lean:254, 272, 276` cut/inline header bytes `tag4Bytes flag j`; Rust `dict.rs:171-181` `tag4_bytes_cmp` | TagN header bytes in both (two cuts with `j ≥ 8` can order differently than under Tag4) | done [Tag4] |
| Heuristic: `Ix/Sharing.lean:300` `shareRefSize`, `tag0EncodedSize`, `tag4EncodedSize`; Rust `crates/ixon/src/sharing.rs:367-368, 499-500` | TagN widths, identically in both languages | done; removed with the heuristic [Share] |
| Heuristic hash preimage of a node header: `Ix/Sharing.lean:58`, Rust `sharing.rs:45` | TagN header bytes in both | done; internal to the heuristic (the exact optimizer uses structural IDs) [Share] |

## 4. Verification theorems

All are in `IxCompileVerify` (`lakefile.lean:313-314`), which `lake lint -- --wfail` builds
(`.github/workflows/ci.yml:41`, driver `lakefile.lean:370-384`). No theorem in `Ix/Tc/Verify`
mentions these names, but `IxTcVerify` has `native_decide` serde fixtures
(`Ix/Tc/Verify/Ingress/SerializedBoolean.lean:42-81`, `Ingress/LiteralBlobs.lean`,
`Inductive/ConcreteFixture.lean`, `Inductive/EnumerationFixture.lean`) that recompute bytes with the
current codec.

### 4.1 Share wire bytes [Share]

The codec is TagN only on this branch, so every theorem below that names the deleted primitives
no longer elaborates. `lake build IxCompileVerify` stops at `Ix/Compile/Verify/Codec.lean` (first
error at line 160: unknown identifier `Ixon.getTag2`), and every module that imports it is
blocked. `lake build IxTcVerify` builds (644 jobs, sorry frontier OK). The tables say what each
theorem becomes; Appendix A lists every affected declaration.

| Theorem / def | What it says | Must become |
|---|---|---|
| `ExprCodec.lean:64` `wireEncode`, Share arm `:91` | `tag4Bytes FLAG_SHARE idx` | `TagN.tagNBytes 4 FLAG_SHARE idx` (`TagN.lean:68`); import `Ix.Compile.Verify.TagN` |
| `ExprSpineCodec.lean:198` `spineWireEncode`, Share arm `:239` | same | same |
| `ExprCodec.lean:111` `wireEncode_size_pos`, `ExprSpineCodec.lean:267` `spineWireEncode_size_pos` (Share cases) | from `tag4Bytes_size_pos` | from `TagN.tagNBytes_size` and `tagNByteWidth_pos` |
| `ExprCodec.lean:223` `putExpr_writes_single`, `ExprSpineCodec.lean:565` `putExpr_writes_spine` (Share cases) | `putTag4_writes FLAG_SHARE idx` | `TagN.putTagN_writes 4 FLAG_SHARE idx` (`TagN.lean:87`) |
| `ExprCodec.lean:298` `getExprFuel_reads_single`, `ExprSpineCodec.lean:942` `getExprFuel_reads_spine` | each of 12 cases builds `getTag4 >>= getExprFromTag ..` | with every header in TagN (§12.12), every case uses `TagN.getTagN_reads 4` (`TagN.lean:165`) for its header and `getTagN_reads 0` for its `Tag0` fields; no bridge lemma is needed |
| `SharingExact.lean:144` `shareWidth_eq_putTag4` | Share width = Tag4 length | restate against `putTagN 4`; `:242` `tagNWidth_eq_encoded` already proves the TagN form |
| `SharingExact.lean:385` `sizeInfo_spec` (`Spec (sizeInfoWith tag4Size e) e`) and its users `:500` `exprSize_eq_spineWireEncode`, `:505` `exprSize_eq_serExpr`, `:767` `exprsSize_eq`, `:808` `serConstant_size_decomposition` | Tag4 price = encoded length | TagN price; valid only once `sizeInfo` is repriced in `Basic.lean:113` |
| `UniformLength.lean:538` `optimizeUniform_variableBytes` (hypothesis `shareWidth i = w`, Tag4 at 569-582) | real length under Tag4 | follow the repriced `exprSize` |
| `UniformModel.lean:1137` `share_opts_filter`, `:1172` `PrepWF.inlineCost_eq`, `UniformLength.lean:235` `PrepWF.options_mem` | restate the `Prep.options` match verbatim, including `tag4Bytes FLAG_SHARE i` | edit in lockstep if `Dictionary.lean:264` changes (only the choice and cost matter to them) |

### 4.2 Header bytes of every expression [Tag4]

All 24 reader cases above, every `putTag4_writes` use in `ExprCodec.lean` and `ExprSpineCodec.lean`,
and the constant codecs (`ConstantCodec.lean`, `MutualConstantCodec.lean`, `RecursorConstantCodec.lean`,
`NonrecursiveConstantCodec.lean`, `ConstantTablesCodec.lean`), whose statements are proved from
`putTag4`/`getTag4` facts; the `SharingExact.lean` length lemmas over `tag4Size`; the uniform-model
length theorems. **[all]** adds every `putTag0`/`getTag0` fact (`Codec.lean`) and the universe codec.

### 4.3 Sharing construction [-]

| Theorem | Uses | Must become |
|---|---|---|
| `Sharing.lean:445` `applySharing_wireWF`, `:454` `applySharing_capacity` (audit root `Audit/Statements.lean:327`) | heuristic | kept for the regression path |
| `CompileSharingCodec.lean:304` `buildConstantWithSharing_wireWF` (audit root `Audit/Statements.lean:220`) | the only endpoint consuming heuristic facts | a tiered twin: rewritten roots and table are `wireWF` and `table.size < 2^64`. `SharingExactPasses.lean:559, 581, 606, 633, 668` (`materializeTable_backward`/`_correct`, `materializeDependent_*`) give backwardness, expansion correctness and the size bound, parametric in `widthAt`; `wireWF` of the output is missing |
| `CompileSharingCodec.lean:18, 30, 42, 54, 713, 729, 749, 797` (`*_eq_unshared`, `*_noSharing_*`) | hypothesis `applySharing #[..] = (#[..], #[])` | restated for the tiered route |
| `CompileSharingCodec.lean:555` `finishConstantWithSharing_run` (by `rfl`), `:571`, `:596`, `:614`; `CompileInductiveCodec.lean:593`; `CompileMutualCodec.lean:1114` | `run .. = .ok (BlockResult.mk' (buildConstantWithSharing ..) ..)` | the tiered builder is fallible, so after the flip these become "`run` = `.ok r` with `r` the tiered block, or a sharing error" |
| Downstream: `CompileAxiomCodec.lean:247, 333`, `CompileDefinitionCodec.lean:267, 322`, `CompileDefinitionDataCodec.lean:257, 314`, `CompileQuotientCodec.lean:179, 226`, `CompileRecursorCodec.lean:314, 370`; top-level endpoints in the same files and `CompileInductiveCodec.lean:1092, 1291`, `CompileMutualCodec.lean:1322, 1374, 1484, 3884` *(sweep)* | mention `buildConstantWithSharing` in statements or proofs | follow the above |
| `Catalog.lean:324` `DecodeCtx.SharingWF` | no theorem establishes it for compiler output | from `FormatOK`'s backwardness conjuncts (`TieredWire.lean:134`; route-switch wiring below) |

The audit manifest `Ix/Compile/Verify/Audit/Statements.lean` (`run_cmd Ix.Tc.Verify.Audit.check
roots`, line 405) requires every listed root to exist with its exact axiom set; the roots at lines
56, 58, 218, 220, 222, 227, 254, 283, 325, 327, 330, 333, 336, 339, 366 and 368 are affected by the
changes above *(sweep; 220, 325, 327, 366, 368 re-read)*. TagN roots are already present (350-357).

**Route-switch wiring.** `Ix.Compile.Verify.Tiered.canonicalSharingTiered_format`
(`TieredWire.lean:185`) and `canonicalSharingTieredTable_format` (:195) give `FormatOK sharing
roots` (:134) for any successful tiered construction. At the switch, `buildConstantWithSharing_wireWF`
and the endpoints downstream of it in `CompileSharingCodec.lean` take their table facts from
`FormatOK` (`wireWF` of entries and roots, `sharing.size < UInt64.size`) instead of
`applySharing_wireWF`/`applySharing_capacity`, and the run lemmas become "`run` = `.ok r` with the
tiered block, or a sharing error". `FormatOK`'s backwardness conjuncts discharge
`DecodeCtx.SharingWF`.

### 4.4 Codec theorems over Tag0/Tag2/Tag4 bytes and sizes [Share] [Tag4] [all]

§12.12: every codec theorem that mentions the old byte or size functions is restated with
`tagNBytes`. The TagN facts are already proved in `Ix/Compile/Verify/TagN.lean` (W1); cite them,
do not reprove:

| Old fact | New fact (`Ix.Compile.Verify.TagN`) |
|---|---|
| byte specs `tag0Bytes`, `tag2Bytes`, `tag4Bytes` (`Codec.lean`) | `tagNBytes 0`, `tagNBytes 2`, `tagNBytes 4` (:68) |
| `putTag0_writes`, `putTag2_writes(_small)`, `putTag4_writes` | `putTagN_writes f flag value` (:87); `runPut_putTagN` (:106) |
| `getTag0_reads(_small/_large)`, `getTag2_reads(_small/_large)`, `getTag4_reads(_small/_large)` | `getTagN_reads f hf flag hflag value` (:165); `runGetExact_getTagN_putTagN` (:245) |
| `tag0_small_fields`, `tag2_small_fields`, `tag4_small_fields` and the canonical-integer reasoning inside `getTag*_reads_large` | none needed: TagN is bijective (`tagNHeader_fields` :140, `runGetExact_getTagN_eq`/`_iff`/`_inj` :486/:508/:521, `putTagN_inj` :529) |
| `tag0Bytes_size_pos`, `tag2Bytes_size_pos`, `tag4Bytes_size_pos`, `tag0ListBytes_size_ge_length` | `tagNBytes_size` (:116) with `tagNByteWidth_pos` (:60) |
| cost-model facts proved by unfolding the old `tag0Size`, `tag4Size` (`if n < 128 …`, `natByteCount`), e.g. `tag4Size_add_le`, `tag0Size_mono`, `tag4Size_mono`, `tag4Size_pos` | the cost model is now `Ixon.tagNByteWidth 0`/`4` (`Basic.lean`); use `tagNByteWidth_mono` (:53), `tagNByteWidth_pos` (:60), `runPut_putTagN_size` (:123); `tag4Size_add_le` (subadditivity) is false under TagN (finding 9) |
| `tag0Size_succ_le` (`UniformExchange.lean`), false under TagN | `tag0Size (n + 1) ≤ tag0Size n + tag0StepBound (n + 1)` (new; finding 7), and θ ∈ {1, θmax} in `stage_cls_theta` / `GlobalWF.theta` |
| (no old counterpart) | rejection laws `getTagN_rejects_code` (:544), `getTagN_rejects_overflow` (:564) |
Appendix A lists every theorem and definition of `Ix/Compile/Verify` that mentions `tag0Bytes`,
`tag2Bytes`, `tag4Bytes`, `tag0Size`, `tag4Size`, `tag0ListBytes`, `shareWidth`, the `*EncodedSize`
helpers, `putTag*_writes`, `getTag*_reads`, `putTag*_size`, `tag*_small_fields`, the deleted
primitives `Ixon.putTag0/2/4`, `Ixon.getTag0/2/4`, `Ixon.Tag0/2/4`, `getTag0Sizes`, `putTag0List`,
the renamed `Ix.CompileM.putTag0`, or `tag0Size_succ_le`. At commit `01e05b00` there are 243
entries in 28 modules (90 S, 93 P, 60 D); no module of `Ix/Tc/Verify` mentions them. Each entry is
classified:

- **D** (a definition: a byte spec such as `wireEncode`, or a cost-model function): redefine with
  `tagNBytes` / `tagNByteWidth`;
- **S** (the statement mentions them): restate with the TagN counterparts and re-prove from the
  table above;
- **P** (only the proof mentions them): the statement stays; replace the old lemmas in the proof.

The list was extracted mechanically (a declaration's statement is the text before its `:=`), so a
classification can be off where a statement spans an unusual layout; the set of names is complete
for those patterns. `CompileMeta.lean` and `CompileMetaStore.lean` only name
`Ix.CompileM.putTag0` as an opaque function (now `tagN0Bytes`); `TieredModel.lean:573` restates
`Dictionary.lean`'s inline option bytes, now `putTagN 4 flag field`. Every module of
Appendix A imports `Codec` directly or transitively, so none of them builds before `Codec` does;
the ones with entries are `Codec`, `ExprCodec`, `ExprSpineCodec`, `ConstantCodec`,
`ConstantTablesCodec`, `NonrecursiveConstantCodec`, `RecursorConstantCodec`,
`MutualConstantCodec`, `SharingExact`, `SharingExactPasses`, the `Uniform*` modules,
`TieredModel`, `TieredPhase3`, `TieredGuard`, and `CompileMeta`/`CompileMetaStore` (a rename of
`Ix.CompileM.putTag0` to `Ix.CompileM.tagN0Bytes` only).

## 5. Metadata audit (§8.2)

### 5.1 Index spaces

- **Separate namespaces, confirmed.** `CallSiteEntry.collapsed sharingIdx` indexes
  `ConstantMeta.metaSharing` (Lean doc `Ix/Ixon.lean:630-638`; Rust `metadata.rs:37`). Both
  compilers start it at 0 per constant. Lean `buildCallSite` uses `surgerySharing.size` as the base
  (`Ix/CompileM.lean:1373-1398`) and the vector is drained into `metaSharing` per constant
  (`takeSurgerySharing`, `Ix/CompileM.lean:370-372`; stored at 2547, 2628, 2668, 2744, 2782, 2860,
  2923). Rust `compile.rs:2011-2051` (`sharing_base + collapsed_idx`) drains it at 2822/2853,
  2913/2950, 2980/3008, 3041/3088, 3114/3134, 3160/3179 *(sweep)*. `callSite.origHead.0` also
  indexes `metaSharing`.
- **Readers keep them apart.** Lean decompile resolves Collapsed and `origHead` through
  `ctx.metaSharing` (`Ix/DecompileM.lean:474, 510, 541`) and Share through `ctx.sharing =
  cnst.sharing` (749). Rust decompile does the same (`decompile.rs:1184-1195, 1237-1247, 1324-1341`
  vs 861-874; test `test_callsite_collapsed_reads_meta_sharing_not_sharing` *(sweep)*). Kernel
  ingress ignores `meta_sharing` (`crates/kernel/src/ingress.rs:1016-1021`; Lean
  `Ix/Tc/IngressMeta.lean:48`).
- Collapsed indices must **not** be offset by the primary table length: nothing reads them that way.

### 5.2 Do metadata payloads contain primary Share references?

No, in either compiler. `metaSharing` entries are raw compiled expressions: Lean
`compileExprSurgical` output (`Ix/CompileM.lean:1373-1382`), Rust `compile_expr` output pushed at
`compile.rs:2011-2015`. Share is produced only by the sharing pass, which runs on the roots after
metadata is built. Their Ref/univ indices point into the primary `refs`/`univs` block tables, which
the construction does not change. **No remapping is needed when the primary table changes.**

### 5.3 Metadata Share: the extended index space (decided, not implemented)

`ConstantMeta.metaSharing` was documented as possibly containing `Share(idx)` "into the extended
sharing table" (`Ix/Ixon.lean` `ConstantMeta` doc; `metadata.rs:237-250`), but no reader
implemented an extended table: both decompilers resolve a metadata Share against the **primary**
table (Lean `decompileExpr shared ..` runs under `ctx.sharing = cnst.sharing`; Rust
`Frame::Decompile`, `decompile.rs:861-874`), and neither compiler emits one.

The owner's rule (`sharing-minimum.md` §13.1): with `p` primary entries and `q` metadata entries, a
`Share(i)` inside a `metaSharing` expression denotes primary entry `i` when `i < p`,
`metaSharing[i − p]` when `p ≤ i < p + q` (entry `j` may reference only `i < p + j`), and is a
decode error otherwise; primary bytes never depend on metadata, and `CallSiteEntry.collapsed
sharingIdx` / `origHead` keep indexing `metaSharing` directly. W1 specifies the construction
(§13.2) and W2 mirrors it.

W4's part, after W1's construction lands: the readers (Lean `Ix/DecompileM.lean` and
`Ix/Tc/IngressMeta.lean`, Rust `decompile.rs` and kernel ingress of metadata; the IxVM only if it
reads metadata) resolve the extended space, with today's behaviour as the `i < p` case and the
`i ≥ p + q` rejection added; the format text and tests follow. Until then readers and writers keep
the current behaviour.

### 5.4 How per-occurrence arena roots survive

Arena nodes mirror the **unshared** logical tree; a Share is transparent and keeps the same arena
index (Lean `Ix/Tc/IngressMeta.lean:21-24, 354-370`; `Ix/DecompileM.lean:388-394`; Rust
`decompile.rs:861-874`, `ingress.rs:746-756`). Call-site `canonMeta` is distributed over the
canonical App telescope after expanding Shares along the spine (Lean
`collectIxonTelescopeExpandingShares`, `Ix/DecompileM.lean:369-384`; Rust `decompile.rs:807-835`,
`ingress.rs:1028-1056`); eta call sites strip `nSynth` lambdas, expanding Shares at each step
(`Ix/DecompileM.lean:438-451`; `decompile.rs:1103-1115`). Universe patches are keyed by arena index
(`Ix/DecompileM.lean:91-97`). Root indices (`typeRoot`, `valueRoot`, `ruleRoots`) are arena indices.
So any change of which subterms are shared, or of where a Share cuts a telescope, leaves arena
roots, binder data, call-site surgery, universe patches and `Named.original` valid, and a
metadata-only edit cannot change anonymous bytes (metadata is not part of `Constant`).

## 6. Version-bump checklist

Policy (`docs/Ixon.md`, "Environment Serialization"): any byte change bumps the version, readers
reject a mismatch, there is no back-compat reading, and `.ixe` files are regenerated. The next
version is 4.

**State on this branch.** The integer code is already TagN everywhere (§8), but the version is
still 3 (`Ix/Ixon.lean:2675` `Env.VERSION`, `crates/ixon/src/serialize.rs:1573`) and the format
IDs are the v3 ones; there is no `NEXT_VERSION` scaffolding and no format switch. So the branch
writes TagN bytes under the v3 header and v3 identifiers: no artifact may be published from it
until the flip, which needs the frozen codec and its proofs (§4).

**The flip (owner decisions §0b-2, §0b-7), one change in both languages:**

1. `Ixon.Env.VERSION` / `Env::VERSION` := 4, so the env header is TagN(4, `0xE`, 4) = `0xE4`.
   Writers: `Ix/Ixon.lean` env `put`/`putEnv` paths, `serialize.rs` env writers; readers: Lean
   `Env.get`/`getEnvVerifiedLazy`, Rust `read_env_header` (used by `get`, `get_anon`,
   `get_anon_mmap`, `parse_lazy_index`). `ix compile --report` prints it
   (`Ix/Cli/CompileCmd.lean:185`). Every CLI command reads through these readers; no command checks
   the version itself *(sweep)*;
2. the object-format byte `3` → `4` in claim and proof scope: Lean `Ix/Claim.lean` (`putScope`/
   `getScope`, "claim: unsupported object format"), Rust `proof.rs` `put_scope`/`get_scope`;
   catalogs `Ix/Catalog.lean:188-189, 250-251`, `catalog.rs:231, 310-315`; in-circuit
   `Ix/IxVM/Kernel/Claim.lean:1226-1227`, `Ix/Aggr/Circuit.lean:536-537` and their generated Rust
   *(sweep, except `Claim.lean` and `proof.rs`)*;
3. the resource validator ID `"ixon-v3/resource-v1"` → `"ixon-v4/resource-v1"`
   (`Ix/Resource/Addressed.lean:21`, `crates/ixon/src/resource/addressed.rs:16`; hashed into
   profile bytes);
4. `Ixon.wireFormatId` (`Ix/Ixon.lean:22`) and Rust `WIRE_FORMAT_ID` (`crates/ixon/src/lib.rs:35`)
   `"ixon-v3"` → `"ixon-v4"` (defined, never used);
5. the fixtures and pins below, regenerated through their producers in the same change;
6. the IxVM codec, every header (§3.1), and `lake exe ix codegen` (assigned separately).

The text-grammar version (`Ix/IxonSyntax/AST.lean:24-26`, `crates/ixon/src/syntax/mod.rs:29-31`)
covers no integer bytes and need not change. No sharing-construction version identifier exists;
`ShareLayout::from_code` is an FFI test selector only.

**Pins and golden fixtures that change.** All of these change with TagN alone (finding 1); the
flip changes several again (header byte, object-format byte, validator ID), so they are
regenerated once, at the flip. The "fails now" column is what this branch observes with TagN under
version 3:

| Pin | Location | Fails now | Regenerate with |
|---|---|---|---|
| Handoff fixtures and digests | `Tests/Fixtures/ixon-v3/handoff/{accepted.ixe, rejected-local-escape.ixe, profile.bin, accepted.claim, manifest.json}`; consumers `Tests/IxonV3Main.lean`, `Tests/IxonV3Handoff.lean`, `crates/kernel/src/resource.rs:126-162` | `ix-kernel` `resource::tests::cross_language_consumer_handoff` | `lake exe ixon-v3-tests --export-handoff` (directory and exe renamed for v4, §6 of the plan) |
| Env-bytes hash | `crates/compile/src/graph.rs:720-738` | `ix-compile` `graph::tests::setup_scan_preserves_compiled_fixture_bytes` | rerun and paste |
| Canonical primitive addresses | `crates/common/src/prim_addrs.rs` `PrimAddrs::new`, `Ix/Tc/Primitive.lean:134-227`, IxVM address literals (`Ix/IxVM/Kernel/{NatPrim,Infer,Whnf,Check,InferOnly}.lean`), `Tests/Fixtures/ixon-v3/primitives.tsv` *(sweep)* | Lean `primitive-address-parity` (57 of 57 mismatched) | `lake test -- --ignored rust-kernel-build-primitives` |
| Claims | `Tests/Fixtures/ixon-v3/claims.tsv` | `ixon` `proof::tests::v3_claim_fixtures_and_strict_scope` (variant 8 read as 16) | the claims fixture producer |
| Catalog claim digest | `Tests/Ix/Claim.lean` (`catalogDigestPin`), `crates/ixon/src/proof.rs` `catalog_claim_wire_bytes_pinned` (hex) | Lean `claim` "Catalog digest parity with Rust pin"; the Rust hex assertion | at the flip, from the serializers' output (Lean and Rust must agree); the wire-byte assertions already expect `E8 00` |
| Resource and addressed fixtures | `Tests/Fixtures/ixon-v3/resource.tsv`, `addressed.tsv` | `ixon` `resource::addressed::tests::canonical_cross_language_fixtures` (profile row) | the fixture producer |
| In-circuit claim readers | `Ix/IxVM/Kernel/Claim.lean`, `Ix/Aggr/Circuit.lean` (Catalog `E8 00`, Resource `E8 01`, object-format byte) | IxVM suites (not run here) | with the IxVM codec |
| FLT benchmark artifact | `Benchmarks/Kernel/AnthropicFLT/cases.json:5-9` *(sweep)* | not run | re-derive addresses |
| `expressions.txt`, `text.tsv` | `Tests/Fixtures/ixon-v3/` | not observed failing | re-check value by value; `text.tsv` holds no bytes |

Keep the historical aggregate proof fixture and add a new dated one.

**`.ixe` regeneration path.** `lake exe ix compile <file>.lean --out <x>.ixe`. CI runs
`lake exe ixon-v3-primitives` then `lake exe ixon-v3-tests --primitives` (`ci.yml:54-57`). CI `.ixe`
caches are keyed by commit. Stale on-disk artifacts that tests reuse *(sweep)*: `tc-parity.ixe` at
the repo root (`Tests/Ix/Tc/ParityEnv.lean:29-31`), `comppoly.ixe`, `tauceti.ixe`,
`IX_SHARING_CORPUS`; the TruthMines piece cache, whose key
(`Benchmarks/TruthMinesSpec/Main.lean:240-268`) omits the format version; `ix bench` closure shards
(`Ix/Cli/BenchCmd.lean:683-704`).

## 7. Risks

1. **Lean/Rust disagreement of tiered outputs** forks the address space. Fixtures and generated
   inputs agree byte for byte at TagN (§8); the Init + Mathlib-sample gate with the final rules is
   the plan §1 gate. [-]
2. **Resource exhaustion in the compiler.** The tiered construction fails closed; a constant over
   the limits is a compile error for every caller (compile, aux-gen, kernel egress, decompile
   recompile). Decision §0b-4: defaults far above every corpus maximum (Mathlib: largest MSS table
   21,461 entries; 81,833 candidates), a CLI override, and identical counters in Lean and Rust on the
   production route; today the two languages count work differently (`exact-sharing-ffi` reports
   one-sided exhaustion). [-]
3. **Proof debt** (§4): `IxCompileVerify` does not build on this branch until the codec theorems are
   restated with `tagNBytes` and the uniform-model theorems with θmax (finding 7). [all]
4. **IxVM lag** (finding 2): the circuit still reads Tag0/Tag2/Tag4, so it misreads any constant
   or claim with an integer past the first rung until it is updated. [Share] [Tag4] [all]
5. **Width-jump assumptions.** TagN grows by one byte per rung end except by four at `R5`. The
   count threshold (finding 7) is generalized in both languages; the certain-excluded rule's
   header subadditivity (finding 9) holds below `R5` nodes, which `maxNodes` must keep
   ensuring when the limits are raised (§0b-4). Any other argument that assumes a header grows by
   at most one byte per boundary is unsound from `R5` on.
   The `Search.lean` pruning bound uses only monotonicity of `tag0Size`, which TagN keeps. [Tag4]
   [all]
6. **Recompile invariant**: Rust `roundtrip_block` requires recompiled addresses to equal
   `Named.original` (`decompile.rs:3390-3405`); the recompile goes through the compiler's switch
   (`SharingRoute::compiler()`), so it follows the route. [-]
7. **Unpublishable intermediate state**: TagN bytes under version 3 and v3 identifiers (§6). [-]
8. **Header aliasing** (finding 6), kept by decision. [-]
9. **Stale caches** keyed without the format version (TruthMines, `ix bench` shards). [-]
10. **Metadata Share** (§5.3): readers change with the extended index space. [-]

## 8. Seams on this branch

**Integer code (`93e2895c`).** TagN is the only code. Rungs as in `sharing-minimum.md` §12.16
(`480923f2`): one header byte, then 0, 1, 2, 3, 4 or 8 bytes; rung ends
`tagNEnd1..tagNEnd5` (Lean) / `TagN::end1..end5` (Rust), and the 8-byte rung rejects values
reaching `2^64`. For `f = 4` every code is valid; for `f = 0, 2`, codes `c ≥ 4` are rejected.

- Lean: `Ixon.putTagN f flag value` / `Ixon.getTagN f` (`TagN` = `{flag, value}`) at every site of
  `Ix/Ixon.lean` (expressions, universes, constants and projections, metadata, names, environments,
  commitments), `Ix/Claim.lean`, `Ix/AssumptionTree.lean`, `Ix/Resource/Addressed.lean` and the
  exact-sharing oracle; `getTagN0Values` reads `count` TagN (`f = 0`) values. Deleted: the
  `Tag0`/`Tag2`/`Tag4` structures, `putTag0/2/4`, `getTag0/2/4`, `Serialize Tag4`, the three
  "noncanonical … integer" checks, and the Share-codec threading (`ShareCodec` arguments,
  `putShare`, `getExprHeader`, `peekU8?`).
- Rust: `crates/ixon/src/tag.rs` defines only `TagN` (`put`, `get`, `byte_width`, `end1..end5`);
  every former `Tag0`/`Tag2`/`Tag4` site in `ixon`, `ix-compile` and `ix-kernel` uses it. Deleted:
  `Tag0`/`Tag2`/`Tag4`, the `*_with` codec variants, and the FFI hooks
  `rs_eq_expr_serialization_with`, `rs_eq_constant_serialization_with`, `rs_share_codec_recode`.
- Compatibility shims, removed together with `ShareLayout.tag4` in `Ix/Sharing/Exact/Tiered.lean`
  and `crates/ixon/src/sharing_exact/tiered.rs` (W1/W2; not edited here): `Ixon.ShareCodec`
  (`Ix/Sharing/Exact/Basic.lean`) and Rust `serialize::ShareCodec`, each `{tag4, tagN}` with the
  current code `tagN`, so `ShareLayout.wire = .tagN`. `ShareLayout.tag4` now prices Shares with
  `shareWidth`, which is TagN, and differs from `.tagN` only in its nominal tier-2 end (256).
- Generic little-endian helpers stay (`Ixon.putU64TrimmedLE`/`getU64TrimmedLE`/`u64ByteCount`, Rust
  `u64_put_trimmed_le`/`u64_get_trimmed_le`/`u64_byte_count`); after the proof restatement the Lean
  ones may have no user.

**Pricing (`93e2895c`).** As in §3.4 and finding 7: identical in Lean and Rust.

**Tests (`93e2895c`, `15001658`).** TagN vectors for `f = 4, 2, 0` in the Rust doc examples
(`crates/ixon/src/lib.rs`), byte-identical TagN units in Lean `tagNUnits` and Rust `tag.rs`, TagN
rejection cases (invalid code, overflow, truncation) instead of non-canonical encodings, width
pins at every TagN rung end, the catalog claim tag `E8 00`, the bracket-start and step-bound checks
in both languages, and the exact-sharing, tiered and FFI-parity suites on the TagN layout only (the
`tiered-tag4` mode and the Share-codec recode groups are gone).

Results on the merge of `ix-sharing` at `0c84fe7a` (W6's arena encoding) with the 4-byte rung
(`9c6384be` plus `0b09aa65`, the arena vector and formatting fixes):

- `lake build`: 321 jobs, no error or warning. `IxTests`, `IxTcVerify` (sorry frontier OK) and the
  executables `ix`, `ixon-v3-tests`, `ixon-v3-primitives`, `sharing-study`, `uniform-hard`,
  `source-contract-tests`, `arena-exclude` build. `IxCompileVerify` does not (§4).
- `lake test` (every primary suite): all pass except `claim` "Catalog digest parity with Rust pin"
  and `primitive-address-parity` (§6). `exact-sharing-ffi`: §2 fixtures × 6 modes 76 same bytes;
  350 generated inputs × modes 2,048 same bytes; 124 Share-bearing Constants (119 tiered outputs;
  5 synthetic: tables up to 66,600 entries and Shares in the 4-, 5- and 9-byte rungs) 0
  disagreements; compiler routes 153 × 2 = 306 same bytes.
- Rust: `cargo fmt --all --check` clean; `cargo build` and `cargo clippy -- -D warnings` (dev
  profile) on `--workspace --all-targets --features ix-ffi/parallel,ix-ffi/net,ix-ffi/test-ffi`
  clean. `cargo test --no-fail-fast`: `ixon` 388 passed, 3 failed; `ix-compile` 307 passed, 1
  failed; `ix-kernel` 850 passed, 1 failed; `ix-common` 17 and `ix-ffi` 23 pass. Every failure is a
  pin or fixture of §6.
- Not run on this state: the ignored heavy suites (`compile`, `decompile`, `rust-*`,
  `ixon-corpus`, …) and the IxVM suites.

**Construction (`6100f9f2`).** One switch per language, `Ix.CompileM.compilerSharing` and Rust
`ix_compile::compile::COMPILER_SHARING`, both `heuristic`; `tiered tagN` runs under explicit
limits (`compilerSharingLimits`, `compiler_sharing_limits()`: each language's library defaults,
spelled out).

- Lean: every block goes through `buildConstantWithSharingVia` (singletons through
  `finishConstantWithSharing` → `buildBlockConstant`, standalone inductive families through
  `finishInductiveFamilyBlock`, mutual blocks through `finishMutualCompilation` →
  `buildCompiledMutualBlockVia`, aux-gen standalone and mutual blocks in
  `Ix/AuxGen/CompileAux.lean`). The heuristic branch reduces definitionally to the previous code.
  The tiered route derives the roots from the payload, checks the caller's root count, and
  reassembles with the checked `Ix.Sharing.Exact.withRoots` (no `getD` fallback).
- Rust: `apply_sharing_to_{definition,axiom,quotient,recursor}_with_stats` and
  `apply_sharing_to_mutual_block` return `Result` and go through `share_roots` along
  `SharingRoute::compiler()`; `_via` variants take an explicit route (tests, FFI hook
  `rs_compiler_sharing_build`). Compile and aux-gen propagate with `?`, kernel egress maps to its
  `String` errors, decompile recompile maps to `DecompileError::BadConstantFormat`, and the
  `IX_ROUNDTRIP_DEBUG` probe reports the failure.
- Errors: resource exhaustion is `CompileError.resourceLimit`; every other construction failure is
  `CompileError.sharingConstruction` (tag 7, mirrored in Rust and the FFI constructor tables).
  There is no fallback to the heuristic.

**Remaining before the route switch, in order:** (0) Rust `tiered.rs` `tagn_width` and its
`TAGN_RUNG*_END` constants follow the 4-byte rung (W2): until then the Rust layout prices Shares
at indices of 66,568 and more with the old widths, so Rust's wire-layout self-check fails closed
on tables of more than 66,568 entries (Lean, whose `tagNWidth` is `Ixon.tagNByteWidth 4`, follows already);
`TagN.lean` re-proved against the six rungs (W1); (1) the codec theorems restated (W1; §4,
Appendix A), so that `IxCompileVerify` builds again; (2) `ShareLayout.tag4` removed from `Tiered.lean` and
`tiered.rs` (W1/W2), then the two `ShareCodec` shims deleted (W4); (3) compiler limits per §0b-4
and a CLI override (W4; identical counters are a W1/W2 item); (4) the switch: `tiered tagN`
becomes the only route, the switch type and the heuristic branch go away, and the §4.3 endpoint
and run lemmas are restated on `FormatOK` (W4); (5) the heuristic removed: `Ix/Sharing.lean`,
`crates/ixon/src/sharing.rs`, `Ix/Compile/Verify/Sharing.lean` and its audit roots, the
`useHeuristicBound` seeds in the exact optimizers (`Ix/Sharing/Exact.lean` `heuristicVariableBytes`,
Rust counterpart; the unshared length stays the bound), the `sharing` suite and the
`rs_expr_hash_matches` hook, keeping only helpers the exact core needs, moved under
`Ix/Sharing/Exact/` (W4). Then the flip (§6) and the IxVM codec.

## 9. Owner decisions on the questions of this map

1. Scope of TagN: all three families, every header including claim, proof, comm and
   assumption-tree headers (§12.12). Done.
2. Object-format byte, validator ID, `wireFormatId`: bump with the version to `4`,
   `"ixon-v4/resource-v1"`, `"ixon-v4"` (§6, not yet applied).
3. Endpoint theorem: the real `wireWF` + capacity + backwardness theorem lands before the flip;
   W1's `canonicalSharingTiered_format` provides it, W4 wires the endpoints at the route switch
   (§4.3).
4. Compiler limits: a safety net (§7 risk 2); not yet applied.
5. `metaSharing`: the extended index space of `sharing-minimum.md` §13 (§5.3); readers are W4's,
   after W1's construction.
6. IxVM: in this PR, after the codecs are stable; assigned separately.
7. Header aliasing: keep; the env header is TagN(4, `0xE`, version), `0xE4` for v4 (finding 6).
8. Cost-model repricing: done on this branch in both languages (finding 1b, §3.4).

## Appendix A. Codec theorems over the deleted integer code

Format: `name` (line, class), at commit `01e05b00`. Classes as in §4.4.

- **`Codec.lean`**: `tag2_small_fields` (145, S), `getTag2_reads_small` (158, S), `runPut_putTag2_small` (175, S), `putTag2_writes_small` (193, S), `tag2Bytes` (379, D), `putTag2_writes` (387, S), `getTag2_reads_large` (394, S), `getTag2_reads` (474, S), `tag0Bytes` (486, D), `putTag0_writes` (494, S), `tag0_small_fields` (634, S), `getTag0_reads_small` (641, S), `getTag0_reads_large` (664, S), `getTag0_reads` (739, S), `tag4Bytes` (756, D), `putTag4_writes` (764, S), `tag4_small_fields` (778, S), `getTag4_reads_small` (790, S), `getTag4_reads_large` (822, S), `getTag4_reads` (902, S), `putUniv_writes_small` (989, P), `getUnivFuel_reads_small` (1037, P), `wireEncode` (1253, D), `tag2Bytes_size_pos` (1273, S), `wireEncode_size_pos` (1278, P), `putUniv_writes` (1283, P), `getUnivFuel_reads` (1320, P)
- **`CompileMeta.lean`**: `serializeIxSubstringRef` (18, D), `serializeIxSourceInfoRef` (24, D), `serializeIxSyntaxPreresolvedRef` (35, D), `serializeIxSyntaxRef` (45, D)
- **`CompileMetaStore.lean`**: `serializeIxSubstring_run_strict` (936, P), `serializeIxSourceInfo_run_strict` (956, P), `serializeIxSyntaxPreresolved_run_strict` (989, P), `serializeIxSyntax_run_strict_effect` (1062, P)
- **`ConstantCodec.lean`**: `definitionBytes` (18, D), `axiomBytes` (23, D), `putDefinition_writes` (46, P), `putAxiom_writes` (58, P), `getDefinition_reads` (67, P), `getAxiom_reads` (134, P), `infoBytes` (195, D), `getInfoFromTag` (213, D), `getConstantInfo_eq` (233, S), `putConstantInfo_writes_core` (237, P), `getConstantInfo_reads_core` (252, P), `emptyConstantBytes` (301, D), `getConstantUnivs` (304, D), `getConstantRefs` (313, D), `getConstantAfterInfo` (321, D), `putConstant_writes_core_empty` (333, P), `getConstant_reads_core_empty` (343, P)
- **`ConstantTablesCodec.lean`**: `constantBytes` (256, D), `putConstant_writes_core` (267, P), `getConstantUnivs_reads_core` (279, S), `getConstantRefs_reads_core` (315, S), `getConstantAfterInfo_reads_core` (356, S)
- **`ExprCodec.lean`**: `tag0ListBytes` (60, D), `wireEncode` (64, D), `tag0Bytes_size_pos` (93, S), `tag0ListBytes_size_ge_length` (97, S), `tag4Bytes_size_pos` (106, S), `wireEncode_size_pos` (111, P), `putTag0List` (172, D), `putTag0List_writes` (175, S), `arrayPutTag0_eq_putTag0List` (187, S), `arrayPutTag0_writes` (193, S), `getTag0Sizes_reads` (199, S), `putExpr_writes_single` (223, P), `getExprFuel_reads_single` (298, P)
- **`ExprSpineCodec.lean`**: `spineWireEncode` (198, D), `spineWireEncode_size_pos` (267, P), `putExpr_writes_spine` (565, P), `spineWireEncode_app` (684, S), `spineWireEncode_lam` (694, S), `spineWireEncode_all` (705, S), `getExprFuel_reads_spine` (942, P)
- **`MutualConstantCodec.lean`**: `constructorBytes` (22, D), `constructorBytes_size_ge` (28, P), `putConstructor_writes` (42, P), `getConstructor_reads` (56, P), `inductiveBytes` (141, D), `putInductive_writes` (155, P), `getInductiveConstructors` (170, D), `getInductiveAfterFlags` (179, D), `getInductiveConstructors_reads` (191, S), `getInductiveAfterFlags_reads` (234, S), `constantInfoBytes` (381, D), `putConstantInfo_writes` (387, P), `getConstantInfo_reads` (407, P), `constantBytes` (590, D), `putConstant_writes` (601, P)
- **`NonrecursiveConstantCodec.lean`**: `quotientBytes` (29, D), `putQuotient_writes` (34, P), `getQuotient_reads` (76, P), `inductiveProjBytes` (144, D), `constructorProjBytes` (147, D), `recursorProjBytes` (151, D), `definitionProjBytes` (154, D), `putInductiveProj_writes` (157, P), `getInductiveProj_reads` (164, P), `putConstructorProj_writes` (182, P), `getConstructorProj_reads` (191, P), `putRecursorProj_writes` (219, P), `getRecursorProj_reads` (226, P), `putDefinitionProj_writes` (244, P), `getDefinitionProj_reads` (251, P), `nonrecursiveInfoBytes` (293, D), `putConstantInfo_writes_nonrecursive` (317, P), `getConstantInfo_reads_variant` (348, S), `nonrecursiveConstantBytes` (423, D), `putConstant_writes_nonrecursive` (434, P)
- **`RecursorConstantCodec.lean`**: `recursorRuleBytes` (21, D), `recursorRuleBytes_size_ge` (36, P), `putRecursorRule_writes` (46, P), `getRecursorRule_reads` (53, P), `recursorBytes` (97, D), `putRecursor_writes` (111, P), `getRecursorRules` (127, D), `getRecursorAfterFlags` (136, D), `getRecursorRules_reads` (154, S), `getRecursorAfterFlags_reads` (196, S), `getRecursor_reads` (261, P), `standaloneInfoBytes` (287, D), `putConstantInfo_writes_standalone` (293, P), `standaloneConstantBytes` (333, D), `putConstant_writes_standalone` (344, P)
- **`SharingExact.lean`**: `trimmedBytes_size` (102, P), `tag4Bytes_size` (106, S), `tag0Bytes_size` (119, S), `putTag4_size` (132, S), `putTag0_size` (138, S), `shareWidth_eq_putTag4` (144, S), `byteCount_eq_u64ByteCount` (152, P), `tag0EncodedSize_eq` (159, S), `tag4EncodedSize_eq` (170, S), `tag0ListBytes_size` (280, S), `univIdxsSize_eq` (286, S), `sizeInfoWith_app_full` (358, S), `sizeInfoWith_lam_full` (366, S), `sizeInfoWith_all_full` (374, S), `sizeInfo_spec` (385, S), `ruleFixed` (533, D), `ctorFixed` (535, D), `recFixed` (539, D), `indFixed` (544, D), `memberFixed` (548, D), `infoFixed` (554, D), `rules_bytes` (562, P), `ctors_bytes` (570, P), `recursorBytes_map` (579, P), `inductiveBytes_map` (590, P), `memberBytes_map` (601, P), `infoBytes_mapRoots` (634, P), `constantBytes_size` (791, S), `S_var_zero` (803, P), `serConstant_size_decomposition` (808, S)
- **`SharingExactPasses.lean`**: `materializeTable_parts` (514, P), `tableInv_loop` (575, P)
- **`TieredGuard.lean`**: `WTree.base` (38, D), `phase3_le_phase1` (718, P), `widthAt_lt8` (999, P), `widthAt_tier2` (1006, P)
- **`TieredModel.lean`**: `gCutCost` (34, D), `PrepWF.gCutScan_spec` (182, P), `PrepWF.gEvalStep_spec` (239, P), `PrepWF.gCutOptions_spec` (483, P), `PrepWF.gInlineCost_eq` (547, P), `PrepWF.gCutOptions_pairs` (670, P), `PrepWF.gOptions_mem` (729, P), `WTree.gcost` (1007, D)
- **`TieredPhase3.lean`**: `TableEvInv` (73, D), `tableEvInv_loop` (145, P), `materializeTable_spec` (193, S), `layoutBytes_eq` (279, S)
- **`UniformClasses.lean`**: `PrepWF.conts_zero` (1109, P), `uniformCost_insert_le_counts` (1132, S), `tag0Size_mono` (1224, S), `mem_of_gain` (1233, S), `tag0_growth_lt` (1257, S), `stored_in_minimum` (1279, S), `same_bracket` (1307, S), `tag4Size_add_le` (1344, S), `ownBytes_pos` (1392, P), `PrepWF.cost_pos` (1407, P), `PrepWF.unshare_spec` (1486, P), `PrepWF.removal` (1662, P), `PrepWF.unreferenced` (1731, P), `gain_d_pos` (2017, P), `classify_sound` (2062, S), `threshold_one_sound` (2123, P)
- **`UniformDecomp.lean`**: `cutsRange` (148, D), `natFrom` (155, D), `PrepWF.inl_split` (191, P), `mem_cutsRange` (234, S), `PrepWF.teleFrom_dom` (256, S), `uniformCost_modular` (715, S), `gain_opaque_bounds` (798, P), `components_modular` (871, S), `lower_bound_sound` (1015, S)
- **`UniformExchange.lean`**: `tag4Size_pos` (52, S), `tag4Size_mono` (85, S), `tag0Size_succ_le` (90, S), `inl_merged_bounds` (109, S), `PrepWF.subst_spec` (415, P)
- **`UniformGain.lean`**: `PrepWF.exchange_counts` (493, P), `PrepWF.exchange` (602, P), `uniformCost_insert_le` (716, P)
- **`UniformKnapsack.lean`**: `knapTotal` (274, D), `knapChoose_le` (278, S), `knapChoose_tie` (619, S)
- **`UniformLength.lean`**: `rebuild_size` (34, S), `spineFold_size` (62, S), `PrepWF.cutOptions_pairs` (176, P), `PrepWF.options_mem` (235, P), `optimizeUniform_variableBytes` (538, S)
- **`UniformModel.lean`**: `naturalCost` (316, D), `cutCosts` (321, D), `uniformCost` (353, D), `cutCost` (485, D), `PrepWF.cutScan_spec` (550, P), `PrepWF.evalStep_spec` (656, P), `PrepWF.cutOptions_spec` (1064, P), `share_opts_filter` (1137, S), `PrepWF.inlineCost_eq` (1172, P)
- **`UniformOptimality.lean`**: `stage_cls_theta` (27, S), `compEnv_wf` (198, P), `csBase_eq` (393, S), `ulen_compParts` (449, S), `tag0Size_bracketStart` (523, S), `tag0Size_ge_of_bracket` (542, S), `uniformKnapsack_le` (598, S), `uniformKnapsack_tie` (1089, S), `uniformChoose_tie` (1275, P)
- **`UniformOptimal.lean`**: `ulen_compCost` (201, S), `ulen_split_component` (302, S), `uunc` (697, D), `GlobalWF.theta_ok` (759, S), `group_rep` (841, S)
- **`UniformOptimizer.lean`**: `materializeDependent_total` (171, S), `uniformFinish_spec` (192, S)
- **`UniformWritings.lean`**: `WTree.cost` (30, D), `encodingCost` (365, D)
