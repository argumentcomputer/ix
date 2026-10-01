# Canonical sharing: integration map (workstream W4)

Integration inventory for plan gates P5–P6 of [`sharing-minimum.md`](sharing-minimum.md), after the
decision of §12.8: the canonical sharing of a constant becomes
`Ix.Sharing.Exact.canonicalSharingTiered .tagN` (Rust `canonical_sharing_tiered(ShareLayout::TagN, ..)`),
the Share index adopts the TagN code, backward references stay, and the format version bumps.

Still open: whether TagN replaces only the Share integer, every Tag4 integer, or all three tag
families (Tag0, Tag2, Tag4). Every item below that depends on that answer is marked:

- **[Share]**: needed for the Share-only TagN scope (and therefore for every scope);
- **[Tag4]**: needed only if every Tag4 integer becomes TagN;
- **[all]**: needed only if Tag0 and Tag2 integers become TagN too;
- **[-]**: independent of the TagN scope (construction, version, metadata, fixtures).

Line numbers are those of commit `3ddda798` (the base of branch `ix-sharing-w4`). Every entry was
read in the source; entries taken from a delegated sweep and not re-read are marked
*(sweep)*.

## 1. Key findings

1. **Share-only TagN is byte-identical to Tag4 for indices 0–7.** Both write `0xB0 | idx`. Every
   hardcoded Share byte vector and fixture in the repository uses Share 0 or 1, so the Share-only
   codec change alone alters no existing fixture bytes; only tables with more than 8 entries change.
   The construction change and the version header still change addresses.
2. **The plan's source map misses a third codec: the IxVM circuit.** `Ix/IxVM/IxonDeserialize.lean`
   reads every expression header with `get_tag4` (line 221) and maps `0xB => Expr.Share(size)`
   (294); `Ix/IxVM/IxonSerialize.lean:60` writes `put_tag4(0xB, idx, rest)`. The Rust file
   `crates/ixvm-codegen/src/aiur_ixvm.rs` is generated from these (`lake exe ix codegen`; CI runs
   `lake exe ix codegen --check`, `.github/workflows/ci.yml:45`). A v4 constant with a table of 9 or
   more entries is misread by the v3 circuit.
3. **Metadata never references the primary table by index.** `CallSiteEntry.collapsed.sharingIdx`
   and `callSite.origHead` index the per-constant `ConstantMeta.metaSharing` vector, arena roots
   follow the unshared logical tree, and every consumer expands `Share` transparently. Re-sharing a
   constant leaves its metadata valid (§5). One latent coupling exists: the documented contract
   says metadata expressions "may contain Share" into an extended table, but both decompilers
   resolve such a Share against the primary table; neither compiler emits one.
4. **No proof covers the tiered construction's output as a wire-valid Constant.** All compiler
   endpoint theorems are stated against the concrete heuristic `Ix.CompileM.buildConstantWithSharing`,
   and `buildConstantWithSharing_wireWF` is the single theorem that consumes heuristic facts
   (`applySharing_wireWF`, `applySharing_capacity`). Making the tiered route the default requires a
   `wireWF` + capacity theorem for its output (§4.3).
5. **No theorem establishes `DecodeCtx.SharingWF`** (backward references,
   `Ix/Compile/Verify/Catalog.lean:324`) for any compiler output, heuristic or tiered.
6. **Version header aliasing.** The Env header and the claim tags share Tag4 flag `0xE`. Version 3
   (`0xE3`) equals the Eval-claim tag and version 4 (`0xE4`) equals the Check-claim tag
   (`crates/ixon/src/proof.rs:216-217`). `docs/Ixon.md:1201-1203` already treats the header as
   context-dependent ("the enclosing protocol must identify the object kind"), and every reader
   dispatches by context; the text and the table row at 1215 name `0xE3` and need updating.

## 2. Where the plan and the code disagree

| Plan statement | Code |
|---|---|
| §8.3 "The expression byte grammar need not change." | True for the construction alone. False after §12.8: the Share grammar changes for indices ≥ 8 (TagN rung 2 starts at 8). |
| §8.2 "Metadata expressions may also contain Share references." | Neither compiler emits Share into `metaSharing` (Lean: `.share` is constructed only by `Ix/Sharing.lean:363` and `Ix/Resource/Addressed.lean:197`; Rust: `compile.rs` emits no Share outside `apply_sharing_*`). The documented "extended sharing table" (`Ix/Ixon.lean` `ConstantMeta.metaSharing` doc; `crates/ixon/src/metadata.rs:237-250`) is not implemented by any reader (§5.3). |
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

| Site | Today | Change | Scope |
|---|---|---|---|
| `Ix/Sharing/Exact/Basic.lean:45` `shareWidth := tag4Size`, `:113` `sizeInfo := sizeInfoWith tag4Size`, `:117` `exprSize`; Rust `sharing_exact/cost.rs:69-81, 115-121` | Tag4 widths ("exact length of `putExpr`") | the wire codec's widths | [Share] |
| `Ix/Sharing/Exact/Tiered.lean:316-318` measured length and the check `layout == .tag4 && measured != predicted`; Rust `tiered.rs:474-483` | measured with Tag4 | measure with the wire codec; check whenever the layout is the wire layout | [Share] |
| `Ix/Sharing/Exact/Dictionary.lean:264` Share option bytes `tag4Bytes FLAG_SHARE i` | Tag4 | No effect on results in the Share-only scope: a Share option is only ever tied against inline or cut options, whose first byte has a flag nibble `0x0..0xA < 0xB`, so the Share option loses every tie in either code. Make it the wire bytes for hygiene. | [Share] |
| `Dictionary.lean:254, 272, 276` cut/inline header bytes `tag4Bytes flag j`; Rust `dict.rs:171-181` `tag4_bytes_cmp` | Tag4 | must become the TagN header bytes: two cuts with `j ≥ 8` can order differently, which changes canonical output | [Tag4] |
| `Ix/Sharing/Exact/Basic.lean` `tag4Size` for every header and `tag0Size` for refs/univs/table count; the uniform model (`Uniform.lean`) and its proofs | Tag4/Tag0 | TagN widths throughout | [Tag4], [all] |
| Heuristic: `Ix/Sharing.lean:300` `shareRefSize`; Rust `crates/ixon/src/sharing.rs:367-368, 499-500` | Tag4 | optional (regression path only) | [Share] |
| Heuristic hash preimage of a Share leaf: `Ix/Sharing.lean:58`, Rust `sharing.rs:45` | `putExpr` bytes | follows the codec; affects only heuristic hashing (the exact optimizer uses structural IDs) | [Share] |

## 4. Verification theorems

All are in `IxCompileVerify` (`lakefile.lean:313-314`), which `lake lint -- --wfail` builds
(`.github/workflows/ci.yml:41`, driver `lakefile.lean:370-384`). No theorem in `Ix/Tc/Verify`
mentions these names, but `IxTcVerify` has `native_decide` serde fixtures
(`Ix/Tc/Verify/Ingress/SerializedBoolean.lean:42-81`, `Ingress/LiteralBlobs.lean`,
`Inductive/ConcreteFixture.lean`, `Inductive/EnumerationFixture.lean`) that recompute bytes with the
current codec.

### 4.1 Share wire bytes [Share]

| Theorem / def | What it says | Must become |
|---|---|---|
| `ExprCodec.lean:64` `wireEncode`, Share arm `:91` | `tag4Bytes FLAG_SHARE idx` | `TagN.tagNBytes 4 FLAG_SHARE idx` (`TagN.lean:68`); import `Ix.Compile.Verify.TagN` |
| `ExprSpineCodec.lean:198` `spineWireEncode`, Share arm `:239` | same | same |
| `ExprCodec.lean:111` `wireEncode_size_pos`, `ExprSpineCodec.lean:267` `spineWireEncode_size_pos` (Share cases) | from `tag4Bytes_size_pos` | from `TagN.tagNBytes_size` and `tagNByteWidth_pos` |
| `ExprCodec.lean:223` `putExpr_writes_single`, `ExprSpineCodec.lean:565` `putExpr_writes_spine` (Share cases) | `putTag4_writes FLAG_SHARE idx` | `TagN.putTagN_writes 4 FLAG_SHARE idx` (`TagN.lean:87`) |
| `ExprCodec.lean:298` `getExprFuel_reads_single`, `ExprSpineCodec.lean:942` `getExprFuel_reads_spine` | each of 12 cases builds `getTag4 >>= getExprFromTag ..` | Share case from `TagN.getTagN_reads 4 _ 0xB _ idx` (`TagN.lean:165`); the 11 other cases need one bridge lemma: on bytes `tag4Bytes flag size` with `flag ≠ 0xB`, the TagN-mode header reader behaves as `getTag4` |
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
| `Catalog.lean:324` `DecodeCtx.SharingWF` | no theorem establishes it for compiler output | new obligation for the tiered route (backwardness is already proved for `materializeTable`) |

The audit manifest `Ix/Compile/Verify/Audit/Statements.lean` (`run_cmd Ix.Tc.Verify.Audit.check
roots`, line 405) requires every listed root to exist with its exact axiom set; the roots at lines
56, 58, 218, 220, 222, 227, 254, 283, 325, 327, 330, 333, 336, 339, 366 and 368 are affected by the
changes above *(sweep; 220, 325, 327, 366, 368 re-read)*. TagN roots are already present (350-357).

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

### 5.3 Latent coupling (not triggered today)

`ConstantMeta.metaSharing` is documented as possibly containing `Share(idx)` "into the extended
sharing table" (`Ix/Ixon.lean` `ConstantMeta` doc; `metadata.rs:237-250`). Both decompilers would
resolve such a Share against the **primary** table (Lean `decompileExpr shared ..` runs under
`ctx.sharing = cnst.sharing`; Rust `Frame::Decompile`, `decompile.rs:861-874`), so a metadata
payload carrying one would silently change meaning when the primary table is re-optimized.
Recommendation: specify that `metaSharing` entries are Share-free and reject a Share there on decode,
or define the extended index space. Either way the question is independent of TagN.

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

Policy (`docs/Ixon.md:879-888`): any byte change bumps the version, readers reject a mismatch, there
is no back-compat reading, and `.ixe` files are regenerated. The next version is 4 (current 3:
`Ix/Ixon.lean:2772`, `crates/ixon/src/serialize.rs:1549`).

**Flip together** (both languages, one change):

1. `Ixon.Env.VERSION := 4` (`Ix/Ixon.lean:2772`) and `Env::VERSION = 4` (`serialize.rs:1549`).
   Writers: `Ix/Ixon.lean:2854, 3290`; `serialize.rs:1576, 1943, 3037`. Readers: `Ix/Ixon.lean:2989,
   3272`; `serialize.rs:121` (`read_env_header`, used by `get`, `get_anon`, `get_anon_mmap`,
   `parse_lazy_index`). `ix compile --report` prints it (`Ix/Cli/CompileCmd.lean:185`). Every CLI
   command reads through these readers; no command checks the version itself *(sweep)*.
2. Share codec default → TagN (§3.1) [Share]; headers, Tag0 and Tag2 per the open decision.
3. Exact-sharing pricing → wire codec (§3.4), with the width pins `Tests/Ix/SharingExact.lean:279-280,
   348` and `crates/ixon/src/sharing_exact/tests.rs:366-395` (Tag4 widths at 256 and 65536).
   `Tests/Ix/SharingExact.lean:274` checks `shareWidth n == (serExpr (.share n)).size`, so pricing
   and codec cannot drift silently.
4. Compiler sharing switch → tiered TagN (Lean and Rust), with the proof obligations of §4.
5. IxVM codec (§3.1) and `lake exe ix codegen`.
6. Proofs of §4.1 (and §4.2 for wider scopes).

**Format IDs** (policy decision; the same bytes would mean different Share indices under v3 and v4:
`B8 08` is Share(8) under Tag4 and Share(16) under TagN):

- the object-format byte `3` in claim and proof scope: Lean `Ix/Claim.lean:523-528` ("claim:
  unsupported object format"), Rust `proof.rs:957-968`; catalogs `Ix/Catalog.lean:188-189, 250-251`,
  `catalog.rs:231, 310-315`; in-circuit `Ix/IxVM/Kernel/Claim.lean:1226-1227`,
  `Ix/Aggr/Circuit.lean:536-537` and their generated Rust *(sweep, except `Claim.lean` and
  `proof.rs`)*;
- the validator ID `"ixon-v3/resource-v1"`, hashed into profile bytes
  (`Ix/Resource/Addressed.lean:21`, `crates/ixon/src/resource/addressed.rs:16`) *(sweep)*;
- `Ixon.wireFormatId := "ixon-v3"` (`Ix/Ixon.lean:22`; its doc comment says "v2") and Rust
  `WIRE_FORMAT_ID` (`crates/ixon/src/lib.rs:34-35`): defined, never used.

The text-grammar version (`Ix/IxonSyntax/AST.lean:24-26`, `crates/ixon/src/syntax/mod.rs:29-31`)
covers no Share bytes and need not change. No sharing-construction version identifier exists;
`ShareLayout::from_code` is an FFI test selector only.

**Pins and golden fixtures that change:**

| Pin | Location | Changes because |
|---|---|---|
| Handoff fixtures and digests | `Tests/Fixtures/ixon-v3/handoff/{accepted.ixe, rejected-local-escape.ixe, profile.bin, accepted.claim, manifest.json}`; consumers `Tests/IxonV3Main.lean`, `Tests/IxonV3Handoff.lean`, `crates/kernel/src/resource.rs:126-162` | header byte (byte 0 of `accepted.ixe` is `e3`); regenerate with `lake exe ixon-v3-tests --export-handoff` |
| Env-bytes hash | `crates/compile/src/graph.rs:720-738` (`34fe80b5…`) | header byte |
| Canonical primitive addresses | `crates/common/src/prim_addrs.rs` `PrimAddrs::new` (line 143), `Ix/Tc/Primitive.lean:134-227`, IxVM address literals (`Ix/IxVM/Kernel/{NatPrim,Infer,Whnf,Check,InferOnly}.lean`), `Tests/Fixtures/ixon-v3/primitives.tsv` *(sweep)* | new construction, and TagN for tables of 9+ entries; generator `lake test -- --ignored rust-kernel-build-primitives`; checked by the primary suites `primitive-address-parity` and `prim-addrs` |
| Addressed fixtures | `Tests/Fixtures/ixon-v3/addressed.tsv` | only if the validator ID or the `identity` constant changes (its Share is index 0) |
| Claims | `Tests/Fixtures/ixon-v3/claims.tsv`, catalog digest `Tests/Ix/Claim.lean:122-124`, `proof.rs:1499-1525` *(sweep)* | only if the object-format byte changes |
| FLT benchmark artifact | `Benchmarks/Kernel/AnthropicFLT/cases.json:5-9` *(sweep)* | v3 artifact unreadable; addresses re-derived |
| IxTcVerify `native_decide` fixtures | §4 | recomputed; literal address pins regenerated |

Unchanged in the Share-only scope: `expressions.txt` (no Share), `resource.tsv` (Shares 0 and 1),
`text.tsv`; the historical aggregate proof fixture (add a new dated one instead).

**`.ixe` regeneration path.** `lake exe ix compile <file>.lean --out <x>.ixe`. CI runs
`lake exe ixon-v3-primitives` then `lake exe ixon-v3-tests --primitives` (`ci.yml:54-57`). CI `.ixe`
caches are keyed by commit. Stale on-disk artifacts that tests reuse *(sweep)*: `tc-parity.ixe` at
the repo root (`Tests/Ix/Tc/ParityEnv.lean:29-31`), `comppoly.ixe`, `tauceti.ixe`,
`IX_SHARING_CORPUS`; the TruthMines piece cache, whose key
(`Benchmarks/TruthMinesSpec/Main.lean:240-268`) omits the format version; `ix bench` closure shards
(`Ix/Cli/BenchCmd.lean:683-704`).

**Docs.** `docs/Ixon.md:92, 285, 612-667` (Share as Tag4, the heuristic), `:879-891` (version 3,
`0xE3`), `:1201-1219` (header and claim table); `docs/Ixon-v3.md:157-161`;
`docs/compilatrix-ixon-v3.md:9-17`.

## 7. Risks

1. **Lean/Rust disagreement of tiered outputs** forks the address space. W2 reports 0 disagreements
   on Init (`sharing-minimum.md` §12.9); Mathlib has not been compared. [-]
2. **Resource exhaustion in the compiler.** The tiered construction fails closed; a constant over the
   limits becomes a compile error. Lean and Rust count work differently, so equal limits can succeed
   in one language and fail in the other (`Tests/Ix/SharingExactFFI.lean` reports one-sided
   exhaustion). Limits need headroom over the corpus maxima (Mathlib: largest MSS table 21,461
   entries; 81,833 candidates). [-]
3. **Proof debt** (§4.3): the default cannot flip without `wireWF`/capacity for the tiered output,
   unless the endpoint theorems carry a hypothesis. [-]
4. **IxVM lag** (finding 2): the circuit misreads v4 constants with 9+ table entries if it is not
   updated in the same change. [Share]
5. **Tie-break bytes in wider scopes** (§3.4): with every Tag4 integer as TagN, cut headers with
   `j ≥ 8` compare differently; updating only one of `Dictionary.lean:254-276` and `dict.rs:181`
   splits Lean and Rust. [Tag4]
6. **Recompile invariant**: Rust `roundtrip_block` requires recompiled addresses to equal
   `Named.original` (`decompile.rs:3390-3405`); a route that does not share the compiler's switch
   breaks decompilation. [-]
7. **Root arrays in Lean**: the heuristic writes rewritten roots back positionally with `getD`
   fallbacks, so a caller passing roots that differ from the payload's is silently accepted. [-]
8. **Header aliasing** (finding 6). [-]
9. **Stale caches** keyed without the format version (TruthMines, `ix bench` shards). [-]
10. **Metadata Share contract** (§5.3), latent. [-]

## 8. Seams on this branch

Introduced by the codec and routing commits that follow this map. Each concern sits behind one
switch per language, so either TagN outcome is a small delta:

- **Codec.** `Ixon.ShareCodec` (`.tag4 | .tagN`) with `ShareCodec.current := .tag4`, and Rust
  `ixon::ShareCodec` with `ShareCodec::CURRENT = Tag4`. Every writer and reader that reaches an
  expression takes the codec (Lean: a trailing argument defaulting to `ShareCodec.current`; Rust:
  `*_with` variants), so tests select either codec explicitly. The only codec-specific code is
  `Ixon.putShare`/`Ixon.getExprHeader` and Rust `ShareCodec::put`/`ShareCodec::get_expr_header`.
  - Share-only scope: flip `current`/`CURRENT`.
  - Every-Tag4 scope: make the TagN header reader read every expression header as TagN and route
    the other header writes of `putExpr`/`put_expr_with` through the codec (one function per
    language).
  - All-tags scope: the codec already reaches every expression-level Tag0 and the constant-level
    counts; the metadata, name and env sections would need the same parameter.
- **Construction.** One compiler switch per language, introduced in the routing commit.
- **Version.** `Env.NEXT_VERSION = 4` in both languages, with the list of what flips with it in its
  doc comment. Nothing writes or accepts it yet.

## 9. Questions for the owner

1. TagN scope: Share only, every Tag4 integer (expression headers only, or also the constant, env,
   claim and proof headers?), or all three families?
2. Do the object-format byte (`3`), the validator ID and `wireFormatId` change with version 4?
3. Is a hypothesis-carrying endpoint theorem acceptable for the first flip, or must the tiered
   route's `wireWF`/capacity/`SharingWF` theorem land first?
4. Compiler limits for the tiered construction: what headroom, and is a resource failure a hard
   compile error for every caller, including kernel egress and decompile recompile?
5. `metaSharing`: forbid Share there, or define the extended index space (§5.3)?
6. Does the IxVM circuit change in the same PR as the format flip?
7. Version 4 makes the env header byte equal the Check-claim tag (as 3 equals the Eval-claim tag).
   Keep the context-dependent reading, or choose a version that avoids the claim tags?
