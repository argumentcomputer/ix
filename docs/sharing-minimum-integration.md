# Canonical sharing and TagN: integration map

This map says where Ixon v4's two changes, canonical sharing and TagN integers, live in the
code, together with what follows from them: format version 4, the new identifiers, the reader
rule for `Share` inside metadata, and the IxVM circuit codec. For each part it names the Lean,
Rust and IxVM code, the theorems that cover it and the fixtures that pin it. The normative
format is [Ixon](Ixon.md); the decisions behind it are in [`sharing-minimum.md`](sharing-minimum.md)
§12–§13. Code is referred to by file and symbol, not by line.

Decisions in force (`sharing-minimum.md` §12.8, §12.11–§12.16, §13):

- the canonical sharing of a constant is `Ix.Sharing.Exact.canonicalSharingTiered .tagN` (Rust
  `canonical_sharing_tiered(ShareLayout::TagN, ..)`), the only sharing construction of both
  compilers; the heuristic and its proofs are removed;
- TagN with flag widths 0, 2 and 4 replaces Tag0, Tag2 and Tag4 at every site of the grammar and
  is the only integer code; there is one format, with no dual-format gate and no reader for the
  old one;
- references stay backward. The format version is 4, together with the object-format byte (4),
  the resource validator ID (`"ixon-v4/resource-v1"`) and `wireFormatId` (`"ixon-v4"`). The env
  header is TagN(4, `0xE`, version), the byte `0xE4`, read by context;
- compiler limits are a safety net: metering and fail-closed errors stay, the defaults sit far
  above every corpus maximum, and `ix compile --sharing-limits` overrides them;
- a `Share` inside a metadata expression is read in the extended index space of
  `sharing-minimum.md` §13.1; there is no metadata construction;
- the IxVM circuit codec changes in the same PR.

**Status at this head:**

| Item | State |
|---|---|
| TagN at every Lean, Rust and IxVM site; six rungs (widths 1, 2, 3, 4, 5, 9); old encoders, decoders and canonical-integer checks deleted | done |
| Exact-sharing pricing and tie-break bytes at TagN widths; count threshold θmax (finding 7); telescope-spine guard (finding 9) | done |
| Canonical construction as the only compiler route in Lean and Rust; heuristic removed | done (§3.2, §8) |
| Compiler limits as a safety net with a CLI override | done (§8) |
| Proofs: TagN codec, phase-1 minimality, per-phase specifications, wire validity of the output, compiler endpoint theorems over it | done; 225 audit roots (§4) |
| Version 4, object format 4, `ixon-v4` identifiers; readers reject other versions | done (§6) |
| Fixtures and pins regenerated through their producers | done, except the FLT benchmark artifact and a new dated aggregate fixture (§6) |
| `.ixe` caches keyed by the format version | done (§6) |
| Metadata `Share` reader rule in both decompilers | done; no metadata construction (§5.3) |
| IxVM: TagN codec, claim scope bytes, v4 primitive addresses, re-pinned FFT costs | done (§3.1, §6) |
| Lean/Rust differential at the PR commit (Init, Mathlib sample) | pending (§7 risk 1) |
| `ix compile` time and memory before and after | pending (`sharing-minimum-performance.md`) |

<!-- PENDING: [parity] Lean/Rust differential at the PR commit (Init in full, Mathlib sample): mark the status row done with the counts. -->

<!-- PENDING: [measure] `ix compile` wall time and peak RSS before (main) and after (PR commit), Init and Mathlib: mark the status row done and cite the measurement. -->

## 1. Key findings

1. **TagN equals the old codes exactly on its first rung.** `Tag4` values 0–7, `Tag2` values
   0–31 and `Tag0` values 0–127 are written identically in both codes; every larger value
   changes bytes. So every artifact with a count, index or size above those bounds changed, not
   only those with large Share indices.
2. **"No integer gets longer" (§12.12) holds below the fifth rung end.** For values from `R5`
   (4,311,811,080 for `f = 4`, 4,311,826,560 for `f = 0`) up to `2^56`, TagN takes 9 bytes where
   the old code took 6–8. Below `R5`, TagN is never longer, and for `f = 0` it is one byte
   shorter on `[2^24, R4)` and `[2^32, R5)`.
3. **The cost model prices the wire bytes.** `Ix/Sharing/Exact/Basic.lean` defines
   `tag0Size := Ixon.tagNByteWidth 0` and `tag4Size := Ixon.tagNByteWidth 4`, and from them
   `shareWidth`, `sizeInfo` and `exprSize`; Rust `sharing_exact/cost.rs` `tag0_len`/`tag4_len`
   are `TagN::byte_width`. The tie-break header bytes are TagN encodings in both languages (Lean
   `Dictionary.lean` `tag4Bytes` runs `putTagN 4`; Rust `cost.rs` `tag4_bytes_cmp` compares
   `TagN::put` outputs). TagN is a prefix code, so distinct header values still differ inside
   the shorter encoding. The tiered construction serializes its output and fails closed when
   the serialized length differs from its price (`rematerialize`, Rust `tiered.rs`).
4. **There are three codecs.** Besides Lean (`Ix/Ixon.lean`) and Rust (`crates/ixon`), the IxVM
   circuit has its own codec (`Ix/IxVM/IxonDeserialize.lean`, `Ix/IxVM/IxonSerialize.lean`),
   generated into `crates/ixvm-codegen/src/aiur_ixvm.rs` by `lake exe ix codegen`. CI runs
   `lake exe ix codegen --check`.
5. **Metadata does not depend on the primary table's shape.** `CallSiteEntry.collapsed
   sharingIdx` and `callSite.origHead` index `ConstantMeta.metaSharing` directly, arena roots
   follow the unshared logical tree, and every consumer expands `Share` transparently.
   Re-sharing a constant leaves its metadata valid (§5).
6. **The compiler endpoint theorems are stated over the tiered construction.**
   `Ix.Compile.Verify.Tiered.canonicalSharingTiered_format` (`TieredWire.lean`) gives
   `FormatOK sharing roots`: every entry and root `wireWF`, `sharing.size < UInt64.size`, entry
   `k` references only `Share(i)` with `i < k`, roots only `i < sharing.size`. The builder can
   fail, so the run endpoints conclude `SharingRunOK`: the run returns an exactly decodable
   block, or fails with the builder's error (§4).
7. **The certain-stored threshold follows the TagN count growth.** The uniform optimizer
   (`Uniform.lean`, Rust `uniform.rs`) once used θ = 2 because one more table entry grew the
   `Tag0` count by at most a byte. The TagN (`f = 0`) count grows by 4 bytes at 4,311,826,560
   entries (5 → 9). The threshold is θmax = `tag0StepBound n + 1` with `n` the candidate count (2
   below that bound), in both languages, and `tag0BracketStart` returns the TagN rung start.
8. **Telescope headers are subadditive only below `R5`.** The certain-excluded rule assumes
   `tag4Size (a + b) ≤ tag4Size a + tag4Size b`, which fails at `R5` = 4,311,811,080 (`f = 4`).
   `optimizeUniformExpanded` fails closed (`formatBound "telescope spine length"`) on a spine of
   `teleSubaddEnd = Ixon.tagNEnd5 4` nodes or more, and the optimality theorems take the bound
   (`SpinesFit`) from that guard. Rust fails with `FormatBound::TelescopeSpine`.
9. **Claim tags past the first rung changed.** Catalog and Resource claims (flag `0xE`, values 8
   and 9) are written `E8 00` and `E8 01`; the old code wrote `E8 08` and `E8 09`.
10. **Version header aliasing (kept).** The env header and the claim tags share flag `0xE`:
    version 4 (`0xE4`) is the Check-claim tag, as version 3 (`0xE3`) was the Eval-claim tag.
    Readers interpret the byte by context; `docs/Ixon.md` states this next to the claim table.

## 2. Where the plan and the code disagree

| Plan statement (`sharing-minimum.md`) | Code |
|---|---|
| §8.3 "The expression byte grammar need not change." | True for the construction alone. False after §12.12: every integer past the first rung changes, including Share indices ≥ 8. |
| §8.2 "Metadata expressions may also contain Share references …" | The readers implement the extended index space (§5.3); no writer emits a `Share` into `metaSharing`. |
| §2 source map: Lean, Rust, FFI. | Also the IxVM circuit codec and its generated Rust (finding 4). |
| §8.1 "Derive roots from ConstantInfo … do not use out-of-range fallbacks." | Implemented: Lean `buildConstantWithSharing` takes the roots from `constantInfoRootExprs` and writes them back with `withRootExprs`, after checking that the construction returned one root per input root. Rust `apply_sharing_to_*` derive the roots from the payload. |

## 3. Call sites and consumers

### 3.1 The integer code: writers and readers

**Lean** (`Ix/Ixon.lean`): `putTagN f flag value` / `getTagN f` (a `TagN` is `{flag, value}`;
`getTagN0Values` reads a run of `f = 0` values). Every site uses them: expressions (`putExpr`,
`getExprFuel`, `getExprFromTag`), universes (`putUniv`, `getUnivFromTag`), constants and
projections, metadata (`ConstantMeta`, `ExprMeta` arenas), names, environments (`putEnv`,
`getEnv`, `getEnvVerifiedLazy`) and commitments; also `Ix/Claim.lean`, `Ix/AssumptionTree.lean`,
`Ix/Resource/Addressed.lean` and the exact-sharing oracle. Hand-rolled readers and writers
use the same code: `Ixon.DeserCursor.tag0?`, `Ix.DecompileM.BlobCursor.readTagN0` and the
syntax-blob writer `Ix.CompileM.tagN0Bytes`.

**Rust**: `crates/ixon/src/tag.rs` defines only `TagN` (`put`, `get`, `byte_width`,
`end1`..`end5`). Every former `Tag0`/`Tag2`/`Tag4` site in `ixon`, `ix-compile` and `ix-kernel`
uses it: `serialize.rs` (`put_expr`, `get_expr`, constants, `Env::put`, `read_env_header`),
`metadata.rs` (with `deser_tag0`), `proof.rs`, `comm.rs`, `assumption_tree.rs`, `lazy.rs`,
and `decompile.rs` (`read_tagn0`). `get_expr` is the only byte-level expression decoder in Rust;
the other readers (`lazy.rs`, `catalog.rs`, `proof.rs`, `diff.rs`, `resource.rs`) decode
expressions through it and skip constants by their length prefix.

**IxVM**: `Ix/IxVM/IxonDeserialize.lean` reads with `get_tagn0`, `get_tagn2` and `get_tagn4`;
the one-byte case is one narrow row and the longer encodings share `get_tagn_tail` and
`get_tagn_wide`. `Ix/IxVM/IxonSerialize.lean` writes with `put_tagn0/2/4`, `put_tagn_tail` and
`put_tagn_wide`. The circuit rejects what the hosts reject: invalid codes, values reaching
`2^64` and truncation. The claim readers (`run_claim` in `Ix/IxVM/Kernel/Claim.lean`, the
aggregator's CheckEnv parser in `Ix/Aggr/Circuit.lean`) require object format 4; Resource
(`E8 01`) decodes and is rejected explicitly, and Catalog (`E8 00`) has no arm. The
assumption-tree header must be exactly `0xE2`. The circuit reads no `.ixe` header and no
`ConstantMeta`. The generated Rust is `crates/ixvm-codegen/src/aiur_ixvm.rs` and
`aiur_ix_aggr.rs`; the suite `ixvm-tagn` holds the circuit codec to `Ixon.putTagN`/`getTagN`.

`LazyConstant` header peeks (`Ix/Ixon.lean`, `lazy.rs`) need no change: a non-Muts constant
header is a rung-1 TagN, one byte.

### 3.2 The sharing construction and its callers

The construction is `Ix.Sharing.Exact.canonicalSharingTiered` (`Ix/Sharing/Exact.lean` over
`Ix/Sharing/Exact/Tiered.lean`) and Rust `canonical_sharing_tiered`
(`crates/ixon/src/sharing_exact/tiered.rs`), with the deterministic parallel variant
`normalize_constant_sharing_tiered_par` (byte-identical to the sequential path).

**Lean.** `Ix.CompileM.buildConstantWithSharing limits info refs univs : Except CompileError
Constant` takes the roots from `constantInfoRootExprs`, runs `canonicalSharingTiered .tagN`
under `limits`, checks that one root comes back per input root and writes them back with
`withRootExprs`. Every block goes through it:

| Caller | Builds |
|---|---|
| `buildBlockConstant` (limits from `CompileEnv.sharingLimits`) via `finishConstantWithSharing` | definitions, theorems, opaques, axioms, quotients, recursors |
| `finishInductiveFamilyBlock` | standalone inductive families |
| `finishMutualCompilation` → `buildCompiledMutualBlock` | mutual blocks |
| `Ix/AuxGen/CompileAux.lean`, through `buildBlockConstant` | aux-gen standalone and mutual blocks |

**Rust** (`crates/compile/src`). `share_roots` runs the construction on a block's ordered roots.
`apply_sharing_to_{definition,axiom,quotient,recursor}_with_stats` and
`apply_sharing_to_mutual_block` run it under the compiler's limits (`compiler_sharing_limits`:
the defaults with the `IX_SHARING_LIMITS` override); the `_with_limits` variants take explicit
limits (tests, and the FFI parity hook `rs_compiler_sharing_build`).

| Caller | Error handling |
|---|---|
| `compile.rs`: `compile_single_def`, `compile_const_inner`, `compile_mutual`, `compile_mutual_block` | `CompileError`, propagated with `?` |
| `compile/mutual.rs`: `compile_aux_block_with_rename` | `CompileError`, propagated |
| `kernel_egress.rs`: `egress_muts_block`, `egress_standalone` | mapped to the egress `String` errors |
| `decompile.rs`: `roundtrip_block` | `recompile_sharing_error` → `DecompileError::BadConstantFormat`; the recompiled address must equal `Named.original`, so the recompile uses exactly the compile route |

Errors: resource exhaustion is `CompileError.resourceLimit` (it names the limit and the
override); every other construction failure is `CompileError.sharingConstruction`. There is no
fallback.

### 3.3 Share consumers that are independent of the encoding

These expand `Share(i)` against the decoded table and need no change for TagN: Lean
`Ix/DecompileM.lean` (`resolveShareIn`, `collectIxonTelescopeExpandingShares`),
`Ix/Tc/Ingress.lean`, `Ix/Tc/IngressMeta.lean` (fuel-bounded expansion that reports a cycle),
`Ix/SemanticContract.lean` (`containsIxon`), `Ix/Resource/Addressed.lean` (offsets Share into a
program-wide table); Rust `crates/compile/src/decompile.rs`, `crates/kernel/src/ingress.rs`,
`crates/compile/src/semantic_contract.rs`, `crates/ixon/src/resource.rs`,
`resource/addressed.rs` and `diff.rs`. The IxVM ingress and conversion modules also consume the
table logically.

### 3.4 Pricing and tie-break bytes in the construction

| Site | What it prices |
|---|---|
| `Ix/Sharing/Exact/Basic.lean`: `tag4Size`, `tag0Size`, `shareWidth`, `sizeInfo`, `exprSize`; Rust `sharing_exact/cost.rs`: `tag4_len`, `tag0_len` | headers, counts, refs/univs indices and Share widths at TagN widths |
| `Ix/Sharing/Exact/Uniform.lean`: `tag0BracketStart`, `tag0StepBound`, `teleSubaddEnd`; Rust `uniform.rs`: `tag0_bracket_start`, `tag0_step_bound` | count brackets at the TagN rung starts, θmax (finding 7), the spine guard (finding 8) |
| `Ix/Sharing/Exact/Tiered.lean`: `ShareLayout.widthAt` (`tagNWidth`), `layoutBytes`, `rematerialize`; Rust `tiered.rs`: `tagn_width` | the real Share width at each index; the serialized length must equal the price |
| `Ix/Sharing/Exact/Dictionary.lean`: `tag4Bytes` (cut, inline and Share option bytes); Rust `cost.rs`: `tag4_bytes_cmp` | tie-break bytes as TagN encodings; a Share option loses every tie, since inline and cut options start with a flag nibble below `0xB` |

## 4. Verification theorems

Everything below builds in `lake build IxCompileVerify`, whose trust audit
(`Ix/Compile/Verify/Audit/Statements.lean`, 225 roots) checks each root's axioms and the sorry
frontier. `lake lint` builds it as well.

- **TagN** (`Ix/Compile/Verify/TagN.lean`): the byte specification `tagNBytes`, the writer and
  reader laws `putTagN_writes` and `getTagN_reads`, canonicity and injectivity
  (`runGetExact_getTagN_eq`, `putTagN_inj`) and the two rejection laws
  (`getTagN_rejects_code`, `getTagN_rejects_overflow`). The codec theorems of `Codec.lean`,
  `ExprCodec.lean`, `ExprSpineCodec.lean` and the constant codecs (`ConstantCodec.lean`,
  `ConstantTablesCodec.lean`, `NonrecursiveConstantCodec.lean`, `RecursorConstantCodec.lean`,
  `MutualConstantCodec.lean`) are stated over these facts; TagN is bijective, so no
  canonical-integer side conditions remain.
- **Size model**: `SharingExact.lean` proves `exprSize_eq_serExpr` (the TagN-priced size is the
  serialized length of every `wireWF` expression) and `serConstant_size_decomposition`;
  `UniformLength.lean` proves `optimizeUniform_variableBytes` (phase 1's serialized length is its
  model length when every index has width `w`).
- **Construction**: phase 1 in `UniformOptimality.lean` (`optimizeUniform_minimum`,
  `optimizeUniform_least`, over the `Uniform*` modules), phase 2 in `TieredTier.lean`
  (`allocate_spec`, `firstTier_spec`) and `TieredGuard.lean` (`allocate_optimal`,
  `phase3_le_phase1`), phase 3 in `TieredPhase3.lean` (`materializeTable_min`,
  `rematerialize_spec`), the selection in `TieredSelect.lean` (`canonicalTieredCore_select`),
  determinism and re-expansion in `TieredIdem.lean`, structural IDs in `SharingExactCanon.lean`
  (`canonicalize_det`), and the format facts in `TieredWire.lean` (`FormatOK`,
  `canonicalSharingTiered_format`, `canonicalSharingTieredTable_format`).
- **Compiler endpoints** (`CompileSharingCodec.lean` and the `Compile*Codec.lean` modules):
  `buildConstantWithSharing_wireWF` takes the entries' and roots' `wireWF` and the table
  capacity from `FormatOK`. `SharingRunOK limits run` states the outcome of a run whose only
  possible failure is the builder: either `run = .ok (result, state')` with
  `BlockResultCodecWF result` (the block is `wireWF` and its bytes decode to it exactly), or
  `run = .error err` where the builder returns `.error err` on some payload and tables. Under
  `SharingSucceeds` only the first case remains. Every `*_codecWF` endpoint concludes
  `SharingRunOK compileEnv.sharingLimits (run ..)`. `FormatOK`'s backwardness conjuncts can
  discharge `DecodeCtx.SharingWF` (`Ix/Compile/Verify/Catalog.lean`); no endpoint states it.

Not machine-checked: that the final tiered result's layout length equals its serialized length
(the construction checks it at run time), phase-2 optimality for tables of more than 1,032
entries, and any global minimum (`docs/Ixon.md`, "What is proved, and what is not").

`IxTcVerify` mentions none of these names, but its `native_decide` serde fixtures
(`Ix/Tc/Verify/Ingress/SerializedBoolean.lean`, `Ingress/LiteralBlobs.lean`,
`Inductive/ConcreteFixture.lean`, `Inductive/EnumerationFixture.lean`) recompute bytes with the
current codec.

## 5. Metadata

### 5.1 Index spaces

- **Separate namespaces.** `CallSiteEntry.collapsed sharingIdx` indexes
  `ConstantMeta.metaSharing`. Both compilers start it at 0 per constant: Lean `buildCallSite`
  numbers collapsed arguments from the current surgery table, which `takeSurgerySharing` drains
  into `metaSharing` per constant; Rust `compile.rs` drains its `surgery_sharing` into
  `meta.meta_sharing` the same way. `callSite.origHead.0` also indexes `metaSharing`.
- **No offset.** Collapsed and `origHead` indices are never offset by the primary table length.
- **Kernel ingress ignores it.** `Ix/Tc/IngressMeta.lean` and Rust `crates/kernel/src/ingress.rs`
  do not read `metaSharing`.

### 5.2 Metadata payloads contain no primary Share references

`metaSharing` entries are raw compiled expressions (Lean `compileExprSurgical`, Rust
`compile_expr`). Share is produced only by the sharing construction, which runs on the roots
after metadata is built. Their Ref/univ indices point into the block's primary `refs`/`univs`
tables, which the construction does not change, so no remapping is needed when the primary table
changes.

### 5.3 Metadata `Share`: the extended index space

The rule is `sharing-minimum.md` §13.1. With `p` primary entries (for a projection, those of its
`Muts` block) and `q` metadata entries, a `Share(i)` inside `metaSharing[j]` denotes primary
entry `i` when `i < p` (shares nested in that entry stay primary) and `metaSharing[i − p]` when
`p ≤ i < p + j`; anything else is rejected. A `Share` in a primary expression always denotes a
primary entry. `CallSiteEntry.collapsed sharingIdx` and `origHead = some (sharingIdx, _)` index
`metaSharing` directly and read that entry in its own scope.

| | Lean | Rust |
|---|---|---|
| scopes and resolution | `Ix.DecompileM.ShareScope` (`primary`, `metaEntry j`), `resolveShareIn` | `decompile::ShareScope` (`Primary`, `Meta { entry }`) |
| table check on load | `validateMetaSharing` (in `withFreshBlock`) | `validate_meta_sharing` (in `load_meta_extensions`, used by `decompile_const`, `decompile_projection` and `roundtrip_block`) |
| error | `DecompileError.invalidMetaShareIndex idx entry primaryLen metaLen constant` | `DecompileError::InvalidMetaShareIndex { idx, entry, primary_len, meta_len, constant }` |
| semantic-contract scan | `Ix.SemanticContract.containsIxon` with the decompiler's scopes | `semantic_contract::contains_ixon` |

The error has tag 11 in both languages. The table check is iterative, does not expand shares and
reports the first violation in entry order, then left-to-right pre-order. A malformed primary
`Share` found by the semantic-contract scan is reported as `InvalidShareIndex`. The IxVM circuit,
kernel ingress and egress, `diff.rs` and the resource validators do not read `metaSharing`
contents, and no writer emits a metadata `Share`. Two pre-existing limits remain: a call site
nested inside a metadata expression may reference any `metaSharing` entry, including its own,
and neither decompiler checks that primary entries reference only earlier entries, so a
malformed table of either kind can make decompilation loop instead of failing.

### 5.4 How per-occurrence arena roots survive

Arena nodes mirror the **unshared** logical tree; a Share is transparent and keeps the same
arena index (`Ix/Tc/IngressMeta.lean`, `Ix/DecompileM.lean`, Rust `decompile.rs`,
`ingress.rs`). Call-site `canonMeta` is distributed over the canonical App telescope after
expanding Shares along the spine (Lean `collectIxonTelescopeExpandingShares`; the Rust
decompiler and kernel ingress do the same), and eta call sites strip `nSynth` lambdas,
expanding Shares at each step. Universe patches are keyed by arena index. Root indices
(`typeRoot`, `valueRoot`, `ruleRoots`) are arena indices. So any change of which subterms are
shared, or of where a Share cuts a telescope, leaves arena roots, binder data, call-site
surgery, universe patches and `Named.original` valid, and a metadata-only edit cannot change
anonymous bytes (metadata is not part of `Constant`).

## 6. Version, identifiers, fixtures and caches

Policy (`docs/Ixon.md`, "Environment Serialization"): any byte change bumps the version,
readers reject a mismatch, there is no back-compat reading, and `.ixe` files are regenerated.

| Item | Lean | Rust | Value |
|---|---|---|---|
| format version | `Ixon.Env.VERSION` | `Env::VERSION` | 4; `.ixe` header `0xE4` |
| object-format byte (claims, proofs, catalog manifests) | `Ixon.Env.OBJECT_FORMAT` | `Env::OBJECT_FORMAT` | 4 |
| wire format ID | `Ixon.wireFormatId` | `WIRE_FORMAT_ID` | `"ixon-v4"` |
| resource validator ID (profile prefix `<ID>/profile\0`) | `Ix.Resource.validatorId` | `resource::addressed::VALIDATOR_ID` | `"ixon-v4/resource-v1"` |
| catalog manifest version | `Ix.Catalog.VERSION` | `CATALOG_VERSION` | 2 (unchanged) |
| text grammar version | `Ixon.Syntax.VERSION` | `syntax::VERSION` | 3 (unchanged; it covers no integer bytes) |

The env readers (Lean `getEnv`, `getEnvVerifiedLazy`; Rust `read_env_header`, used by
`Env::get`, `get_anon`, `get_anon_mmap` and `parse_lazy_index`) reject any other version with
"expected .ixe format version 4, got N — recompile the artifact". The in-circuit claim readers
require object format 4 (§3.1).

**Fixtures and pins.** Each is regenerated by its producer, never edited by hand:

| Fixture or pin | Location | Checked by | Producer |
|---|---|---|---|
| handoff set | `Tests/Fixtures/ixon-v4/handoff/` (`accepted.ixe`, `rejected-local-escape.ixe`, `profile.bin`, `accepted.claim`, `manifest.json`) | `ixon-v4-tests` (byte equality); `ix-kernel` `resource::tests::cross_language_consumer_handoff` | `lake exe ixon-v4-tests --export-handoff` |
| claims, addressed resources, resource cases | `Tests/Fixtures/ixon-v4/{claims,addressed,resource}.tsv` | `ixon-v4-tests` (whole files); `ixon` `proof::tests::v4_claim_fixtures_and_strict_scope`, `resource::addressed::tests::canonical_cross_language_fixtures` | `lake exe ixon-v4-tests --export-fixtures` |
| canonical primitive addresses | `Tests/Fixtures/ixon-v4/primitives.tsv`, `crates/common/src/prim_addrs.rs` (`PrimAddrs::new`), `Ix/Tc/Primitive.lean`, the IxVM literals in `Ix/IxVM/Kernel/*.lean` | `lake exe ixon-v4-primitives` (file equality), suites `primitive-address-parity` and `prim-addrs` (IxVM literals) | `lake exe ixon-v4-primitives` |
| catalog claim digest | `Tests/Ix/Claim.lean`, `crates/ixon/src/proof.rs` (`catalog_claim_wire_bytes_pinned`) | `claim` suite, `ixon` tests | the serializers' output |
| env-bytes hash | `crates/compile/src/graph.rs` | `ix-compile` `graph::tests::setup_scan_preserves_compiled_fixture_bytes` | rerun and pin |
| independent expression bytes | `Tests/Fixtures/ixon-v4/expressions.txt` | `ixon-v4-tests`; `ixon` `v4_independent_golden_expressions` | written by hand from the specification (`text.tsv` holds no bytes) |
| IxVM FFT-cost pins | `Tests/Ix/IxVM.lean` (kernel checks), the shard pin in `Tests/Main.lean` | ignored runner `ixvm` | rerun and pin |

Not regenerated, because their inputs are not available in the development environment:

- `Benchmarks/Kernel/AnthropicFLT/cases.json` pins a 30 GB v3 artifact
  (`flt-after-source-hints-1.ixe`) by sha256. Its addresses must be re-derived from that
  artifact recompiled at v4; until then the harness rejects the old artifact by hash, and a v4
  binary rejects its header, so it cannot be consumed silently.
- The aggregate-proof fixture `Tests/Fixtures/Aggregate/mathlib-2026-09-03` is kept as a
  historical v3 fixture; `stage2FixturePinnedAndFenced` (`Tests/AggrSemantics.lean`) pins its
  wrapper and requires its rejection with "claim: unsupported object format". A dated v4 fixture
  is produced on a large machine (compile, profile, shard, prove, aggregate, verify).

**Caches and on-disk artifacts.** The TruthMines piece-cache key includes `ixe=<VERSION>`
(`Benchmarks/TruthMinesSpec/Main.lean`); `ix bench` keeps closure shards under
`<dir>/ixe-v<VERSION>/` (`Ix/Cli/BenchCmd.lean`); `tc-parity.ixe` is recompiled when its header
carries another version (`Tests/Ix/Tc/ParityEnv.lean`). `comppoly.ixe` and `tauceti.ixe` are
user-built and gitignored; a stale one fails with the version error. CI caches `.ixe` files by
commit. To regenerate an `.ixe`: `lake exe ix compile <file>.lean --out <x>.ixe`.

## 7. Risks

1. **Lean/Rust disagreement of tiered outputs** would fork the address space. Fixtures,
   generated inputs and the compiler route agree byte for byte (`exact-sharing-ffi`), and so did
   the corpus differentials on Init and a Mathlib sample at earlier commits
   (`sharing-minimum-performance.md`). The final differential runs at the PR commit.
2. **Resource exhaustion in the compiler.** The construction fails closed; a constant over the
   limits is a compile error for every caller (compile, aux-gen, kernel egress, decompile
   recompile). The defaults sit far above every corpus maximum (Mathlib: largest MSS table
   21,461 entries; 81,833 candidates), and `--sharing-limits` raises them. Lean and Rust count
   work differently, so equal limits can succeed in one language and fail in the other; every
   observed case was a Lean-only exhaustion that matched Rust once raised.
3. **Model length versus wire length** is not one theorem for the final result; the
   construction compares the two on every output and fails closed (§4).
4. **Width jumps.** TagN grows by one byte per rung end except by four at `R5`. The count
   threshold (finding 7) and the telescope-spine guard (finding 8) cover the two arguments that
   needed it; any new argument that assumes a header grows by at most one byte per boundary is
   unsound from `R5` on.
5. **Recompile invariant.** Rust `roundtrip_block` requires recompiled addresses to equal
   `Named.original`; the recompile calls the compile path's `apply_sharing_*` functions under
   the compiler's limits, so it follows the route.
6. **Header aliasing** (finding 10), kept by decision.
7. **Stale artifacts.** Caches are keyed by the format version (§6). Artifacts pinned by hash
   from outside the repository (the FLT benchmark) must be regenerated by their owners.
8. **Metadata reader gaps** (§5.3): cyclic tables can make the decompilers loop. They predate
   this work and affect only malformed input.

<!-- PENDING: [parity] Lean/Rust differential at the PR commit (Init in full, Mathlib sample, corpora compiled at that commit): add its counts to risk 1. -->

## 8. Implementation notes

**Integer code.** One header byte, then 0, 1, 2, 3, 4 or 8 bytes; rung ends `tagNEnd1..tagNEnd5`
(Lean) / `TagN::end1..end5` (Rust); the 8-byte rung rejects values reaching `2^64`. For
`f = 4` every code is valid; for `f = 0, 2`, codes `c ≥ 4` are rejected. Deleted: the
`Tag0`/`Tag2`/`Tag4` structures and their `put`/`get`, `Serialize Tag4`, the three "noncanonical
… integer" checks, the Share-codec threading (`ShareCodec`, `putShare`, `getExprHeader`), and
the Rust `*_with` codec variants with their FFI hooks. The generic little-endian helpers stay
(`Ixon.putU64TrimmedLE`/`getU64TrimmedLE`, Rust `u64_put_trimmed_le`/`u64_get_trimmed_le`).

**Construction and route.** `ShareLayout` has the single constructor `tagN`
(`ShareLayout.wire = .tagN`). Phase 1 runs at each width `w ∈ {1, 2, 3}` and the cheapest
candidate in real bytes wins (ties to the lower width); the per-width candidate in the theorems
is `tieredAtWidth`. Removed with the heuristic: `Ix/Sharing.lean`, `crates/ixon/src/sharing.rs`,
`Ix/Compile/Verify/Sharing.lean` and its two audit roots (`rewriteWithSharing_wireWF`,
`applySharing_wireWF`), the heuristic seeds of the exact optimizers (the unshared length is the
initial bound), the `sharing` suite and the heuristic FFI hooks. Experiment hooks used during
development (forced phase-1 width, a fourth phase-1 candidate, the MSS inspector, the
`sharing_corpus` modes `--layout`, `--width-experiment` and `--mss-*`) are removed; the
forced-width entry point survives only as a crate-private test helper.

**Limits.** Lean `Ix.Sharing.Exact.Limits` and Rust `ExactSharingLimits` hold the defaults
(`docs/Ixon.md`, "Canonical construction"). `Limits.withOverrides` and
`ExactSharingLimits::with_overrides` parse one grammar; keys of the other language are accepted
and ignored. `ix compile --sharing-limits` and `ix compile-lean --sharing-limits` validate the
override and publish it through `IX_SHARING_LIMITS`, which the Lean drivers
(`CompileEnv.sharingLimits`) and Rust `compiler_sharing_limits` read; an invalid value fails
every block that shares.

**Test oracles.** The width-state search (`Ix.Sharing.Exact.Search`, `search.rs`, the `exact`
corpus mode), the tiny exhaustive oracle (`Exact.Oracle`, `oracle.rs`), the subset-enumeration
reference of phase 1 (`uniformSubsetSearch`, `uniform_subset_search`) and the MSS reference
encoding (`mss.rs`, test-only) are labelled as test oracles; the compiler path never calls them.

**Tests.**

- `exact-sharing` (`Tests/Ix/Sharing{Exact,Uniform,Tiered}.lean`): the plan's fixtures with
  exact bytes, the uniform optimizer against the width-state reference, first-tier brute force,
  idempotence, the limits and their overrides.
- `exact-sharing-ffi` (`Tests/Ix/SharingExactFFI.lean`): Lean and Rust bytes on fixtures,
  generated inputs, Share-bearing constants with tables up to 66,600 entries (Shares in the 4-,
  5- and 9-byte rungs) and the compiler route. With `IX_SHARING_CORPUS=<file.ixe>` it runs over
  every constant of an `.ixe` (modes `tiered-tagN`, `uniform-w<k>`, `exact`;
  `IX_SHARING_CORPUS_MODES`, `IX_SHARING_CORPUS_SELECT`, `IX_SHARING_CORPUS_LIMIT`).
- `ixon` (`tagNUnits`: expected encodings, rejection vectors, rung-end vectors, boundary
  round trips), with the same vectors in Rust `tag.rs`; `ixvm-tagn` for the circuit.
- `ixon-v4-tests` and `ixon-v4-primitives` (§6); the Rust `sharing_exact` tests, including
  parallel against sequential byte identity.
- Benchmarks and studies: `sharing-study` (`Benchmarks/SharingStudy.lean`: stored, canonical,
  unshared and MSS bytes, and the `--meta` scanner), `uniform-hard`
  (`Benchmarks/UniformHard.lean`), and the Rust example `sharing_corpus`
  (`crates/ixon/examples/sharing_corpus.rs`).

<!-- PENDING: [verify] CI-equivalent gates at the PR commit (lake build; lake build IxCompileVerify IxTcVerify; lake test and the ignored suites; lake test -- cli; ixon-v4-tests and ixon-v4-primitives; cargo test --workspace; cargo clippy -D warnings; cargo fmt --check; lake lint; lake exe ix codegen --check): record the results here. -->

## 9. Owner decisions on the questions of this map

1. Scope of TagN: all three families, every header including claim, proof, comm and
   assumption-tree headers (§12.12). Applied.
2. Object-format byte, validator ID, `wireFormatId`: bumped with the version to `4`,
   `"ixon-v4/resource-v1"`, `"ixon-v4"` (§6). Applied.
3. Endpoint theorem: the real `wireWF` + capacity + backwardness theorem
   (`canonicalSharingTiered_format`), with the endpoints stated over it (§4). Applied.
4. Compiler limits: a safety net with a CLI override (§7 risk 2). Applied.
5. `metaSharing`: the extended index space of `sharing-minimum.md` §13 (§5.3). Readers applied;
   no construction.
6. IxVM: updated in this PR (§3.1). Applied.
7. Header aliasing: kept; the env header is TagN(4, `0xE`, version), `0xE4` for v4
   (finding 10).
8. Cost-model repricing: TagN widths in both languages (finding 3, §3.4). Applied.
