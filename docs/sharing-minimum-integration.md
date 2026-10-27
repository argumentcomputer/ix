# Canonical sharing and TagN: integration map

This map says where Ixon v4's two changes, canonical sharing and TagN integers, live in the
code, together with what follows from them: format version 4, the new identifiers, the reader
rule for `Share` inside metadata, and the IxVM circuit codec. For each part it names the Lean,
Rust and IxVM code, the theorems that cover it and the fixtures that pin it. The normative
format is [Ixon](Ixon.md); the decisions behind it are in [`sharing-minimum.md`](sharing-minimum.md)
§12–§14. Code is referred to by file and symbol, not by line.

Decisions in force (`sharing-minimum.md` §12.8, §12.11–§12.16, §13–§14):

- the canonical sharing of a constant is `Ix.Sharing.Exact.canonicalSharingTiered .tagN` (Rust
  `canonical_sharing_tiered(ShareLayout::TagN, ..)`), the only sharing construction of both
  compilers, under `sharing-k16-greedy-v1` (K = 16); the heuristic and its proofs
  are removed. The old unbounded exact search is a reference route;
- TagN with flag widths 0, 2 and 4 replaces Tag0, Tag2 and Tag4 at every site of the grammar and
  is the only integer code; there is one format, with no dual-format gate and no reader for the
  old one;
- references stay backward. Checked payloads and claims retain object format 4,
  the resource validator ID (`"ixon-v4/resource-v1"`) and `wireFormatId` (`"ixon-v4"`).
  The environment envelope is v4 (`0xE4`), or v5 (`0xE5`) with a role binding;
  the extension does not change the checked payload grammar;
- compiler limits are a safety net: metering and fail-closed errors stay, the defaults sit far
  above every corpus maximum, and `ix compile --sharing-limits` overrides them;
- a `Share` inside a metadata expression is read in the extended index space of
  `sharing-minimum.md` §13.1; there is no metadata construction;
- the IxVM circuit codec changes in the same PR.

**Current implementation map:**

| Item | State |
|---|---|
| TagN at every Lean, Rust and IxVM site; six rungs (widths 1, 2, 3, 4, 5, 9); old encoders, decoders and canonical-integer checks deleted | done |
| Sharing pricing and tie-break bytes at TagN widths; count threshold θmax (finding 7); telescope-spine guard (finding 8) | implemented; guards can still refuse |
| Canonical construction as the only compiler route in Lean and Rust; heuristic removed | done (§3.2, §8) |
| Compiler limits as a safety net with a CLI override | done (§8) |
| Successful-run proofs for the production family, input expansion, format and builder codec; audited fast twins | proved with the conditions described in §4; totality, output-domain closure and cost remain follow-ups |
| Checked object format 4 and `ixon-v4` identifiers; v4/v5 environment envelopes | implemented; see [Ixon](Ixon.md#environment) for the envelope distinction |
| `.ixe` caches keyed by the format version | done (§6) |
| Metadata `Share` reader rule in both decompilers | done; no metadata construction (§5.3) |
| IxVM TagN codec, claim scope bytes and v4 primitive addresses | implemented (§3.1, §6); the historical gate record below does not establish current FFT cost-pin acceptance |
| Corpus parity and performance | [K16 production evidence](sharing-minimum.md#144-evidence-and-release-gates); older exact-route measurements below are historical |

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
   the shorter encoding. That the price of the tiered output is its serialized length is a
   theorem (`canonicalSharingTiered_serialized`); Rust also serializes the returned candidate
   and compares the lengths at run time (`tiered.rs`, check 9).
4. **There are three codecs.** Besides Lean (`IxC/Ixon/Codec.lean`, with the metadata and
   environment codecs in `Ix/Ixon.lean`) and Rust (`crates/ixon`), the IxVM
   circuit has its own codec (`Ix/IxVM/IxonDeserialize.lean`, `Ix/IxVM/IxonSerialize.lean`),
   generated into `crates/ixvm-codegen/src/aiur_ixvm.rs` by `lake exe ix codegen`. CI runs
   `lake exe ix codegen --check`.
5. **Metadata does not depend on the primary table's shape.** A Pass 3 record's `_ix.inline`
   indexes `ConstantMeta.metaSharing` directly (before CQ3.6 the call-site `sharingIdx` and
   `origHead` did the same), arena roots follow the unshared logical tree, and every consumer expands `Share` transparently.
   Re-sharing a constant leaves its metadata valid (§5).
6. **The compiler's sharing builder theorems are stated over the tiered construction.**
   `Ix.Sharing.Verify.Tiered.canonicalSharingTiered_format` (`TieredWire.lean`) gives
   `FormatOK sharing roots`: every entry and root `wireWF`, `sharing.size < UInt64.size`, entry
   `k` references only `Share(i)` with `i < k`, roots only `i < sharing.size`. The builder can
   fail, so the singleton-driver tail concludes `SharingRunOK`: the run returns an exactly decodable
   block, or fails with an error the builder returns on some payload (§4).
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

**Lean** (`IxC/Ixon/Codec.lean`; metadata, names and environments in `Ix/Ixon.lean`): `putTagN f flag value` / `getTagN f` (a `TagN` is `{flag, value}`;
`getTagN0Values` reads a run of `f = 0` values). Every site uses them: expressions (`putExpr`,
`getExprFuel`, `getExprFromTag`), universes (`putUniv`, `getUnivFromTag`), constants and
projections, metadata (`ConstantMeta`, `ExprMeta` arenas), names, environments (`putEnv`,
`getEnv`, `getEnvVerifiedLazy`) and commitments; also `Ix/Claim.lean`, `Ix/AssumptionTree.lean`,
`Ix/Resource/Addressed.lean` and the exact-sharing oracle. Hand-rolled readers and writers
use the same code: `Ixon.DeserCursor.tagN0?`, `Ix.DecompileM.BlobCursor.readTagN0` and the
syntax-blob writer `Ix.CompileM.tagN0Bytes`.

**Rust**: `crates/ixon/src/tag.rs` defines only `TagN` (`put`, `get`, `byte_width`,
`end1`..`end5`). Every former `Tag0`/`Tag2`/`Tag4` site in `ixon`, `ix-compile` and `ix-kernel`
uses it: `serialize.rs` (`put_expr`, `get_expr`, constants, `Env::put`, `read_env_header`),
`metadata.rs` (with `deser_tagn0`), `proof.rs`, `comm.rs`, `assumption_tree.rs`, `lazy.rs`,
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
under `limits` and writes the roots back with `withRootExprs`, which delegates to the checked
`Ix.Sharing.Exact.withRoots` (one root per input root, no positional fallback). Every block goes
through it:

| Caller | Builds |
|---|---|
| `buildBlockConstant` (limits from `CompileEnv.sharingLimits`) via `finishConstantWithSharing` | definitions, theorems, opaques, axioms, quotients, recursors |
| `finishInductiveFamilyBlock` | standalone inductive families |
| `finishMutualCompilation` → `buildCompiledMutualBlock` | mutual blocks |
| `Ix/AuxGen/CompileAux.lean`, through `buildBlockConstant` | aux-gen standalone and mutual blocks |

**Rust** (`crates/compile/src`). `share_roots` runs the construction on a block's ordered roots.
`apply_sharing_to_{definition,axiom,quotient,recursor,mutual_block}_with_limits` run it under
the limits they are given and return the shared `Constant`. The compiler passes the limits it
read once per run (`CompileState::sharing_limits`, from `compiler_sharing_limits`: the defaults
with the `IX_SHARING_LIMITS` override); the FFI parity hook `rs_compiler_sharing_build` passes
explicit limits.

| Caller | Error handling |
|---|---|
| `compile.rs`: `compile_single_def`, `compile_const_inner`, `compile_mutual`, `compile_mutual_block` | `CompileError`, propagated with `?` |
| `compile/mutual.rs`: `compile_aux_block_with_rename` | `CompileError`, propagated |
| `kernel_egress.rs`: `egress_muts_block`, `egress_standalone` | mapped to the egress `String` errors, naming the constant (`egress '<name>': …`) |
| `decompile.rs`: `roundtrip_block` | `AuxGenError::Recompile`, which keeps the compile error and its category and names the constant and step (`recompile of '<name>' (sharing): …`); the recompiled address must equal `Named.original`, so the recompile uses exactly the compile route |

Errors: resource exhaustion is `CompileError.resourceLimit` (it names the limit and the
override); every other construction failure is `CompileError.sharingConstruction`.
The initial K16 gate selects the exact or greedy family before search; a
failure does not switch families or emit a best-so-far result.

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
| `Ix/Sharing/Exact/Tiered.lean`: `ShareLayout.widthAt` (`tagNWidth`), `layoutBytes`, `rematerialize`; Rust `tiered.rs`: `tagn_width` | the real Share width at each index; the price is the serialized length (a theorem in Lean, a run-time check in Rust) |
| `Ix/Sharing/Exact/Dictionary.lean`: `tag4Bytes` (cut, inline and Share option bytes); Rust `cost.rs`: `tag4_bytes_cmp` | tie-break bytes as TagN encodings; a Share option loses every tie, since inline and cut options start with a flag nibble below `0xB` |

## 4. Verification theorems

The current theorem inventory and limitations are in
[Ixon, "What is proved, and what is not"](Ixon.md#what-is-proved-and-what-is-not).
The source map is:

| Contract | Source and conditions |
| --- | --- |
| TagN and constant codec | `IxC/Ixon/Verify/{Basic,TagN,Constant}.lean` and the supporting codecs; wire bounds and exact decoding remain explicit |
| Actual input expansion and output meaning | `IxSharingVerify/CanonicalMeaning.lean`, `FamilyDomain.lean`, `CanonicalProduction.lean`; successful production runs preserve the ordered input expressions, including the input-to-DAG bridge |
| K16 family minimum, format and serialized length | `IxSharingVerify/CanonicalProduction.lean`; the successful production entry supplies the domain and check premises; phase 1 minimizes within the fixed family, not over every subset of a large component |
| Representation congruence and idempotence | `IxSharingVerify/FamilyIdempotence.lean`; congruence requires the same unfolded roots, non-expression fields, refs and universes, and both normalizations must succeed at the same configuration, layout and limits |
| Compatibility with the old exact route | `IxSharingVerify/FamilyExactConstant.lean`; every initial component at all three widths has at most 16 members, the old route uses `uniformSubsetSearch = false`, and both public wrappers succeed with the same limits |
| Compiler builder and stored-byte decoding | `IxSharingVerify/Builder.lean`; `buildConstantWithSharing_wireWF_headers` requires wire-safe header fields and reference/universe tables plus builder success; `finishConstantInfoWithSharing_run_codecWF` retains its wire-safe payload/table premises and allows a builder error |
| Compiled implementations equal their specifications | audited `@[csimp]` equalities, including `Ix/Sharing/FamilyNormalizeArea.lean`; equality covers complete results, charges and errors, and the guarded area evaluator falls back to the reference evaluator without changing the family |

The compatibility row compares
`Ix.Sharing.Exact.Reference.normalizeConstantSharingTiered` with the production
`Ix.Sharing.Exact.normalizeConstantSharingTiered` under its listed conditions.
It does not assert unchanged bytes for the whole K16 cutover; §14.4 of
`sharing-minimum.md` records the changed corpus constants and their attribution.

`lake build --wfail IxSharingVerify` builds these sharing proofs and audits;
`lake -d IxC build --wfail` builds the codec proofs with the certified checker.
`Audit/Statements.lean` fixes each root's axiom set, `Audit/SorryFrontier.lean`
rejects `sorryAx` in sharing declarations, and `Audit/CompiledCode.lean`
requires every compiler-path `csimp` equality to be an audit root. The
builder's stored-byte roots are included: hash finalization uses
`Address.admissionHash`, with no `native_decide` axiom or hash-injectivity
premise. The module map in `Ix/Sharing/Exact.lean` identifies the specification
and compiled implementation of each stage.

These are successful-run contracts. Old-route success does not imply
new-route success at an arbitrarily tight budget; idempotence does not
silently supply second-run success. Totality on the stated framed-input
domain, output-domain closure and cost bounds remain follow-up work
([§14.3](sharing-minimum.md#143-proof-scope-and-follow-up)). There is no global
minimum claim or phase-2 optimum for tables above 1,032 entries. Rust has
differential evidence, not a universal refinement proof. Sharing preserves
the unfolded Ixon expressions; these results do not complete the Source
acceptance or compiler value-preservation composition.

The former `Ix.Tc.Verify` tree, whose `native_decide` serde fixtures recomputed bytes with the
codec, is retired ([kernel](kernel.md), "Removal ledger").

## 5. Metadata

### 5.1 Index spaces

- **Separate namespaces.** A Pass 3 decompile record's `_ix.inline` indexes
  `ConstantMeta.metaSharing`, which both compilers start at 0 per constant. (Before CQ3.6 the
  call-site surgery's `CallSiteEntry.collapsed sharingIdx` and `callSite.origHead.0` indexed it
  too.)
- **No offset.** Record indices are never offset by the primary table length.
- **Kernel ingress ignores it.** `Ix/Tc/IngressMeta.lean` and Rust `crates/kernel/src/ingress.rs`
  do not read `metaSharing`.

### 5.2 Metadata payloads contain no primary Share references

`metaSharing` entries are raw compiled expressions (the source occurrences of Pass 3 records,
compiled by Lean `Ix.CompileM` and Rust `compile_expr`). Share is produced only by the sharing construction, which runs on the roots
after metadata is built. Their Ref/univ indices point into the block's primary `refs`/`univs`
tables, which the construction does not change, so no remapping is needed when the primary table
changes.

### 5.3 Metadata `Share`: the extended index space

The rule is `sharing-minimum.md` §13.1. With `p` primary entries (for a projection, those of its
`Muts` block) and `q` metadata entries, a `Share(i)` inside `metaSharing[j]` denotes primary
entry `i` when `i < p` (shares nested in that entry stay primary) and `metaSharing[i − p]` when
`p ≤ i < p + j`; anything else is rejected. A `Share` in a primary expression always denotes a
primary entry. A record's `_ix.inline` indexes `metaSharing` directly and reads that entry in its
own scope.

| | Lean | Rust |
|---|---|---|
| scopes and resolution | `Ix.DecompileM.ShareScope` (`primary`, `metaEntry j`), `resolveShareIn` | `decompile::ShareScope` (`Primary`, `Meta { entry }`) |
| table check on load | `validateMetaSharing` (in `withFreshBlock`) | `validate_meta_sharing` (in `load_meta_extensions`, used by `decompile_const`, `decompile_projection` and `roundtrip_block`) |
| error | `DecompileError.invalidMetaShareIndex idx entry primaryLen metaLen constant` | `DecompileError::InvalidMetaShareIndex { idx, entry, primary_len, meta_len, constant }` |
| semantic-contract scan | `Ix.SemanticContract.containsIxon` with the decompiler's scopes | `semantic_contract::contains_ixon` |

The error has tag 11 in both languages. The table check is iterative, does not expand shares and
reports the first violation in entry order, then left-to-right pre-order. A malformed primary
`Share` found by the semantic-contract scan is reported as `InvalidShareIndex`; the record replay
uses the scan to refuse a record over a compiled term that carries a contract. The IxVM circuit,
kernel ingress and egress, `diff.rs` and the resource validators do not read `metaSharing`
contents, and no writer emits a metadata `Share`. The table check is linear in the DAG size of
the table: each shared node is visited once. Its scope must be distinguished from the
certified reader and from other host traversals:

| Entry | Current checks and boundary |
| --- | --- |
| Certified IxC admission | `IxC/Kernel/Ixon/Reader.lean`, `MemberReader.mk'` builds each primary sharing entry against earlier entries only; `convExpr` returns a malformed-reference error when a self/forward reference is used. An unused failing entry need not be forced. This entry does not read optional `ConstantMeta` or replay `_ix.inline` records. |
| Host metadata-Share expansion | `validateMetaSharing` / `validate_meta_sharing` checks every metadata table entry, rejecting self, forward and out-of-range metadata Shares before decompilation. This does not validate the primary sharing table or the metadata arena/replay graph. |
| Raw host primary-Share expansion | `Ix.DecompileM.resolveShareIn`, Rust `BlockCache::resolve_share` and Rust kernel `ingress.rs`'s expression conversion check primary index range but have no backwardness/progress guard on that traversal. For example, `sharing = [Share(0)]` resolves `Share(0)` back to itself. These host paths are distinct from the certified IxC reader. |
| Host metadata replay | The arena codec represents arbitrary UInt64 child references with wrapping deltas (`Ix/Ixon.lean`, `crates/ixon/src/metadata.rs`). Its canonical byte encoding does not establish acyclicity. The decompilers follow `Mdata.child` and range-checked `_ix.inline` replay targets without a general active-cycle check; the metadata-Share bound does not constrain those edges. |

These remaining host traversal limits follow from the current resolver/replay
code; they are not a blanket claim that all cyclic metadata bypasses checks.
Rust kernel `LocalDefnDependencies::validate` separately rejects local safe
definition cycles. That guard does not validate Share or metadata-replay edges.

### 5.4 How per-occurrence arena roots survive

Arena nodes mirror the **unshared** logical tree; a Share is transparent and keeps the same
arena index (`Ix/Tc/IngressMeta.lean`, `Ix/DecompileM.lean`, Rust `decompile.rs`,
`ingress.rs`). Universe patches are keyed by arena index. Root indices
(`typeRoot`, `valueRoot`, `ruleRoots`) are arena indices. So any change of which subterms are
shared, or of where a Share cuts a telescope, leaves arena roots, binder data, Pass 3
records, universe patches and `Named.original` valid. Editing only the optional
`ConstantMeta` sidecar leaves anonymous bytes fixed. Semantic source-contract
mdata is different: compilation lowers it into `Constant`'s binder fields,
which are part of anonymous identity (`Ix/SemanticContract.lean`).

## 6. Version, identifiers, fixtures and caches

The checked payload grammar and the metadata envelope have separate versions
([Ixon, "Environment Serialization"](Ixon.md#environment-serialization)).
The sharing-rule revision is separate again (§14 of `sharing-minimum.md`).

| Item | Lean | Rust | Value |
|---|---|---|---|
| environment envelope version | `Ixon.Env.envelopeVersion` | `Env::envelope_version` | 4 (`0xE4`) without a role binding; otherwise 5 (`0xE5`) |
| object-format byte (claims, proofs, catalog manifests) | `Ixon.Env.OBJECT_FORMAT` | `Env::OBJECT_FORMAT` | 4 |
| wire format ID | `Ixon.wireFormatId` | `WIRE_FORMAT_ID` | `"ixon-v4"` |
| resource validator ID (profile prefix `<ID>/profile\0`) | `Ix.Resource.validatorId` | `resource::addressed::VALIDATOR_ID` | `"ixon-v4/resource-v1"` |
| catalog manifest version | `Ix.Catalog.VERSION` | `CATALOG_VERSION` | 2 (unchanged) |
| text grammar version | `Ixon.Syntax.VERSION` | `syntax::VERSION` | 3 (unchanged; it covers no integer bytes) |

The env readers (Lean `getEnv`, `getEnvVerifiedLazy`; Rust `read_env_header`, used by
`Env::get`, `get_anon`, `get_anon_mmap` and `parse_lazy_index`) accept envelopes
4 and 5 and reject other versions. Original records and original-hint overrides
belong to the v5 metadata extension, outside the checked constant set. Claim and catalog readers
reject another object format with "claim: unsupported object format N, expected 4 — regenerate
the claim" ("catalog: …" likewise). The in-circuit claim readers require object format 4
(§3.1). The scratch files of the `ixon-v4-*` executables live under `$IX_IXON_V4_DIR` (default
`/tmp`; `Tests/Ix/IxonV4Paths.lean`).

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
(`Benchmarks/TruthMinesSpec/Main.lean`); `tc-parity.ixe` is recompiled when its header
carries another version (`Tests/Ix/Tc/ParityEnv.lean`). `comppoly.ixe` and `tauceti.ixe` are
user-built and gitignored; a stale one fails with the version error. CI caches `.ixe` files by
commit. To regenerate an `.ixe`: `lake exe ix compile <file>.lean --out <x>.ixe`.

## 7. Risks

1. **Lean/Rust disagreement of tiered outputs** would fork the address space. Fixtures,
   generated inputs and the compiler route agree byte for byte (`exact-sharing-ffi`). With Rust
   in its checked mode, all stored constants of Init (56,783) and of Init+Std (100,277) compiled
   on Lean 4.34.0 give identical bytes, as did all of Init (56,622) and a Mathlib sample of
   20,284 constants on Lean 4.33.1, with no resource exhaustion on either side; and the
   merge-queue suite `lake test -- --ignored compile` requires the Lean and Rust compilers to
   write identical environments (238,574 constants on Lean 4.34.0)
   (`sharing-minimum-performance.md`).
2. **Resource exhaustion in the compiler.** The construction fails closed; a constant over the
   limits is a compile error for every caller (compile, aux-gen, kernel egress, decompile
   recompile). The defaults sit far above every corpus maximum (Mathlib: largest MSS table
   21,461 entries; 81,833 candidates; largest table-count knapsack 9,959,424 cells against a
   `knapsack_cells` default of 2^28), and `--sharing-limits` raises them. Neither language limits
   the candidate count on this path. Lean and Rust count work differently (Rust's `work` charges
   the evaluations actually done: one evaluation of the whole table in one pass, one per prefix
   otherwise), so equal limits can succeed in one language and fail in the other; every observed
   case was a Lean-only exhaustion that matched Rust once raised.
3. **The pointer cache is not evidence of term equality.** Successful input expansion is
   covered by the proofs (§4), including structural confirmation of cache hits. The
   unsafe pointer key remains an explicit implementation boundary in the audit.
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
8. **Host traversal limits** (§5.3): raw host primary-Share expansion and metadata
   arena/replay traversal still lack general cycle guards. The certified IxC reader
   uses only earlier primary entries, and host metadata-Share self/forward references
   already fail their dedicated check. These are separate entrypoint contracts.
9. **Length range.** General Rust costs and signed deltas still use checked 128-bit
   arithmetic, so overflow can refuse where Lean's `Nat` succeeds. The earlier initial-
   classification overflow on doubling DAGs is repaired: all 11 fixtures, including
   depths 127–256, have Rust/Lean byte parity. That bounded predicate repair does not
   prove the remaining general arithmetic bounds (§14.3–§14.4 of `sharing-minimum.md`).
10. **Rust's default mode checks built expressions for the returned candidate only.** A wrong
    length of another candidate would change the selection without an error. The checked mode
    (`ExactSharingLimits::full_check`) builds and checks all three; over all of Init and Mathlib
    it gives the default mode's output.

## 8. Implementation notes

**Integer code.** One header byte, then 0, 1, 2, 3, 4 or 8 bytes; rung ends `tagNEnd1..tagNEnd5`
(Lean) / `TagN::end1..end5` (Rust); the 8-byte rung rejects values reaching `2^64`. For
`f = 4` every code is valid; for `f = 0, 2`, codes `c ≥ 4` are rejected. Deleted: the
`Tag0`/`Tag2`/`Tag4` structures and their `put`/`get`, `Serialize Tag4`, the three "noncanonical
… integer" checks, the Share-codec threading (`ShareCodec`, `putShare`, `getExprHeader`), and
the Rust `*_with` codec variants with their FFI hooks, and the Lean little-endian helpers
`putU64TrimmedLE`/`getU64TrimmedLE`/`u64ByteCount` (the TagN code uses `putU64TrimmedLEAux`
and `getU64TrimmedLEAux`; Rust keeps `u64_put_trimmed_le`/`u64_get_trimmed_le`).

**Construction and route.** `ShareLayout` has the single constructor `tagN`
(`ShareLayout.wire = .tagN`). Phase 1 runs at each width `w ∈ {1, 2, 3}` and the cheapest
candidate in real bytes wins (ties to the lower width); the per-width candidate in the theorems
is `tieredAtWidth`. Removed with the heuristic: `Ix/Sharing.lean`, `crates/ixon/src/sharing.rs`,
`Ix/Compile/Verify/Sharing.lean` and its two audit roots (`rewriteWithSharing_wireWF`,
`applySharing_wireWF`), the heuristic seeds of the exact optimizers (the unshared length is the
initial bound), the `sharing` suite and the heuristic FFI hooks. Experiment hooks used during
development (forced phase-1 width, a fourth phase-1 candidate, the MSS inspector, the
`sharing_corpus` modes `--layout`, `--width-experiment` and `--mss-*`) are removed; the
forced-width entry point survives only as a crate-private test helper. Also removed: the Rust
`apply_sharing_with_stats` and `apply_sharing_to_*_with_stats` wrappers,
`SingletonSharingResult`, `MutualBlockSharingResult`, `block_stats`/`BlockSizeStats`,
`optimize_dag`, `optimize_dag_uniform`, `optimize_sharing_uniform_reference` and `tier2_end`.
Renamed: `check_canonical_sharing` → `check_exact_minimum` (Lean `checkCanonicalSharing` →
`checkExactMinimum`, `CanonicalCheck` → `ExactMinimumCheck`).

**Rust checks and metering.** The module documentation of `crates/ixon/src/sharing_exact/tiered.rs`
("Checks") lists every check. In the default mode every limit and every phase-1 to phase-3 length
check applies to all three candidates, and the checks on built expressions run for the returned
candidate; the checked mode (`ExactSharingLimits::full_check`: unit tests, the FFI parity hooks,
`sharing_corpus --full-check`) runs them for all three. Phase 1 is a dry run that builds no
expressions; phase 3 evaluates the whole table once when the order is closed under stored
descendants and per prefix otherwise (an App spine of 1,288 nodes ending in a stored term reaches
the per-prefix path; it is a fixture in both languages, 7,105 bytes). The cargo feature
`ixon/sharing-profile` (off by default, compiled in CI) adds phase timers.

**Limits.** Lean `Ix.Sharing.Exact.Limits` and Rust `ExactSharingLimits` hold the defaults
(`docs/Ixon.md`, "Canonical construction"). `Limits.withOverrides` (`parseLimitValue`) and
`ExactSharingLimits::with_overrides` (`parse_limit_value`) parse one grammar: values are ASCII
digits, `2^k` or `max`; items and keys are trimmed of spaces, tabs, line feeds and carriage
returns only; keys of the other language are accepted and ignored. One list of 35
specifications pins both (`LIMIT_SPEC_PARITY` in `crates/ixon/src/sharing_exact/tests.rs`,
`limitSpecParity` in `Tests/Ix/SharingExact.lean`). `ix compile --sharing-limits` and
`ix compile-lean --sharing-limits` validate the override and publish it through
`IX_SHARING_LIMITS`. The Lean compiler reads it through
`Ix.Cli.driverOptionsFromEnv`, carried in `CompileEnv.sharingLimits`; the Rust
compile and regeneration paths use `CompileState::sharing_limits`. Lean's
`decompileEnvFullParallel` reads stored originals and ignores its historical
sharing-limits parameter; it does not invoke the sharing construction.

**Test oracles.** The width-state search (`Ix.Sharing.Exact.Search`, `search.rs`, the `exact`
corpus mode), the tiny exhaustive oracle (`Exact.Oracle`, `oracle.rs`), the subset-enumeration
reference of phase 1 (`uniformSubsetSearch`, `uniform_subset_search`) and the MSS reference
encoding (`mss.rs`, test-only) are labelled as test oracles; the compiler path never calls them.

**Tests.**

- `exact-sharing` (`Tests/Ix/Sharing{Exact,Uniform,Tiered}.lean`): the plan's fixtures with
  exact bytes, the uniform optimizer against the width-state reference, first-tier brute force,
  idempotence, pointer-layout independence, the tiered path at scale (tables above 1,032
  entries, the 1,288-node spine, the parallel widths) and under each production limit, and the
  limit grammar (`limitSpecParity`).
- `exact-sharing-ffi` (`Tests/Ix/SharingExactFFI.lean`): Lean and Rust bytes on fixtures,
  generated inputs, Share-bearing constants with tables up to 66,600 entries (Shares in the 4-,
  5- and 9-byte rungs), the re-normalization of 119 table-carrying inputs, malformed tables, and
  the compiler route. With `IX_SHARING_CORPUS=<file.ixe>` it runs over
  every constant of an `.ixe` (modes `tiered-tagN`, `uniform-w<k>`, `exact`;
  `IX_SHARING_CORPUS_MODES`, `IX_SHARING_CORPUS_SELECT`, `IX_SHARING_CORPUS_LIMIT`).
- `ixon` (`tagNUnits`: expected encodings, rejection vectors, rung-end vectors, boundary
  round trips), with the same vectors in Rust `tag.rs`; `ixvm-tagn` for the circuit.
- `ixon-v4-tests` and `ixon-v4-primitives` (§6); the Rust `sharing_exact` tests, including
  parallel against sequential byte identity.
- Benchmarks and studies: `sharing-study` (`Benchmarks/SharingStudy.lean`: the rebuild check,
  round trip, unshared size and the MSS baseline), `lean-sharing-prof <ixe> full|split|hash
  [select-file]` (`Benchmarks/LeanSharingProf.lean`, the Lean construction's phase profile),
  `uniform-hard` (`Benchmarks/UniformHard.lean`), and the Rust example `sharing_corpus`
  (`crates/ixon/examples/sharing_corpus.rs`; `--full-check`, `--sharing-limits SPEC`, and
  `--check-sequential`, which compares the parallel and sequential paths under the run's
  limits).

### Historical gates before the K16 cutover

Recorded on Lean 4.33.1 at the head of the earlier canonical-sharing change,
before it was merged with the certified checker. These are historical
commands and counts, not gates on the current PR head. `IxTcVerify` and
`IxCompileVerify` have since been retired; §4 maps their retained sharing
and codec contracts. K16 evidence is recorded in
[§14.4](sharing-minimum.md#144-evidence-and-release-gates). The old run reported:

- Lean: `lake build --wfail -v`; `lake test --wfail` (primary tier, 3,957 checks); `lake lint --
  --wfail -v`; `lake build IxTcVerify` (audits of 2,034, 1 and 7 roots, sorry frontier clean);
  `lake build IxCompileVerify --wfail` (250 roots; sorry frontier clean for `Ix.Compile.Verify`
  and `Ix.Sharing`; all 19 `@[csimp]` theorems are roots); `lake exe ix codegen --check`; `diff
  lean-toolchain Benchmarks/Compile/lean-toolchain`; `lake test --wfail -- cli`; `lake test
  --wfail -- ffi`; `lake exe ixon-v4-primitives` then `lake exe ixon-v4-tests --primitives`
  (2,052 golden checks, 4,054 VM checks, 3,540 addressed interfaces validated).
- Rust: `cargo fmt --all --check`; `cargo clippy --release --workspace --all-targets --features
  ix-ffi/parallel,ix-ffi/net,ix-ffi/test-ffi,ixon/sharing-profile -- -D warnings`; `cargo check`
  with the same features; `cargo test --release --workspace` (1,716 passed, 20 ignored); `cargo
  deny check`.
- Merge-queue partitions run locally: `tc-unit`; the compile-pipeline partition
  (`--ignored rust-canon-roundtrip serial-canon-roundtrip parallel-canon-roundtrip graph-cross
  condense-cross rust-serialize ixon-corpus rust-decompile validate-aux aux-gen-diff
  decompile-diff`); and `--ignored compile` (Lean and Rust compile all 237,295 constants of the
  test environment; constants, metadata and serialized environments are identical), run on the
  tree just before the final cleanup and documentation commits. The other ignored partitions
  (`--ignored decompile`, the misc partition with the `ixvm` runner, the Tc ignored suites) are
  run by the merge queue.

## 9. Owner decisions on the questions of this map

1. Scope of TagN: all three families, every header including claim, proof, comm and
   assumption-tree headers (§12.12). Applied.
2. Object-format byte, validator ID, `wireFormatId`: bumped with the version to `4`,
   `"ixon-v4/resource-v1"`, `"ixon-v4"` (§6). Applied.
3. Endpoint theorem: the real `wireWF` + capacity + backwardness theorem
   (`canonicalSharingTiered_format`), with the endpoints stated over it (§4). Applied; the
   compiler's sharing builder theorems remain over it, and the per-declaration endpoints
   are retired with the compiler-correctness proofs.
4. Compiler limits: a safety net with a CLI override (§7 risk 2). Applied.
5. `metaSharing`: the extended index space of `sharing-minimum.md` §13 (§5.3). Readers applied;
   no construction.
6. IxVM: updated in this PR (§3.1). Applied.
7. Header aliasing: kept; the env header is TagN(4, `0xE`, version), `0xE4` for v4
   (finding 10).
8. Cost-model repricing: TagN widths in both languages (finding 3, §3.4). Applied.
