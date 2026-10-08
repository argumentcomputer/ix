import Ix.CompileCert.Opt.Basic
import Ix.CompileCert.Opt.Subst
import Ix.CompileCert.Opt.Shape
import Ix.CompileCert.Opt.Rec
import Ix.CompileCert.Opt.O1
import Ix.CompileCert.Opt.O6
import Ix.CompileCert.Opt.O3
import Ix.CompileCert.Opt.O4
import Ix.CompileCert.Opt.Total
import Ix.CompileCert.Opt.Guard
import Ix.CompileCert.Opt.Engine
import Ix.CompileCert.Opt.Rewrite
import Ix.CompileCert.Opt.RewriteTotal
import Ix.CompileCert.Opt.RewriteInst
import Ix.CompileCert.Opt.LevelTransport
import Ix.CompileCert.Opt.LevelSemantics
import Ix.CompileCert.Opt.LevelRefinement
import Ix.CompileCert.Opt.ExpansionOrigin
import Ix.CompileCert.Opt.SourceScope
import Ix.CompileCert.Opt.SourceInstallScope
import Ix.CompileCert.Opt.IngestionArity
import Ix.CompileCert.Opt.IngestionLookup
import Ix.CompileCert.Opt.Canonicity
import Ix.CompileCert.Opt.AuxCore
import Ix.CompileCert.Opt.O2
import Ix.CompileCert.Opt.ShapeWF
import Ix.CompileCert.Opt.ShapeRange

/-!
# M7 L3-def: the definitional passes, proved once over the compiler's code

The definitional optimisation passes of Pass 3 (`Ix/Compile/Pass/Opt/{O1,…,O6,O11a}.lean`, design
document §1.5) replace an occurrence `a.{us} a₁ … a_m` of an image-kind auxiliary of a changed
block by an Ix auxiliary of Pass 2 applied to (a selection of) the same arguments. Each module's
docstring calls the pass *definitional* and lists its conversion steps. This package restates
each docstring as a theorem about the compiler's own function (unfolded; no copy), in X1's
conversion `Conv` on erased terms (`Ix.CompileCert.Conv`):

* **faithfulness**: `P.apply env o = some e → ExprConv Γ e (occTerm o)`, for every `Γ` that has
  the rules the docstring's conversion uses — the *laws* (`RecLaw`, `RecOnLaw`, `IxRecOnLaw`,
  `CasesOnLaw`, …: δ of the image-kind head to its image or to Lean's construction over images,
  δ of Pass 2's auxiliary to the same construction over the canonical recursor, the shape read
  off the image). Every law is a named hypothesis. The per-occurrence O2 theorem additionally
  assumes `O2Ready`; discharging the general engine law requires capture-avoiding helpers;
* **the side condition** `P.Side env o` (the docstring's list) and its necessity (`P_side`).

The theorems, by pass:

| pass | faithfulness | laws |
|---|---|---|
| O1 (`rec`/`recOn`, permuted block) | `O1_faithful` | `RecLaw`, `RecOnLaw`, `IxRecOnLaw` |
| O6 (`rec`/`recOn`, selection image) | `O6_faithful` | the same |
| O2 (`rec`, split block), per occurrence | `O2_faithful_on` | `RecLawI`, `O2MinorLaw`, `AuxGenCopies`, `BAbsClosed Γ`, `O2Ready` (`PrefixFresh` and `RecurConvFrom`) |
| O3 (`casesOn`, no collapse) | `O3_faithful` | `CasesOnLaw`, `Γ.InstClosed` |
| O4 (`below`, `brecOn`, `.go`, `.eq`, selection) | `O4_faithful` | `O4Law` (`RecConsSquare`, `BRecOnSquare`, `EqPIrrel`), `Γ.InstClosed` |
| totality of O1, O3, O4, O6 | `O1_none_iff`, `O3_none_iff`, `O4_none_iff`, `O6_none_iff`: a decline is exactly a failed side condition (`O1_of_side` …) | `ShapesWF` (the shapes within Lean's ranges) for O1, O4, O6 |
| shape ranges | `readShape_wf`, `optBlockOf_wf`, `optBlocks_wf`, `shapesWF_optLookup` | none; `ShapesWF` holds for the actual driver environment |
| O11a selection | `engine_of_O11a`, `engineN_O11a_fuel_eq`, `engineFull_of_O11a` | an O11a success; this is selection/fuel independence, not its conversion law |
| O7–O12 (proof-justified) | `pj_site_none`: they decline with no site | — |
| the engine | `engineN_faithful`, `engineN_site_none`, `engineN_site_iff` | `EngineLaws` (the above, `O2Faithful`, `O11aFaithful`) |
| the hook (`Driver.optLookup`) | `hook_faithful`, `hook_siteStable`, `optLookup_eq` | `EngineLaws` |
| the rewrite (`Translate.rw`, its core `rwP`) | `rwP_faithful`, `rewriteConstP_faithful`; D1: `rwP_lean_name`; totality: `rwP_error` (named failures only), `rwP_mono` (fuel-independent) | `HeadLaws`, `LevelClosed Γ`, `HookFaithful`, `HookSiteStable` |
| instantiated expansion lifting | `spineP_faithful_inst`, `rwP_faithful_inst`, `rewriteConstP_faithful_inst`; lookup reduction: `expansionOfP_instLookup_of_stored` | `HeadLaws`, `HookFaithful`, `HookSiteStable`, and pointwise computed/raw expansion conversion; deriving this intermediate relation from source remains open |
| stored expansion origin | `expansion_stored_origin`, `expansion_stored_property` | rewrite-enabled values are exactly queried definitions/theorems; deriving source scope and referenced-spine arity remains open |
| independent source universe scope | `SourceScope.exportSourceExpr_scope`, `SourceScope.exportSourceEntry_defn_scope`, `SourceScope.exportSourceEntry_thm_scope` | scope follows from the actual independent source-export guards; source ingestion correspondence and referenced-spine arity remain open |
| installed original-source universe scope | `SourceScope.definition_scope_of_installation`, `SourceScope.theorem_scope_of_installation` | scope follows for each original definition/theorem in an existing `SourceInstallation` inventory; obtaining the receipt and proving ingestion correspondence and referenced-spine arity remain open |
| actual ingestion/export counts | `IngestionArity.canonConst_params_size`, `IngestionArity.source_constant_export`, `IngestionArity.source_constant_inferred_arity` | declaration telescope count for every `CanonState`; export-spine length and arity from the existing kernel reference inference; cache-content, source-lookup and annotation correspondence remain open |
| captured original-source lookups | `IngestionLookup.captured_lookup`, `IngestionLookup.closed_reference_lookup`, `IngestionLookup.closed_reference_canon_arity` | exact supplied lookup and ingestion count follow from the existing capture/closure witness; hash-keyed compiler lookup, cache-content and annotation correspondence remain open |
| universe-map transport | `substLevel_empty_params`, `substLevel_empty_univs`, `substLevel_paramFree`; `Conv.mapC_viaConv`, `conv_substLevels_viaConv` | exact scalar normalization facts; mapped-rule conversion remains an explicit intermediate obligation, not a discharged source law |
| semantic level bridge | `normalizeLevel_paramFree_eval`, `substLevel_paramFree_eval`; `checkedIxLevelEq_eval`, `normalizeLevel_eval_of_checked` | numeric fragment proved for every successful evaluation with arbitrary caches; the general independent-check relation is intermediate, and polymorphic source-derived soundness remains open |
| polymorphic scalar runtime | `LevelRefinement.normalizeLevel_evalP`, `substLevel_evalP`, `substLevel_compose_of_source_export_evalP`, `substLevel_params_of_source_export` | actual structural smart/lookup semantics with arbitrary cached fields; source-export scope is derived internally, while ingestion, referenced-spine arity and the general term-conversion bridge remain open |
| canonicity (C-1, C-2) | `O1_O3_disjoint` … `O2_O7_disjoint`, `O1_O6_agree`, `O11a_O2_pattern`, `engine_of_O1`, `engine_of_O3`, `engine_of_O4`, `O1_out`, `argT_congr` | — |

The common part: `rec_sel_conv`, `recOn_sel_conv` (`Rec.lean`), `delta_sel`, `delta_beta` (δ then
β on a telescope, `Basic.lean`, `Subst.lean`), the β-reduct of a telescope as a simultaneous
substitution and its composition (`betaN_eq_msubst`, `betaN_betaN`, `Subst.lean`); abstraction
through the total core copy (`conv_babs`, `er_batchAbstractP`, `AuxCore.lean`) and the successful
`Option` loop invariant (`forIn_option_inv`, `ShapeWF.lean`). `ShapeRange.lean` derives argument ranges from a closed
image telescope; image construction must still supply that closedness. `AuxGenCopies` names the remaining
executable-to-core equality hypothesis; fixture comparisons do not prove it.
-/
