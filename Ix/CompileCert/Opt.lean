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
import Ix.CompileCert.Opt.Canonicity
import Ix.CompileCert.Opt.AuxCore
import Ix.CompileCert.Opt.O2
import Ix.CompileCert.Opt.ShapeWF

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
| O7–O12 (proof-justified) | `pj_site_none`: they decline with no site | — |
| the engine | `engineN_faithful`, `engineN_site_none`, `engineN_site_iff` | `EngineLaws` (the above, `O2Faithful`, `O11aFaithful`) |
| the hook (`Driver.optLookup`) | `hook_faithful`, `hook_siteStable`, `optLookup_eq` | `EngineLaws` |
| the rewrite (`Translate.rw`, its core `rwP`) | `rwP_faithful`, `rewriteConstP_faithful`; D1: `rwP_lean_name`; totality: `rwP_error` (named failures only), `rwP_mono` (fuel-independent) | `HeadLaws`, `LevelClosed Γ`, `HookFaithful`, `HookSiteStable` |
| canonicity (C-1, C-2) | `O1_O3_disjoint` … `O2_O7_disjoint`, `O1_O6_agree`, `O11a_O2_pattern`, `engine_of_O1`, `engine_of_O3`, `engine_of_O4`, `O1_out`, `argT_congr` | — |

The common part: `rec_sel_conv`, `recOn_sel_conv` (`Rec.lean`), `delta_sel`, `delta_beta` (δ then
β on a telescope, `Basic.lean`, `Subst.lean`), the β-reduct of a telescope as a simultaneous
substitution and its composition (`betaN_eq_msubst`, `betaN_betaN`, `Subst.lean`); abstraction
through the total core copy (`conv_babs`, `er_batchAbstractP`, `AuxCore.lean`) and the successful
`Option` loop invariant (`forIn_option_inv`, `ShapeWF.lean`). `AuxGenCopies` names the remaining
executable-to-core equality hypothesis; fixture comparisons do not prove it.
-/
