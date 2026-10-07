import Ix.CompileCert.Bridge.Term
import Ix.CompileCert.Bridge.Lane
import Ix.CompileCert.Bridge.Denote
import Ix.CompileCert.Bridge.Rules
import Ix.CompileCert.Bridge.Justified
import Ix.CompileCert.Bridge.Induction
import Ix.CompileCert.Bridge.Graded
import Ix.CompileCert.Bridge.Develop
import Ix.CompileCert.Bridge.RoundTrip
import Ix.CompileCert.Bridge.Pair
import Ix.CompileCert.Bridge.Tower

/-!
# M7 X2: the bridge from the compiler's terms to the checker's, and conversion soundness

The proved-once ladder (L2a, L3) states its theorems about the compiler's `Ix.Expr` (through X1's
erasure `er` and conversion `Conv`); the certified checker reads `Kernel.Expr` from the bytes and
its model (`Kernel.Denotes`, `StrongInstalledModel`) interprets the installed, annotated terms.
This package connects the two (PLAN-L2a §1.4 obligation O-B, §2.0 B1/B2):

* **the bridge** (`Bridge/Term.lean`): `bridgeT N L : Tm → Option Kernel.Expr` and
  `bridge N L := bridgeT N L ∘ er`, the reader's form (binders `.never`, constants by `N`, levels
  by `L`); totality (`bridgeT_isSome_iff`), injectivity on erased content (`bridgeT_agree`,
  `bridgeT_injective`), commutation with X1's lift/lower/substitution/spines (`bridgeT_lift`,
  `bridgeT_lower`, `bridgeT_inst`, `bridgeT_appN`), and `Skel` (an annotated term over a bridged
  skeleton) with the same laws;
* **the lane's export** (`Bridge/Lane.lean`): at the lane's naming the bridge is the lane's
  translation `ixToKernel` through the decompiled `Lean.Expr` (`bridge_eq_lane`,
  `bridge_eq_ixToKernel`), hence the reader's entry for every constant W certifies by a direct
  match; for compiler-built constants, `Emitted` (the installed value is an annotation of the
  bridge of the compiler's value), decided per compile by `checkEmitted` (`checkEmitted_sound`),
  proved once by L4's emission theorem;
* **the public reading under the operations** (`Bridge/Denote.lean`): `denotes_lift`,
  `denotes_inst`, `denotes_inst0`, `denotes_lower`, `denotes_levels` (for level-local
  interpretations, `cvalLocal_of_strong`);
* **conversion soundness, rule by rule** (`Bridge/Rules.lean`): `SemEq` with its congruences;
  `semEq_beta` (premise: the argument in the abstraction's domain), `semEq_beta_graph` (graph
  regime: premise from typing), `semEq_eta` (premise: the function in the product at the binder's
  own domain and regime), `semEq_delta` (installed definitions), `semEq_theorem` (installed
  theorems are model facts);
* **justified conversions** (`Bridge/Justified.lean`): X1's `Conv` and its semantics at once,
  every rule with its premise; `justified_sound`;
* **model-level induction** (`Bridge/Induction.lean`): a recursor's typing law at a `Prop` motive
  gives induction over the model's reading of the type for any meta-level predicate (`predMotive`,
  `piR_inhabited`, the inversions of the public reading, `model_telescope_inhabited`), and the
  `Nat` instance `nat_induction`, read off the checker's pinned `Nat.rec`;
* **graded readings and graph-regime β** (`Bridge/Graded.lean`): `Graded` (the public reading's
  `WellDenoted`), stable under lifting and substitution; `RedB` (β at graph-regime binders in every
  context) sound on graded terms with the reduct graded (`RedB.sound`); the annotation lemmas
  (`denotes_of_erasePw_pos`, `bridge_reading_pos`: the bridge's reading is the installed reading in
  the graph regime; `squash_pt`);
* **the worked instance** (`Bridge/Develop.lean`): the β-only development reduces the plain
  substitution (`developB_red`, `instantiateB_red`, X1's `develop_conv` in directed form); on the
  bridges that reduction is the checker's graph-regime β (`TRedB.bridge`), so a graded occurrence and
  its development denote the same (`developB_sem`, `instantiateB_sem`), and an inlined image
  occurrence denotes what the unfolded constant does (`inlineB_sem`), with X1's `inline_conv` on the
  compiler side (`inlineB_justified`);
* **pair projections and ι** (`Bridge/Pair.lean`, `Bridge/Tower.lean`): X1's projection rules from the
  model's pair law (`PairLaw`, `semEq_proj0`, `semEq_proj1`, `Justified.proj0`, `Justified.proj1`),
  which holds in every strong model (`pairLaw_of_tower`, `pairLaw_of_fireOk`): IxC's tower law
  transported to the public reading (`tower_field`, `denotes_proj_ctor`); and ι as a semantic
  equality (`semEq_iota`, the lane's public recursor law);
* **the executable round trip** (`Bridge/RoundTrip.lean`): `bridgeExport` and `bridgeSource` (the
  lane's exports through the compiler's `canonExpr` and the bridge), `bridgeSource_eq`; the ignored
  runner `bridge-roundtrip` compares them on the fixtures (through the bytes and the certified reader)
  and on every Init+Std constant.

Not claimed: `Conv a b → ⟦a⟧ = ⟦b⟧` for an arbitrary derivation (false for untyped β and η in the
set model, `M7-X2-bridge.md` §1.3), and the emission of compiler terms into bytes (L4).
-/
