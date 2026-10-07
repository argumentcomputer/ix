import Ix.CompileCert.Bridge.Term
import Ix.CompileCert.Bridge.Lane
import Ix.CompileCert.Bridge.Denote
import Ix.CompileCert.Bridge.Rules
import Ix.CompileCert.Bridge.Justified
import Ix.CompileCert.Bridge.Induction

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
  `Nat` instance `nat_induction`, read off the checker's pinned `Nat.rec`.

Not claimed: `Conv a b → ⟦a⟧ = ⟦b⟧` for an arbitrary derivation (false for untyped β and η in the
set model, `M7-X2-bridge.md` §1.3), and the emission of compiler terms into bytes (L4).
-/
