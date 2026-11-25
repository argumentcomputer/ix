import IxCC.Fir.Proof.Shape
import IxCC.Fir.Proof.Rep

/-! Required axiom fences for the shape certificate at Fir (`plans/ONE-PIPELINE.md`,
section 2): the vocabulary's facts (`IxCC.Shape.Basic`), the checker's soundness
(`Fir.Proof.Shape`: `checkSound`, `codeSound` and the lemmas they rest on, `check_checked` from
the Boolean checker to the rules), and the representation derived from the shapes
(`Fir.Proof.Rep.ofShapes_*`: its facts from `checkSound` alone). Expected messages are preserved
verbatim. -/

/-! The vocabulary: weakening's two facts, and the native functions at a word. -/

/-- info: 'IxCC.Shape.Shape.le_any' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Shape.Shape.le_any

/-- info: 'IxCC.Shape.Shape.le_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Shape.Shape.le_refl

/-- info: 'IxCC.Shape.Shape.word_slot' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Shape.Shape.word_slot

/-- info: 'IxCC.Shape.Shape.word_elemKind' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Shape.Shape.word_elemKind

/-- info: 'IxCC.Shape.Shape.word_immediate' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Shape.Shape.word_immediate

/-- info: 'IxCC.Shape.Shape.word_rep' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Shape.Shape.word_rep

/-- info: 'IxCC.Shape.Shape.word_le_natLt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Shape.Shape.word_le_natLt

/-- info: 'IxCC.Shape.Shape.natLt_le_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Shape.Shape.natLt_le_word

/-! The checker's soundness: `CheckSound`, `CodeSound`, the evaluator invariant with a join stack,
the lemmas (`LeSound`, `PrimOkSound`, right-hand sides), and the Boolean checker. -/

/-- info: 'IxCC.Fir.Proof.Shape.checkSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.Shape.checkSound

/-- info: 'IxCC.Fir.Proof.Shape.codeSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.Shape.codeSound

/-- info: 'IxCC.Fir.Proof.Shape.evalSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.Shape.evalSound

/-- info: 'IxCC.Fir.Proof.Shape.leSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.Shape.leSound

/-- info: 'IxCC.Fir.Proof.Shape.valOk_word_inv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.Shape.valOk_word_inv

/-- info: 'IxCC.Fir.Proof.Shape.primOkSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.Shape.primOkSound

/-- info: 'IxCC.Fir.Proof.Shape.rhsSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.Shape.rhsSound

/-- info: 'IxCC.Fir.Proof.Shape.primShape_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.Shape.primShape_ok

/-- info: 'IxCC.Fir.Proof.Shape.check_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.Shape.check_checked

/-- info: 'IxCC.Fir.Proof.Shape.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.Shape.check_sound

/-- info: 'IxCC.Fir.Proof.Shape.check_codeSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.Shape.check_codeSound

/-! The representation derived from the shapes. -/

/-- info: 'IxCC.Fir.Proof.Rep.ofShapes_valOk' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.Rep.ofShapes_valOk

/-- info: 'IxCC.Fir.Proof.Rep.ofShapes_envOk' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.Rep.ofShapes_envOk

/-- info: 'IxCC.Fir.Proof.Rep.ofShapes_word' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.Rep.ofShapes_word

/-- info: 'IxCC.Fir.Proof.Rep.ofShapes_runSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.Rep.ofShapes_runSound

/-- info: 'IxCC.Fir.Proof.Rep.ofShapes_codeSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.Rep.ofShapes_codeSound
