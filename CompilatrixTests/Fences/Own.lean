import Compilatrix.Own.Immortal
import Compilatrix.Own.Semantics

/-! Required axiom fences for the Phase 1 Own fragment (M1.F5): the checker
accepts exactly the image of the immortal embedding
(`checkImmortal_iff`, `immortal_erase`, `checkImmortal_immortal`), erasure
inverts the embedding (`erase_immortal`), their structural lemmas, and the
termination facts of the Own semantics. Expected messages are preserved
verbatim. -/

/-- info: 'Compilatrix.Own.Code.size_pos' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Code.size_pos

/-- info: 'Compilatrix.Own.lookupJ_weight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.lookupJ_weight

/-- info: 'Compilatrix.Own.JEntry.jweight_after' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.JEntry.jweight_after

/-- info: 'Compilatrix.Own.map_map_of_all' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.map_map_of_all

/-- info: 'Compilatrix.Own.mapAll_map' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Own.mapAll_map

/-- info: 'Compilatrix.Own.eraseRhs_immRhs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.eraseRhs_immRhs

/-- info: 'Compilatrix.Own.eraseCode_immCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.eraseCode_immCode

/-- info: 'Compilatrix.Own.eraseAlts_immAlts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.eraseAlts_immAlts

/-- info: 'Compilatrix.Own.eraseOpt_immOpt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.eraseOpt_immOpt

/-- info: 'Compilatrix.Own.zip_map_fst_snd' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.zip_map_fst_snd

/-- info: 'Compilatrix.Own.eraseFun_immFun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.eraseFun_immFun

/-- info: 'Compilatrix.Own.mapAll_true' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Own.mapAll_true

/-- info: 'Compilatrix.Own.erase_immortal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.erase_immortal

/-- info: 'Compilatrix.Own.map_pair_snd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.map_pair_snd

/-- info: 'Compilatrix.Own.okRhs_immRhs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.okRhs_immRhs

/-- info: 'Compilatrix.Own.okCode_immCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.okCode_immCode

/-- info: 'Compilatrix.Own.okAlts_immAlts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.okAlts_immAlts

/-- info: 'Compilatrix.Own.okOpt_immOpt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.okOpt_immOpt

/-- info: 'Compilatrix.Own.okFun_immFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.okFun_immFun

/-- info: 'Compilatrix.Own.checkImmortal_immortal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.checkImmortal_immortal

/-- info: 'Compilatrix.Own.immRhs_eraseRhs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.immRhs_eraseRhs

/-- info: 'Compilatrix.Own.immCode_eraseCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.immCode_eraseCode

/-- info: 'Compilatrix.Own.immAlts_eraseAlts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.immAlts_eraseAlts

/-- info: 'Compilatrix.Own.immOpt_eraseOpt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.immOpt_eraseOpt

/-- info: 'Compilatrix.Own.map_fst_zip' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.map_fst_zip

/-- info: 'Compilatrix.Own.map_plain_zip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.map_plain_zip

/-- info: 'Compilatrix.Own.immFun_eraseFun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.immFun_eraseFun

/-- info: 'Compilatrix.Own.immortal_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.immortal_erase

/-- info: 'Compilatrix.Own.checkImmortal_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.checkImmortal_iff
