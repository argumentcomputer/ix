import IxCC.Own.Immortal
import IxCC.Own.Semantics

/-! Required axiom fences for the Phase 1 Own fragment (M1.F5): the checker
accepts exactly the image of the immortal embedding
(`checkImmortal_iff`, `immortal_erase`, `checkImmortal_immortal`), erasure
inverts the embedding (`erase_immortal`), their structural lemmas, and the
termination facts of the Own semantics. Expected messages are preserved
verbatim. -/

/-- info: 'IxCC.Own.Code.size_pos' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Code.size_pos

/-- info: 'IxCC.Own.lookupJ_weight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.lookupJ_weight

/-- info: 'IxCC.Own.JEntry.jweight_after' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.JEntry.jweight_after

/-- info: 'IxCC.Own.map_map_of_all' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.map_map_of_all

/-- info: 'IxCC.Own.mapAll_map' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Own.mapAll_map

/-- info: 'IxCC.Own.eraseRhs_immRhs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.eraseRhs_immRhs

/-- info: 'IxCC.Own.eraseCode_immCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.eraseCode_immCode

/-- info: 'IxCC.Own.eraseAlts_immAlts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.eraseAlts_immAlts

/-- info: 'IxCC.Own.eraseOpt_immOpt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.eraseOpt_immOpt

/-- info: 'IxCC.Own.zip_map_fst_snd' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.zip_map_fst_snd

/-- info: 'IxCC.Own.eraseFun_immFun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.eraseFun_immFun

/-- info: 'IxCC.Own.mapAll_true' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Own.mapAll_true

/-- info: 'IxCC.Own.erase_immortal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.erase_immortal

/-- info: 'IxCC.Own.map_pair_snd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.map_pair_snd

/-- info: 'IxCC.Own.okRhs_immRhs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.okRhs_immRhs

/-- info: 'IxCC.Own.okCode_immCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.okCode_immCode

/-- info: 'IxCC.Own.okAlts_immAlts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.okAlts_immAlts

/-- info: 'IxCC.Own.okOpt_immOpt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.okOpt_immOpt

/-- info: 'IxCC.Own.okFun_immFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.okFun_immFun

/-- info: 'IxCC.Own.checkImmortal_immortal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.checkImmortal_immortal

/-- info: 'IxCC.Own.immRhs_eraseRhs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.immRhs_eraseRhs

/-- info: 'IxCC.Own.immCode_eraseCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.immCode_eraseCode

/-- info: 'IxCC.Own.immAlts_eraseAlts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.immAlts_eraseAlts

/-- info: 'IxCC.Own.immOpt_eraseOpt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.immOpt_eraseOpt

/-- info: 'IxCC.Own.map_fst_zip' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.map_fst_zip

/-- info: 'IxCC.Own.map_plain_zip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.map_plain_zip

/-- info: 'IxCC.Own.immFun_eraseFun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.immFun_eraseFun

/-- info: 'IxCC.Own.immortal_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.immortal_erase

/-- info: 'IxCC.Own.checkImmortal_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.checkImmortal_iff
