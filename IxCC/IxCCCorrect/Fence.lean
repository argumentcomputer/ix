import IxCCCorrect.Routes
import IxCCCorrect.Today
import IxCCCorrect.Progress
import IxCCCorrect.Shape
import IxCCCorrect.Shape1
import IxCCCorrect.Shape1Check

/-! # The target statements' axiom fence: every theorem `IxCCCorrect` proves uses at most the
three standard axioms. Building the library checks it (`#guard_msgs`), in the required check
`ixcc-grounding`; `check-build-graph` counts and digests its assertions apart from the shared
aggregate's and the grounding library's (`nix/ci-coverage.json`, `correct_*`). The tiers, the
routes and the progress targets are definitions and have no fence. -/

/-! ## `IxCCCorrect.Routes` -/

/-- info: 'IxCC.Correct.CertifyingRoute.holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.CertifyingRoute.holds

/-- info: 'IxCC.Correct.CertifiedRoute.holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.CertifiedRoute.holds

/-! ## `IxCCCorrect.Today` -/

/-- info: 'IxCC.Correct.LoadedFile.toLoaded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.LoadedFile.toLoaded

/-- info: 'IxCC.Correct.verifyProgram_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.verifyProgram_target

/-- info: 'IxCC.Correct.correctToday_of_verifyExeBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.correctToday_of_verifyExeBytes

/-- info: 'IxCC.Correct.correctToday_of_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.correctToday_of_accepts

/-! ## `IxCCCorrect.Progress` -/

/-- info: 'IxCC.Correct.NeverWrong.neverStuck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.NeverWrong.neverStuck

/-- info: 'IxCC.Correct.viewed_stuck_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.viewed_stuck_iff

/-- info: 'IxCC.Correct.neverStuck_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.neverStuck_iff

/-- info: 'IxCC.Correct.neverWrong_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.neverWrong_iff

/-- info: 'IxCC.Correct.not_goesWrong_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.not_goesWrong_iff

/-- info: 'IxCC.Correct.rc_not_goesWrong_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.rc_not_goesWrong_iff

/-- info: 'IxCC.Correct.not_stuck_of_refinesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.not_stuck_of_refinesOn

/-- info: 'IxCC.Correct.recheck_sound_of_neverWrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.recheck_sound_of_neverWrong

/-- info: 'IxCC.Correct.recheck_not_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.recheck_not_stuck

/-- info: 'IxCC.Correct.recheck_not_stuck_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.recheck_not_stuck_at

/-- info: 'IxCC.Correct.rc_sound_of_neverWrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.rc_sound_of_neverWrong

/-- info: 'IxCC.Correct.rc_not_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.rc_not_stuck

/-- info: 'IxCC.Correct.rc_not_stuck_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.rc_not_stuck_at

/-- info: 'IxCC.Correct.plainExeOutcome_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.plainExeOutcome_mono

/-- info: 'IxCC.Correct.plain_exe_sound_of_neverWrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.plain_exe_sound_of_neverWrong

/-- info: 'IxCC.Correct.rc_plain_exe_sound_of_neverWrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.rc_plain_exe_sound_of_neverWrong

/-- info: 'IxCC.Correct.plain_exe_specified_of_neverStuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.plain_exe_specified_of_neverStuck

/-- info: 'IxCC.Correct.rc_plain_exe_specified_of_neverStuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.rc_plain_exe_specified_of_neverStuck

/-- info: 'IxCC.Correct.FunctionalProgress.safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.FunctionalProgress.safety

/-- info: 'IxCC.Correct.SafetyProgress.given' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.SafetyProgress.given

/-! ## `IxCCCorrect.Shape` -/

/-- info: 'IxCC.Correct.Shape.arity_cases' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.arity_cases

/-- info: 'IxCC.Correct.Shape.headArity_prim' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.headArity_prim

/-- info: 'IxCC.Correct.Shape.eval2_nat' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.eval2_nat

/-- info: 'IxCC.Correct.Shape.evalLits_of_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.evalLits_of_length

/-- info: 'IxCC.Correct.Shape.litArgs_map_lit' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.litArgs_map_lit

/-- info: 'IxCC.Correct.Shape.primValue_lits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.primValue_lits

/-- info: 'IxCC.Correct.Shape.eval_app_strict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.eval_app_strict

/-- info: 'IxCC.Correct.Shape.eval_app_byName' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.eval_app_byName

/-- info: 'IxCC.Correct.Shape.eval_letE_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.eval_letE_rel

/-- info: 'IxCC.Correct.Shape.apply_clo_never' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.apply_clo_never

/-- info: 'IxCC.Correct.Shape.ValOk.nat_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.ValOk.nat_inv

/-- info: 'IxCC.Correct.Shape.EnvOk.get' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.EnvOk.get

/-- info: 'IxCC.Correct.Shape.forceAll_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.forceAll_nat

/-- info: 'IxCC.Correct.Shape.allOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.allOk

/-- info: 'IxCC.Correct.Shape.applyAll_nats' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.applyAll_nats

/-- info: 'IxCC.Correct.Shape.run_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.run_ok

/-- info: 'IxCC.Correct.Shape.view_lit_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.view_lit_ne_none

/-- info: 'IxCC.Correct.Shape.neverWrong_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.neverWrong_of_shape

/-- info: 'IxCC.Correct.Shape.recheck_sound_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.recheck_sound_of_shape

/-- info: 'IxCC.Correct.Shape.synth_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.synth_sound

/-- info: 'IxCC.Correct.Shape.mem_of_sigOf' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.mem_of_sigOf

/-- info: 'IxCC.Correct.Shape.entryOk_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.entryOk_sound

/-- info: 'IxCC.Correct.Shape.sigOk_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.sigOk_of_check

/-- info: 'IxCC.Correct.Shape.neverWrong_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape.neverWrong_of_check

/-! ## `IxCCCorrect.Shape1` -/

/-- info: 'IxCC.Correct.Shape1.eval2_bool' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.eval2_bool

/-- info: 'IxCC.Correct.Shape1.getElem?_two_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.getElem?_two_add

/-- info: 'IxCC.Correct.Shape1.evalConst_unfolds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.evalConst_unfolds

/-- info: 'IxCC.Correct.Shape1.evalConst_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.evalConst_head

/-- info: 'IxCC.Correct.Shape1.headArity_ctor' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.headArity_ctor

/-- info: 'IxCC.Correct.Shape1.fire_cases_ord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.fire_cases_ord

/-- info: 'IxCC.Correct.Shape1.fire_recr_ord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.fire_recr_ord

/-- info: 'IxCC.Correct.Shape1.EnvOk.get' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.EnvOk.get

/-- info: 'IxCC.Correct.Shape1.EnvOk.getD' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.EnvOk.getD

/-- info: 'IxCC.Correct.Shape1.EnvOk.length' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.EnvOk.length

/-- info: 'IxCC.Correct.Shape1.EnvOk.append' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.EnvOk.append

/-- info: 'IxCC.Correct.Shape1.EnvOk.reverse' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.EnvOk.reverse

/-- info: 'IxCC.Correct.Shape1.EnvOk.take' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.EnvOk.take

/-- info: 'IxCC.Correct.Shape1.EnvOk.all_replicate' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.EnvOk.all_replicate

/-- info: 'IxCC.Correct.Shape1.envOk_lits' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.envOk_lits

/-- info: 'IxCC.Correct.Shape1.ValOk.nat_inv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.ValOk.nat_inv

/-- info: 'IxCC.Correct.Shape1.ValOk.enum_inv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.ValOk.enum_inv

/-- info: 'IxCC.Correct.Shape1.selectRule_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.selectRule_ok

/-- info: 'IxCC.Correct.Shape1.HeadOk.arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.HeadOk.arity

/-- info: 'IxCC.Correct.Shape1.forceAll_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.forceAll_nat

/-- info: 'IxCC.Correct.Shape1.applyAll_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.applyAll_ok

/-- info: 'IxCC.Correct.Shape1.allOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.allOk

/-- info: 'IxCC.Correct.Shape1.run_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.run_ok

/-- info: 'IxCC.Correct.Shape1.eraseVal_enum_levels' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.eraseVal_enum_levels

/-- info: 'IxCC.Correct.Shape1.view_nat_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.view_nat_ok

/-- info: 'IxCC.Correct.Shape1.view_enum_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.view_enum_ok

/-- info: 'IxCC.Correct.Shape1.neverWrong_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.neverWrong_of_shape

/-- info: 'IxCC.Correct.Shape1.recheck_sound_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.recheck_sound_of_shape

/-! ## `IxCCCorrect.Shape1Check` -/

/-- info: 'IxCC.Correct.Shape1.mem_of_lookupEnum' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.mem_of_lookupEnum

/-- info: 'IxCC.Correct.Shape1.mem_instsOf' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.mem_instsOf

/-- info: 'IxCC.Correct.Shape1.mem_appRes' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.mem_appRes

/-- info: 'IxCC.Correct.Shape1.synth_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.synth_sound

/-- info: 'IxCC.Correct.Shape1.fldsOf_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.fldsOf_sound

/-- info: 'IxCC.Correct.Shape1.isOrdinary_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.isOrdinary_sound

/-- info: 'IxCC.Correct.Shape1.predOk_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.predOk_sound

/-- info: 'IxCC.Correct.Shape1.casesOk_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.casesOk_sound

/-- info: 'IxCC.Correct.Shape1.rulesOk_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.rulesOk_sound

/-- info: 'IxCC.Correct.Shape1.recrOk_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.recrOk_sound

/-- info: 'IxCC.Correct.Shape1.enumOk_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.enumOk_sound

/-- info: 'IxCC.Correct.Shape1.entryOk_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.entryOk_sound

/-- info: 'IxCC.Correct.Shape1.sigOk_of_cert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.sigOk_of_cert

/-- info: 'IxCC.Correct.Shape1.neverWrong_of_cert_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.neverWrong_of_cert_nat

/-- info: 'IxCC.Correct.Shape1.neverWrong_of_cert_enum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape1.neverWrong_of_cert_enum
