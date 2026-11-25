import IxCCCorrect.Routes
import IxCCCorrect.Today
import IxCCCorrect.Progress
import IxCCCorrect.Shape
import IxCCCorrect.Shape1
import IxCCCorrect.Shape1Check
import IxCCCorrect.Shape2
import IxCCCorrect.Shape2Check
import IxCCCorrect.ShapeHook
import IxCCCorrect.ShapeTree
import IxCCCorrect.Compile
import IxCCCorrect.CompileCertified
import IxCCCorrect.GroundRoot
import IxCCCorrect.GroundCheck
import IxCCCorrect.Compose
import IxCCCorrect.ComposeExe
import IxCCCorrect.GroundShape
import IxCCCorrect.Unique
import IxCCCorrect.ComposeExit
import IxCCCorrect.UniqueIota
import IxCCCorrect.UniqueNat
import IxCCCorrect.CanonLaw
import IxCCCorrect.UniqueEnum

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

/-! ## `IxCCCorrect.Shape2` -/

/-- info: 'IxCC.Correct.Shape2.eval2_bool' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.eval2_bool

/-- info: 'IxCC.Correct.Shape2.getElem?_two_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.getElem?_two_add

/-- info: 'IxCC.Correct.Shape2.evalConst_unfolds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.evalConst_unfolds

/-- info: 'IxCC.Correct.Shape2.evalConst_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.evalConst_head

/-- info: 'IxCC.Correct.Shape2.headArity_ctor' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.headArity_ctor

/-- info: 'IxCC.Correct.Shape2.getElem?_append_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.getElem?_append_add

/-- info: 'IxCC.Correct.Shape2.fire_cases_ord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.fire_cases_ord

/-- info: 'IxCC.Correct.Shape2.fire_cases_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.fire_cases_sub

/-- info: 'IxCC.Correct.Shape2.fire_recr_ord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.fire_recr_ord

/-- info: 'IxCC.Correct.Shape2.fire_recr_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.fire_recr_sub

/-- info: 'IxCC.Correct.Shape2.EnvOk.get' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.EnvOk.get

/-- info: 'IxCC.Correct.Shape2.EnvOk.getD' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.EnvOk.getD

/-- info: 'IxCC.Correct.Shape2.EnvOk.length' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.EnvOk.length

/-- info: 'IxCC.Correct.Shape2.EnvOk.append' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.EnvOk.append

/-- info: 'IxCC.Correct.Shape2.EnvOk.reverse' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.EnvOk.reverse

/-- info: 'IxCC.Correct.Shape2.slotOk_irrNone' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.slotOk_irrNone

/-- info: 'IxCC.Correct.Shape2.envOk_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.envOk_fields

/-- info: 'IxCC.Correct.Shape2.envOk_fields_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.envOk_fields_lt

/-- info: 'IxCC.Correct.Shape2.EnvOk.take' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.EnvOk.take

/-- info: 'IxCC.Correct.Shape2.EnvOk.drop' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.EnvOk.drop

/-- info: 'IxCC.Correct.Shape2.ValsOk.toEnv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.ValsOk.toEnv

/-- info: 'IxCC.Correct.Shape2.ValsOk.get' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.ValsOk.get

/-- info: 'IxCC.Correct.Shape2.EnvOk.all_replicate' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.EnvOk.all_replicate

/-- info: 'IxCC.Correct.Shape2.envOk_lits' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.envOk_lits

/-- info: 'IxCC.Correct.Shape2.ValOk.nat_inv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.ValOk.nat_inv

/-- info: 'IxCC.Correct.Shape2.ValOk.enum_inv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.ValOk.enum_inv

/-- info: 'IxCC.Correct.Shape2.ValOk.data_inv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.ValOk.data_inv

/-- info: 'IxCC.Correct.Shape2.ValOk.data_inv_ls' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.ValOk.data_inv_ls

/-- info: 'IxCC.Correct.Shape2.ValOk.inter_inv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.ValOk.inter_inv

/-- info: 'IxCC.Correct.Shape2.ValOk.word_inv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.ValOk.word_inv

/-- info: 'IxCC.Correct.Shape2.selectRule_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.selectRule_data

/-- info: 'IxCC.Correct.Shape2.selectRule_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.selectRule_ok

/-- info: 'IxCC.Correct.Shape2.HeadOk.arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.HeadOk.arity

/-- info: 'IxCC.Correct.Shape2.asWord_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.asWord_lt

/-- info: 'IxCC.Correct.Shape2.ValsOk.one_inv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.ValsOk.one_inv

/-- info: 'IxCC.Correct.Shape2.ValsOk.two_inv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.ValsOk.two_inv

/-- info: 'IxCC.Correct.Shape2.wordValue_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.wordValue_ok

/-- info: 'IxCC.Correct.Shape2.forceAll_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.forceAll_nat

/-- info: 'IxCC.Correct.Shape2.forceAll_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.forceAll_ok

/-- info: 'IxCC.Correct.Shape2.applyAll_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.applyAll_ok

/-- info: 'IxCC.Correct.Shape2.allOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.allOk

/-- info: 'IxCC.Correct.Shape2.run_ok_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.run_ok_vals

/-- info: 'IxCC.Correct.Shape2.run_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.run_ok

/-- info: 'IxCC.Correct.Shape2.eraseVal_enum_levels' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.eraseVal_enum_levels

/-- info: 'IxCC.Correct.Shape2.view_nat_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.view_nat_ok

/-- info: 'IxCC.Correct.Shape2.view_enum_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.view_enum_ok

/-- info: 'IxCC.Correct.Shape2.neverWrong_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.neverWrong_of_shape

/-- info: 'IxCC.Correct.Shape2.recheck_sound_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.recheck_sound_of_shape

/-! ## `IxCCCorrect.Shape2Check` -/

/-- info: 'IxCC.Correct.Shape2.mem_of_lookupEnum' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.mem_of_lookupEnum

/-- info: 'IxCC.Correct.Shape2.mem_of_lookup' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.mem_of_lookup

/-- info: 'IxCC.Correct.Shape2.wordEntryOk_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.wordEntryOk_sound

/-- info: 'IxCC.Correct.Shape2.mem_instsOf' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.mem_instsOf

/-- info: 'IxCC.Correct.Shape2.mem_appRes' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.mem_appRes

/-- info: 'IxCC.Correct.Shape2.mem_projRes' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.mem_projRes

/-- info: 'IxCC.Correct.Shape2.hasShape_parts' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.hasShape_parts

/-- info: 'IxCC.Correct.Shape2.isLam_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.isLam_eq

/-- info: 'IxCC.Correct.Shape2.chkWith_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.chkWith_sound

/-- info: 'IxCC.Correct.Shape2.synth_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.synth_sound

/-- info: 'IxCC.Correct.Shape2.fldsOf_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.fldsOf_sound

/-- info: 'IxCC.Correct.Shape2.isOrdinary_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.isOrdinary_sound

/-- info: 'IxCC.Correct.Shape2.predOk_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.predOk_sound

/-- info: 'IxCC.Correct.Shape2.casesOk_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.casesOk_sound

/-- info: 'IxCC.Correct.Shape2.casesSubOkAt_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.casesSubOkAt_sound

/-- info: 'IxCC.Correct.Shape2.rulesOk_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.rulesOk_sound

/-- info: 'IxCC.Correct.Shape2.recrOkAt_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.recrOkAt_sound

/-- info: 'IxCC.Correct.Shape2.recrOk_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.recrOk_sound

/-- info: 'IxCC.Correct.Shape2.recrSubOkAt_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.recrSubOkAt_sound

/-- info: 'IxCC.Correct.Shape2.dataCtorScan_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.dataCtorScan_sound

/-- info: 'IxCC.Correct.Shape2.dataCtorOk_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.dataCtorOk_sound

/-- info: 'IxCC.Correct.Shape2.ctorsOk_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.ctorsOk_sound

/-- info: 'IxCC.Correct.Shape2.structOk_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.structOk_sound

/-- info: 'IxCC.Correct.Shape2.enumOk_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.enumOk_sound

/-- info: 'IxCC.Correct.Shape2.entryOk_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.entryOk_sound

/-- info: 'IxCC.Correct.Shape2.sigOk_of_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.sigOk_of_cert

/-- info: 'IxCC.Correct.Shape2.neverWrong_of_cert_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.neverWrong_of_cert_nat

/-- info: 'IxCC.Correct.Shape2.neverWrong_of_cert_enum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.neverWrong_of_cert_enum

/-! ## `IxCCCorrect.ShapeHook` -/

/-- info: 'IxCC.Correct.Shape2.tys_nat_of_resultTy' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.tys_nat_of_resultTy

/-- info: 'IxCC.Correct.Shape2.rootsOk_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.rootsOk_get

/-- info: 'IxCC.Correct.Shape2.neverWrong_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.neverWrong_of_check

/-- info: 'IxCC.Correct.Shape2.neverStuck_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.neverStuck_checked

/-- info: 'IxCC.Correct.Shape2.neverWrong_of_enumRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.neverWrong_of_enumRoot

/-- info: 'IxCC.Correct.Shape2.frontRootsOk_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.frontRootsOk_get

/-- info: 'IxCC.Correct.Shape2.checkShaped_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.checkShaped_sound

/-- info: 'IxCC.Correct.Shape2.runShaped_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.runShaped_ok

/-- info: 'IxCC.Correct.Shape2.runShaped_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.runShaped_sound

/-- info: 'IxCC.Correct.Shape2.neverWrong_of_shape_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.neverWrong_of_shape_view

/-- info: 'IxCC.Correct.Shape2.rc_tys_nat_of_resultTy' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.rc_tys_nat_of_resultTy

/-- info: 'IxCC.Correct.Shape2.rc_view_nat_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.rc_view_nat_ok

/-- info: 'IxCC.Correct.Shape2.rc_neverWrong_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.rc_neverWrong_of_check

/-- info: 'IxCC.Correct.Shape2.rc_sound_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.rc_sound_of_shape

/-! ## `IxCCCorrect.ShapeTree` -/

/-- info: 'IxCC.Correct.Shape2.treeView_ctor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.treeView_ctor

/-- info: 'IxCC.Correct.Shape2.fieldsView_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.fieldsView_cons

/-- info: 'IxCC.Correct.Shape2.eraseVal_con' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.eraseVal_con

/-- info: 'IxCC.Correct.Shape2.reads_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.reads_fields

/-- info: 'IxCC.Correct.Shape2.reads_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.reads_lt

/-- info: 'IxCC.Correct.Shape2.reads_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.reads_val

/-- info: 'IxCC.Correct.Shape2.rc_view_tree_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.rc_view_tree_ok

/-- info: 'IxCC.Correct.Shape2.rc_neverWrong_of_treeRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.rc_neverWrong_of_treeRoot

/-- info: 'IxCC.Correct.Shape2.view_enum_ok_any' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.view_enum_ok_any

/-- info: 'IxCC.Correct.Shape2.rc_neverWrong_of_enumRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.rc_neverWrong_of_enumRoot

/-- info: 'IxCC.Correct.Shape2.rcRootsOk_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.rcRootsOk_get

/-- info: 'IxCC.Correct.Shape2.rcCheckShaped_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.rcCheckShaped_sound

/-- info: 'IxCC.Correct.Shape2.rcRunShaped_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Shape2.rcRunShaped_sound

/-! ## `IxCCCorrect.Compile` -/

/-- info: 'IxCC.Correct.extract_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.extract_all

/-- info: 'IxCC.Correct.execImage_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.execImage_checked

/-- info: 'IxCC.Correct.machine_of_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.machine_of_build

/-- info: 'IxCC.Correct.plain_file_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.plain_file_sound

/-- info: 'IxCC.Correct.plain_file_sound_rc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.plain_file_sound_rc

/-- info: 'IxCC.Correct.machine_file_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.machine_file_sound

/-- info: 'IxCC.Correct.machine_file_sound_rc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.machine_file_sound_rc

/-- info: 'IxCC.Correct.executable_today' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.executable_today

/-- info: 'IxCC.Correct.compiledAs_of_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.compiledAs_of_stages

/-- info: 'IxCC.Correct.compile_today' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.compile_today

/-- info: 'IxCC.Correct.compile_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.compile_route

/-- info: 'IxCC.Correct.compile_admits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.compile_admits

/-- info: 'IxCC.Correct.binds_packaged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.binds_packaged

/-- info: 'IxCC.Correct.compileWith_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.compileWith_refines

/-- info: 'IxCC.Correct.compileWith_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.compileWith_route

/-! ## `IxCCCorrect.CompileCertified` -/

/-- info: 'IxCC.Correct.except_bind_ok' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Correct.except_bind_ok

/-- info: 'IxCC.Correct.except_mapError_ok' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Correct.except_mapError_ok

/-- info: 'IxCC.Correct.compileCertified_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.compileCertified_parts

/-- info: 'IxCC.Correct.compileCertified_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.compileCertified_refines

/-- info: 'IxCC.Correct.compileCertified_today' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.compileCertified_today

/-- info: 'IxCC.Correct.shapeZero_checks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.shapeZero_checks

/-- info: 'IxCC.Correct.shapeRc_checks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.shapeRc_checks

/-- info: 'IxCC.Correct.shapeZero_notWrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.shapeZero_notWrong

/-- info: 'IxCC.Correct.shapeRc_notWrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.shapeRc_notWrong

/-- info: 'IxCC.Correct.runShaped_of_shapeZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.runShaped_of_shapeZero

/-- info: 'IxCC.Correct.rcRunShaped_of_shapeRc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.rcRunShaped_of_shapeRc

/-- info: 'IxCC.Correct.outcome_noWrong' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.outcome_noWrong

/-- info: 'IxCC.Correct.executable_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.executable_sound

/-- info: 'IxCC.Correct.compileCertified_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.compileCertified_sound

/-- info: 'IxCC.Correct.compileCertified_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.compileCertified_route

/-- info: 'IxCC.Correct.compileCertified_seedClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.compileCertified_seedClosure

/-! ## `IxCCCorrect.GroundRoot` -/

/-- info: 'IxCC.Correct.foArgs_nats' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.foArgs_nats

/-- info: 'IxCC.Correct.denotesList_lits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.denotesList_lits

/-- info: 'IxCC.Correct.rootCanon_coreWK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.rootCanon_coreWK

/-- info: 'IxCC.Correct.Grounded.canon_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Grounded.canon_sound

/-- info: 'IxCC.Correct.Grounded.app_denotes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Grounded.app_denotes

/-- info: 'IxCC.Correct.Grounded.same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.Grounded.same

/-! ## `IxCCCorrect.GroundCheck` -/

/-- info: 'IxCC.Correct.viewTag_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.viewTag_some

/-- info: 'IxCC.Correct.ctorsListed_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.ctorsListed_sound

/-- info: 'IxCC.Correct.resultOk_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.resultOk_sound

/-- info: 'IxCC.Correct.groundOkB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.groundOkB_sound

/-- info: 'IxCC.Correct.groundCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.groundCheck_sound

/-- info: 'IxCC.Correct.GroundOk.result_not_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.GroundOk.result_not_word

/-- info: 'IxCC.Correct.GroundOk.result_not_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.GroundOk.result_not_data

/-! ## `IxCCCorrect.Compose` -/

/-- info: 'IxCC.Correct.admits_of_ingress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.admits_of_ingress

/-- info: 'IxCC.Correct.obsOf_lit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.obsOf_lit

/-- info: 'IxCC.Correct.obsOf_con' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.obsOf_con

/-- info: 'IxCC.Correct.viewNat_viewOf' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.viewNat_viewOf

/-- info: 'IxCC.Correct.viewNat_treeViewOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.viewNat_treeViewOf

/-- info: 'IxCC.Correct.srcRun_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.srcRun_ok

/-- info: 'IxCC.Correct.canonResult_of_canonValue' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.canonResult_of_canonValue

/-- info: 'IxCC.Correct.returnsCanon_of_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.returnsCanon_of_at

/-- info: 'IxCC.Correct.agrees_of_srcPlainEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.agrees_of_srcPlainEval

/-- info: 'IxCC.Correct.recheck_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.recheck_agrees

/-- info: 'IxCC.Correct.rc_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.rc_agrees

/-- info: 'IxCC.Correct.groundCheckRecheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.groundCheckRecheck_sound

/-- info: 'IxCC.Correct.groundCheckRc_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.groundCheckRc_sound

/-! ## `IxCCCorrect.ComposeExe` -/

/-- info: 'IxCC.Correct.written_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.written_append

/-- info: 'IxCC.Correct.written_prefix' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.written_prefix

/-- info: 'IxCC.Correct.stdout_started' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.stdout_started

/-- info: 'IxCC.Correct.accepted_prefix' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Correct.accepted_prefix

/-- info: 'IxCC.Correct.writeSeq_written_other' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.writeSeq_written_other

/-- info: 'IxCC.Correct.writeSeq_written_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.writeSeq_written_prefix

/-- info: 'IxCC.Correct.stdout_reportsMsg' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.stdout_reportsMsg

/-- info: 'IxCC.Correct.stdout_printsResult' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.stdout_printsResult

/-- info: 'IxCC.Correct.stdout_plainRefused' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.stdout_plainRefused

/-- info: 'IxCC.Correct.stdout_of_outcome' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.stdout_of_outcome

/-- info: 'IxCC.Correct.parseArg_of_parseArgBytes' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.parseArg_of_parseArgBytes

/-- info: 'IxCC.Correct.mapM_parseArg_of_parseArgsList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.mapM_parseArg_of_parseArgsList

/-- info: 'IxCC.Correct.abi_parse_of_parseArgsList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.abi_parse_of_parseArgsList

/-- info: 'IxCC.Correct.answer_lt_of_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.answer_lt_of_agrees

/-- info: 'IxCC.Correct.render_eq_of_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.render_eq_of_obs

/-- info: 'IxCC.Correct.tier1Stdout_of_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.tier1Stdout_of_outcome

/-- info: 'IxCC.Correct.recheck_arity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.recheck_arity

/-- info: 'IxCC.Correct.plain_exe_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.plain_exe_agrees

/-- info: 'IxCC.Correct.plain_exe_tier1Stdout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.plain_exe_tier1Stdout

/-- info: 'IxCC.Correct.rc_plain_exe_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.rc_plain_exe_agrees

/-- info: 'IxCC.Correct.rc_plain_exe_tier1Stdout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.rc_plain_exe_tier1Stdout

/-! ## `IxCCCorrect.Unique` -/

/-- info: 'IxCC.Correct.accepted_has_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.accepted_has_model

/-- info: 'IxCC.Correct.numeralBasis_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.numeralBasis_of_check

/-- info: 'IxCC.Correct.sameDenotation_lit_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.sameDenotation_lit_unique

/-- info: 'IxCC.Correct.agrees_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.agrees_unique

/-! ## `IxCCCorrect.GroundShape` -/

/-- info: 'IxCC.Correct.returnsCanon_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.returnsCanon_of_shape

/-- info: 'IxCC.Correct.neverWrong_of_groundShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.neverWrong_of_groundShape

/-- info: 'IxCC.Correct.groundShapeCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.groundShapeCheck_sound

/-- info: 'IxCC.Correct.groundShapeCheckP_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.groundShapeCheckP_sound

/-- info: 'IxCC.Correct.GroundOk.target_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.GroundOk.target_key

/-- info: 'IxCC.Correct.recheck_agrees_shaped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.recheck_agrees_shaped

/-- info: 'IxCC.Correct.plain_exe_tier1Stdout_shaped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.plain_exe_tier1Stdout_shaped

/-- info: 'IxCC.Correct.tier1Check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.tier1Check_sound

/-! ## `IxCCCorrect.ComposeExit` -/

/-- info: 'IxCC.Correct.getLast?_append_of_ne_nil' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.getLast?_append_of_ne_nil

/-- info: 'IxCC.Correct.exitStatus_cons_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.exitStatus_cons_cons

/-- info: 'IxCC.Correct.exitStatus_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.exitStatus_append

/-- info: 'IxCC.Correct.writeSeq_prefix_exit' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.writeSeq_prefix_exit

/-- info: 'IxCC.Correct.writeSeq_written_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.writeSeq_written_full

/-- info: 'IxCC.Correct.message_status_ne_zero' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Correct.message_status_ne_zero

/-- info: 'IxCC.Correct.writeFailed_ne_zero' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Correct.writeFailed_ne_zero

/-- info: 'IxCC.Correct.reportsMsg_prefix_exit' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.reportsMsg_prefix_exit

/-- info: 'IxCC.Correct.cons_prefix_exit' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.cons_prefix_exit

/-- info: 'IxCC.Correct.nil_prefix_exit' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.nil_prefix_exit

/-- info: 'IxCC.Correct.exit_of_outcome' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.exit_of_outcome

/-- info: 'IxCC.Correct.tier1Exit_of_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.tier1Exit_of_outcome

/-- info: 'IxCC.Correct.plain_exe_tier1Core_shaped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.plain_exe_tier1Core_shaped

/-- info: 'IxCC.Correct.tier1Check_sound_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.tier1Check_sound_core

/-! ## `IxCCCorrect.UniqueIota` -/

/-- info: 'IxCC.Correct.lamDoms_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.lamDoms_sound

/-- info: 'IxCC.Correct.boolRecStored_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.boolRecStored_of_check

/-- info: 'IxCC.Correct.bool_true_ne_false_iota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.bool_true_ne_false_iota

/-- info: 'IxCC.Correct.numeralBasisI_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.numeralBasisI_of_check

/-- info: 'IxCC.Correct.sameDenotation_lit_unique_iota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.sameDenotation_lit_unique_iota

/-- info: 'IxCC.Correct.agrees_unique_iota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.agrees_unique_iota

/-! ## `IxCCCorrect.UniqueNat` -/

/-- info: 'IxCC.Correct.natRecStored_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.natRecStored_of_check

/-- info: 'IxCC.Correct.natRec_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.natRec_sep

/-- info: 'IxCC.Correct.litSet_inj_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.litSet_inj_rec

/-- info: 'IxCC.Correct.numeralBasisN_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.numeralBasisN_of_check

/-- info: 'IxCC.Correct.sameDenotation_lit_unique_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.sameDenotation_lit_unique_rec

/-- info: 'IxCC.Correct.agrees_unique_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.agrees_unique_rec

/-! ## `IxCCCorrect.CanonLaw` -/

/-- info: 'IxCC.Correct.selRetype1_eq_of_not_defn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.selRetype1_eq_of_not_defn

/-- info: 'IxCC.Correct.ctorCanon_selRetype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.ctorCanon_selRetype

/-! ## `IxCCCorrect.UniqueEnum` -/

/-- info: 'IxCC.Correct.minorDoms_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.minorDoms_length

/-- info: 'IxCC.Correct.piDoms_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.piDoms_sound

/-- info: 'IxCC.Correct.enumRecStored_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.enumRecStored_of_check

/-- info: 'IxCC.Correct.fits_minors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.fits_minors

/-- info: 'IxCC.Correct.enum_ctor_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.enum_ctor_ne

/-- info: 'IxCC.Correct.agrees_unique_enum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Correct.agrees_unique_enum

/-! ## `IxCCCorrect.Claim`, `IxCCCorrect.Tiers` (owner-approved P3) -/

/-- info: 'IxCC.Correct.ArgTy.natCount_replicate_nat' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.ArgTy.natCount_replicate_nat

/-- info: 'IxCC.Correct.argTerms_replicate' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Correct.argTerms_replicate
