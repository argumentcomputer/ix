import IxCCCorrect.Shape
import IxCC.Shape.Src.Judgment

/-!
# `IxCCCorrect.Shape2`: re-exports

Moved to production as `IxCC.Shape.Src.Judgment` (namespace `IxCC.SrcShape`), which needs no
model. Every name is re-exported here under `IxCC.Correct.Shape2`, so modules written against
the old names build unchanged; `#print axioms` of an old name prints the production name.
-/

namespace IxCC.Correct.Shape2

export IxCC.Shape (
  Shape arrows)

export IxCC.SrcShape (
  DataDecl Sig HasShape wordArgs wordResOk srcShape fieldSlot ScrutOk HeadOk ValOk SlotOk 
  EnvOk ValsOk ResOk Unfolds HeadOf ConstOk SigOk eval2_bool getElem?_two_add 
  evalConst_unfolds evalConst_head headArity_ctor getElem?_append_add fire_cases_ord 
  fire_cases_sub fire_recr_ord fire_recr_sub EnvOk.get EnvOk.getD EnvOk.length 
  EnvOk.append EnvOk.reverse slotOk_irrNone envOk_fields envOk_fields_lt EnvOk.take 
  EnvOk.drop ValsOk.toEnv ValsOk.get EnvOk.all_replicate envOk_lits ValOk.nat_inv 
  ValOk.enum_inv ValOk.data_inv ValOk.data_inv_ls ValOk.inter_inv ValOk.word_inv 
  selectRule_data selectRule_ok HeadOk.arity asWord_lt ValsOk.one_inv ValsOk.two_inv 
  wordValue_ok forceAll_nat forceAll_ok applyAll_ok AllOk allOk run_ok_vals run_ok 
  eraseVal_enum_levels view_nat_ok view_enum_ok neverWrong_of_shape 
  recheck_sound_of_shape )

end IxCC.Correct.Shape2
