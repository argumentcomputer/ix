import IxVMRefinement.Assembly.LateRegistry
import IxVMRefinement.Decl.LateWalkedConst
import IxVMRefinement.Assembly.TypingDefnBlock

/-! # The step of a definition record, keeping a clause along its declaration step

The steps this module stated are restated in `Assembly/ValueUnitStep.lean`: the step of a
standalone definition, theorem or opaque record (`valueUnitStep_defn`) and of a block of
definitions (`valueUnitStep_defnBlock`), each stated once for the typing fold and the binding
fold, over the fold's clause, with the limit of the record's check a validating role context
or an assuming one. A clause that a declaration step keeps but that does not follow from the
stored constant alone (the registry of native families holds a model of the environment) is
kept there along the step of the declaration judgement the install returns (`valueInstall`,
`memberInstall`, `FoldClauseWith.consValue`).

The module is kept for its imports: the registry, the declaration step of a walked value
constant at a validating context (`Decl.walkedConst_declRunJ`) and the facts about a block of
definitions.
-/
