import IxVMRefinement.Core.Registry
import IxVMRefinement.L1.Hashed

/-! # Record loads (`Ingress::get_ci`, `get_ci_cprj`, `get_ci_iprj`, `load_verified_constant`)

Step lemmas for the four record-load functions of `Specs.Callees.Fn`.
* `get_ci`, `get_ci_cprj`, `get_ci_iprj`: discharged directly from `hc.loads` (`LoadFacts`).
* `load_verified_constant`: combines `L1.load_verified_constant_addr` (giving `Hashed` and the
  `Address.blake3Pure` identity) with `LoadFacts.recordShape` (the shallow decoded record shape
  `ConstShapeRep` at `Ix.Cert.recordAt c.E`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

set_option linter.unusedVariables false

/-- `Ingress::get_ci`: discharged from `LoadFacts.getCI`. -/
theorem get_ci_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Ingress::get_ci" args h r h' calls) :
    Specs.Callees.get_ci c args h r h' calls := by
  intro ap a hargs good ha
  subst hargs
  exact hc.loads.getCI ap r h h' calls a ev good ha

/-- `Ingress::get_ci_cprj`: discharged from `LoadFacts.getCprj`. -/
theorem get_ci_cprj_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Ingress::get_ci_cprj" args h r h' calls) :
    Specs.Callees.get_ci_cprj c args h r h' calls := by
  intro bp i j b hargs good hb
  subst hargs
  exact hc.loads.getCprj bp r i j h h' calls b ev good hb

/-- `Ingress::get_ci_iprj`: discharged from `LoadFacts.getIprj`. -/
theorem get_ci_iprj_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Ingress::get_ci_iprj" args h r h' calls) :
    Specs.Callees.get_ci_iprj c args h r h' calls := by
  intro bp i b hargs good hb
  subst hargs
  exact hc.loads.getIprj bp r i h h' calls b ev good hb

/-- `Ingress::load_verified_constant`: combines `L1.load_verified_constant_addr` with
`LoadFacts.recordShape`. -/
theorem load_verified_constant_step (c : Ctx) (hc : CoreFacts c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Ingress::load_verified_constant" args h r h' calls) :
    Specs.Callees.load_verified_constant c args h r h' calls := by
  intro ap a hargs good ha
  subst hargs
  obtain ⟨bytes, _, _, _, _, -, -, hashed, hblake, -⟩ := L1.load_verified_constant_addr ha ev
  exact ⟨⟨bytes, hashed, hblake⟩,
    fun cst hcst => hc.loads.recordShape ap r h h' calls a cst ev good ha hcst⟩

end IxVM.Refinement.Core
