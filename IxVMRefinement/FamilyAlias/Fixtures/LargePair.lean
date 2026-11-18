import IxVMRefinement.FamilyAlias.AdviceLayout
import IxVMRefinement.FamilyAlias.Fixtures.Terms

/-! # A mutual pair in `Type u` with large recursors

The family step's conclusion at a concrete family (`inhabited`):

    mutual
      inductive PA.{u} : Type u | mk : PA
      inductive PB.{u} : Type u | mk : PB
    end

The data below are written out by a generator, from these sources:

* `blk`: Lean's own constants of the family (types, constructors, recursors with their rules,
  the auxiliary recursors of a nested family included), lowered by IxC's reader
  (`Ix.Kernel.Reader.lowerInductiveDecls`) with the reader's level numbering. The keys of the
  members are placeholder addresses; the basis and `List` are at their role keys.
* `pre`, `aliases`, `tbl`: the advice layout (`advicePrefix`, `familyAliases`, `familyTable`) of
  the environment IxC's own fold stores after it checks the block with the model its
  in-process modeller generates. The advice keys are placeholder addresses.
* `tysM`, `tysR`, `rhsss`: the annotated types and rule right-hand sides IxC's fold stores.

`record_ok` evaluates the record search: each judgement of the record is a run of IxC's
executable checker on the renamed positional subject, bridged to a derivation. -/

namespace IxVM.Refinement.Decl.FamilyAlias.Fixtures.LargePair

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule RecRuleFire ReducibilityHint)

set_option maxRecDepth 100000

def k0 : KKey := Key.id (adr [176, 0, 0])
def k1 : KKey := Key.id (adr [176, 0, 1])
def k2 : KKey := Key.id (adr [176, 0, 2])
def k3 : KKey := Key.id (adr [176, 0, 3])
def k4 : KKey := Key.id (adr [176, 0, 4])
def k5 : KKey := Key.id (adr [176, 0, 5])
def k6 : KKey := Key.id (adr [173, 0, 15])
def k7 : KKey := Key.id (adr [173, 0, 8])
def k8 : KKey := Key.id (adr [173, 0, 9])
def k9 : KKey := Key.id (adr [173, 0, 10])
def k10 : KKey := Key.id (adr [173, 0, 11])
def k11 : KKey := Key.role (Ix.Kernel.Role.eq)
def k12 : KKey := Key.id (adr [173, 0, 13])
def k13 : KKey := Key.role (Ix.Kernel.Role.eqRefl)
def k14 : KKey := Key.id (adr [173, 0, 14])
def k15 : KKey := Key.id (adr [173, 0, 12])
def k16 : KKey := Key.id (adr [173, 0, 7])
def k17 : KKey := Key.id (adr [173, 0, 0])
def k18 : KKey := Key.id (adr [173, 0, 4])
def k19 : KKey := Key.id (adr [173, 0, 3])
def k20 : KKey := Key.id (adr [173, 0, 2])
def k21 : KKey := Key.id (adr [173, 0, 1])
def k22 : KKey := Key.id (adr [173, 0, 6])
def k23 : KKey := Key.id (adr [173, 0, 5])
def k24 : KKey := Key.id (adr [176, 0, 200])
def k25 : KKey := Key.role (Ix.Kernel.Role.list)
def k26 : KKey := Key.role (Ix.Kernel.Role.listNil)
def k27 : KKey := Key.role (Ix.Kernel.Role.listCons)
def k28 : KKey := Key.role (Ix.Kernel.Role.punitRec)
def k29 : KKey := Key.role (Ix.Kernel.Role.punit)
def k30 : KKey := Key.role (Ix.Kernel.Role.punitUnit)
def k31 : KKey := Key.role (Ix.Kernel.Role.eqRec)
def k32 : KKey := Key.aux k5 (Ix.Kernel.Derived.model)
def k33 : KKey := Key.aux k32 (Ix.Kernel.Derived.iota 0)
def k34 : KKey := Key.aux k3 (Ix.Kernel.Derived.model)
def k35 : KKey := Key.aux k4 (Ix.Kernel.Derived.model)
def k36 : KKey := Key.aux k35 (Ix.Kernel.Derived.iota 0)
def k37 : KKey := Key.aux k2 (Ix.Kernel.Derived.model)
def k38 : KKey := Key.aux k0 (Ix.Kernel.Derived.model)
def k39 : KKey := Key.aux k1 (Ix.Kernel.Derived.model)

/-- The block, as read. -/
def b0 : ConstantInfo .anon :=
  ConstantInfo.indInfo (cv k0 [0] (st (ls (lp 0)))) { eta := false, etaCtor := none, etaParams := 0, etaFields := 0, unitlike := false, unitParams := 0, ruleK := false, sortZ := (pZ []) }
def b1 : ConstantInfo .anon :=
  ConstantInfo.indInfo (cv k1 [0] (st (ls (lp 0)))) { eta := false, etaCtor := none, etaParams := 0, etaFields := 0, unitlike := false, unitParams := 0, ruleK := false, sortZ := (pZ []) }
def b2 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k2 [0] (cn k0 [(lp 0)])) 0 0
def b3 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k3 [0] (cn k1 [(lp 0)])) 0 0
def b4 : ConstantInfo .anon :=
  ConstantInfo.recInfo (cv k4 [1, 0] (pi pN (pi pN (cn k0 [(lp 0)]) (st (lp 1))) (pi pN (pi pN (cn k1 [(lp 0)]) (st (lp 1))) (pi pN (ap (bv 1) (cn k2 [(lp 0)])) (pi pN (ap (bv 1) (cn k3 [(lp 0)])) (pi pN (cn k0 [(lp 0)]) (ap (bv 4) (bv 0)))))))) 4 4 [(RecRule.mk k2 0 0 RecRuleFire.inert (lm pN (pi pN (cn k0 [(lp 0)]) (st (lp 1))) (lm pN (pi pN (cn k1 [(lp 0)]) (st (lp 1))) (lm pN (ap (bv 1) (cn k2 [(lp 0)])) (lm pN (ap (bv 1) (cn k3 [(lp 0)])) (bv 1))))) false false false)]
def b5 : ConstantInfo .anon :=
  ConstantInfo.recInfo (cv k5 [1, 0] (pi pN (pi pN (cn k0 [(lp 0)]) (st (lp 1))) (pi pN (pi pN (cn k1 [(lp 0)]) (st (lp 1))) (pi pN (ap (bv 1) (cn k2 [(lp 0)])) (pi pN (ap (bv 1) (cn k3 [(lp 0)])) (pi pN (cn k1 [(lp 0)]) (ap (bv 3) (bv 0)))))))) 4 4 [(RecRule.mk k3 0 0 RecRuleFire.inert (lm pN (pi pN (cn k0 [(lp 0)]) (st (lp 1))) (lm pN (pi pN (cn k1 [(lp 0)]) (st (lp 1))) (lm pN (ap (bv 1) (cn k2 [(lp 0)])) (lm pN (ap (bv 1) (cn k3 [(lp 0)])) (bv 0))))) false false false)]
def blk : List (ConstantInfo .anon) :=
  [b0, b1, b2, b3, b4, b5]

/-- The prefix in the advice layout, newest first. -/
def p0 : ConstantInfo .anon :=
  ConstantInfo.thmInfo (cv k6 [0, 1] (pi (pZ []) (pi pN (cn k7 [(lp 1)]) (st (lp 0))) (pi (pZ []) (pi pN (cn k8 [(lp 1)]) (st (lp 0))) (pi (pZ []) (ap (bv 1) (cn k9 [(lp 1)])) (pi (pZ []) (ap (bv 1) (cn k10 [(lp 1)])) (ap (ap (ap (cn k11 [(lp 0)]) (ap (bv 2) (cn k10 [(lp 1)]))) (ap (ap (ap (ap (ap (cn k12 [(lp 0), (lp 1)]) (bv 3)) (bv 2)) (bv 1)) (bv 0)) (cn k10 [(lp 1)]))) (bv 0))))))) (lm pN (pi pN (cn k7 [(lp 1)]) (st (lp 0))) (lm pN (pi pN (cn k8 [(lp 1)]) (st (lp 0))) (lm pN (ap (bv 1) (cn k9 [(lp 1)])) (lm pN (ap (bv 1) (cn k10 [(lp 1)])) (ap (ap (cn k13 [(lp 0)]) (ap (bv 2) (cn k10 [(lp 1)]))) (ap (ap (ap (ap (ap (cn k12 [(lp 0), (lp 1)]) (bv 3)) (bv 2)) (bv 1)) (bv 0)) (cn k10 [(lp 1)])))))))
def p1 : ConstantInfo .anon :=
  ConstantInfo.thmInfo (cv k14 [0, 1] (pi (pZ []) (pi pN (cn k7 [(lp 1)]) (st (lp 0))) (pi (pZ []) (pi pN (cn k8 [(lp 1)]) (st (lp 0))) (pi (pZ []) (ap (bv 1) (cn k9 [(lp 1)])) (pi (pZ []) (ap (bv 1) (cn k10 [(lp 1)])) (ap (ap (ap (cn k11 [(lp 0)]) (ap (bv 3) (cn k9 [(lp 1)]))) (ap (ap (ap (ap (ap (cn k15 [(lp 0), (lp 1)]) (bv 3)) (bv 2)) (bv 1)) (bv 0)) (cn k9 [(lp 1)]))) (bv 1))))))) (lm pN (pi pN (cn k7 [(lp 1)]) (st (lp 0))) (lm pN (pi pN (cn k8 [(lp 1)]) (st (lp 0))) (lm pN (ap (bv 1) (cn k9 [(lp 1)])) (lm pN (ap (bv 1) (cn k10 [(lp 1)])) (ap (ap (cn k13 [(lp 0)]) (ap (bv 3) (cn k9 [(lp 1)]))) (ap (ap (ap (ap (ap (cn k15 [(lp 0), (lp 1)]) (bv 3)) (bv 2)) (bv 1)) (bv 0)) (cn k9 [(lp 1)])))))))
def p2 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k12 [0, 1] (pi (pZ [0]) (pi pN (cn k7 [(lp 1)]) (st (lp 0))) (pi (pZ [0]) (pi pN (cn k8 [(lp 1)]) (st (lp 0))) (pi (pZ [0]) (ap (bv 1) (cn k9 [(lp 1)])) (pi (pZ [0]) (ap (bv 1) (cn k10 [(lp 1)])) (pi (pZ [0]) (cn k8 [(lp 1)]) (ap (bv 3) (bv 0)))))))) (lm (pZ [0]) (pi pN (cn k7 [(lp 1)]) (st (lp 0))) (lm (pZ [0]) (pi pN (cn k8 [(lp 1)]) (st (lp 0))) (lm (pZ [0]) (ap (bv 1) (cn k9 [(lp 1)])) (lm (pZ [0]) (ap (bv 1) (cn k10 [(lp 1)])) (lm (pZ [0]) (cn k8 [(lp 1)]) (ap (ap (ap (ap (ap (cn k16 [(lp 0), (lp 1)]) (lm pN (cn k17 [(lp 1)]) (lm pN (ap (cn k18 [(lp 1)]) (bv 0)) (ap (ap (ap (ap (ap (cn k19 [(lim (ls (lp 1)) (ls (lp 0))), (lp 1)]) (lm pN (cn k17 [(lp 1)]) (pi pN (ap (cn k18 [(lp 1)]) (bv 0)) (st (lp 0))))) (bv 6)) (bv 5)) (bv 1)) (bv 0))))) (bv 2)) (bv 1)) (cn k20 [(lp 1)])) (bv 0))))))) (ReducibilityHint.regular 2)
def p3 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k15 [0, 1] (pi (pZ [0]) (pi pN (cn k7 [(lp 1)]) (st (lp 0))) (pi (pZ [0]) (pi pN (cn k8 [(lp 1)]) (st (lp 0))) (pi (pZ [0]) (ap (bv 1) (cn k9 [(lp 1)])) (pi (pZ [0]) (ap (bv 1) (cn k10 [(lp 1)])) (pi (pZ [0]) (cn k7 [(lp 1)]) (ap (bv 4) (bv 0)))))))) (lm (pZ [0]) (pi pN (cn k7 [(lp 1)]) (st (lp 0))) (lm (pZ [0]) (pi pN (cn k8 [(lp 1)]) (st (lp 0))) (lm (pZ [0]) (ap (bv 1) (cn k9 [(lp 1)])) (lm (pZ [0]) (ap (bv 1) (cn k10 [(lp 1)])) (lm (pZ [0]) (cn k7 [(lp 1)]) (ap (ap (ap (ap (ap (cn k16 [(lp 0), (lp 1)]) (lm pN (cn k17 [(lp 1)]) (lm pN (ap (cn k18 [(lp 1)]) (bv 0)) (ap (ap (ap (ap (ap (cn k19 [(lim (ls (lp 1)) (ls (lp 0))), (lp 1)]) (lm pN (cn k17 [(lp 1)]) (pi pN (ap (cn k18 [(lp 1)]) (bv 0)) (st (lp 0))))) (bv 6)) (bv 5)) (bv 1)) (bv 0))))) (bv 2)) (bv 1)) (cn k21 [(lp 1)])) (bv 0))))))) (ReducibilityHint.regular 2)
def p4 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k10 [0] (cn k8 [(lp 0)])) (cn k22 [(lp 0)]) (ReducibilityHint.regular 1)
def p5 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k9 [0] (cn k7 [(lp 0)])) (cn k23 [(lp 0)]) (ReducibilityHint.regular 1)
def p6 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k8 [0] (st (ls (lp 0)))) (ap (cn k18 [(lp 0)]) (cn k20 [(lp 0)])) (ReducibilityHint.regular 1)
def p7 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k7 [0] (st (ls (lp 0)))) (ap (cn k18 [(lp 0)]) (cn k21 [(lp 0)])) (ReducibilityHint.regular 1)
def p8 : ConstantInfo .anon :=
  ConstantInfo.recInfo (cv k16 [1, 0] (pi (pZ [1]) (pi pN (cn k17 [(lp 0)]) (pi pN (ap (cn k18 [(lp 0)]) (bv 0)) (st (lp 1)))) (pi (pZ [1]) (ap (ap (bv 0) (cn k21 [(lp 0)])) (cn k23 [(lp 0)])) (pi (pZ [1]) (ap (ap (bv 1) (cn k20 [(lp 0)])) (cn k22 [(lp 0)])) (pi (pZ [1]) (cn k17 [(lp 0)]) (pi (pZ [1]) (ap (cn k18 [(lp 0)]) (bv 0)) (ap (ap (bv 4) (bv 1)) (bv 0)))))))) 4 3 [(RecRule.mk k23 0 0 RecRuleFire.plain (lm (pZ [1]) (pi pN (cn k17 [(lp 0)]) (pi pN (ap (cn k18 [(lp 0)]) (bv 0)) (st (lp 1)))) (lm (pZ [1]) (ap (ap (bv 0) (cn k21 [(lp 0)])) (cn k23 [(lp 0)])) (lm (pZ [1]) (ap (ap (bv 1) (cn k20 [(lp 0)])) (cn k22 [(lp 0)])) (bv 1)))) false false true), (RecRule.mk k22 0 0 RecRuleFire.plain (lm (pZ [1]) (pi pN (cn k17 [(lp 0)]) (pi pN (ap (cn k18 [(lp 0)]) (bv 0)) (st (lp 1)))) (lm (pZ [1]) (ap (ap (bv 0) (cn k21 [(lp 0)])) (cn k23 [(lp 0)])) (lm (pZ [1]) (ap (ap (bv 1) (cn k20 [(lp 0)])) (cn k22 [(lp 0)])) (bv 0)))) false false true)]
def p9 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k22 [0] (ap (cn k18 [(lp 0)]) (cn k20 [(lp 0)]))) 0 0
def p10 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k23 [0] (ap (cn k18 [(lp 0)]) (cn k21 [(lp 0)]))) 0 0
def p11 : ConstantInfo .anon :=
  ConstantInfo.indInfo (cv k18 [0] (pi pN (cn k17 [(lp 0)]) (st (ls (lp 0))))) { eta := false, etaCtor := none, etaParams := 0, etaFields := 0, unitlike := false, unitParams := 0, ruleK := false, sortZ := (pZ []) }
def p12 : ConstantInfo .anon :=
  ConstantInfo.recInfo (cv k19 [1, 0] (pi (pZ [1]) (pi pN (cn k17 [(lp 0)]) (st (lp 1))) (pi (pZ [1]) (ap (bv 0) (cn k21 [(lp 0)])) (pi (pZ [1]) (ap (bv 1) (cn k20 [(lp 0)])) (pi (pZ [1]) (cn k17 [(lp 0)]) (ap (bv 3) (bv 0))))))) 3 3 [(RecRule.mk k21 0 0 RecRuleFire.plain (lm (pZ [1]) (pi pN (cn k17 [(lp 0)]) (st (lp 1))) (lm (pZ [1]) (ap (bv 0) (cn k21 [(lp 0)])) (lm (pZ [1]) (ap (bv 1) (cn k20 [(lp 0)])) (bv 1)))) false false true), (RecRule.mk k20 0 0 RecRuleFire.plain (lm (pZ [1]) (pi pN (cn k17 [(lp 0)]) (st (lp 1))) (lm (pZ [1]) (ap (bv 0) (cn k21 [(lp 0)])) (lm (pZ [1]) (ap (bv 1) (cn k20 [(lp 0)])) (bv 0)))) false false true)]
def p13 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k20 [0] (cn k17 [(lp 0)])) 0 0
def p14 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k21 [0] (cn k17 [(lp 0)])) 0 0
def p15 : ConstantInfo .anon :=
  ConstantInfo.indInfo (cv k17 [0] (st (ls lz))) { eta := false, etaCtor := none, etaParams := 0, etaFields := 0, unitlike := false, unitParams := 0, ruleK := false, sortZ := (pZ []) }
def p16 : ConstantInfo .anon :=
  ConstantInfo.recInfo (cv k24 [1, 0] (pi (pZ [1]) (st (ls (lp 0))) (pi (pZ [1]) (pi pN (ap (cn k25 [(lp 0)]) (bv 0)) (st (lp 1))) (pi (pZ [1]) (ap (bv 0) (ap (cn k26 [(lp 0)]) (bv 1))) (pi (pZ [1]) (pi (pZ [1]) (bv 2) (pi (pZ [1]) (ap (cn k25 [(lp 0)]) (bv 3)) (pi (pZ [1]) (ap (bv 3) (bv 0)) (ap (bv 4) (ap (ap (ap (cn k27 [(lp 0)]) (bv 5)) (bv 2)) (bv 1)))))) (pi (pZ [1]) (ap (cn k25 [(lp 0)]) (bv 3)) (ap (bv 3) (bv 0)))))))) 4 4 [(RecRule.mk k26 0 1 RecRuleFire.plain (lm (pZ [1]) (st (ls (lp 0))) (lm (pZ [1]) (pi pN (ap (cn k25 [(lp 0)]) (bv 0)) (st (lp 1))) (lm (pZ [1]) (ap (bv 0) (ap (cn k26 [(lp 0)]) (bv 1))) (lm (pZ [1]) (pi (pZ [1]) (bv 2) (pi (pZ [1]) (ap (cn k25 [(lp 0)]) (bv 3)) (pi (pZ [1]) (ap (bv 3) (bv 0)) (ap (bv 4) (ap (ap (ap (cn k27 [(lp 0)]) (bv 5)) (bv 2)) (bv 1)))))) (bv 1))))) false false true), (RecRule.mk k27 2 1 RecRuleFire.plain (lm (pZ [1]) (st (ls (lp 0))) (lm (pZ [1]) (pi pN (ap (cn k25 [(lp 0)]) (bv 0)) (st (lp 1))) (lm (pZ [1]) (ap (bv 0) (ap (cn k26 [(lp 0)]) (bv 1))) (lm (pZ [1]) (pi (pZ [1]) (bv 2) (pi (pZ [1]) (ap (cn k25 [(lp 0)]) (bv 3)) (pi (pZ [1]) (ap (bv 3) (bv 0)) (ap (bv 4) (ap (ap (ap (cn k27 [(lp 0)]) (bv 5)) (bv 2)) (bv 1)))))) (lm (pZ [1]) (bv 3) (lm (pZ [1]) (ap (cn k25 [(lp 0)]) (bv 4)) (ap (ap (ap (bv 2) (bv 1)) (bv 0)) (ap (ap (ap (ap (ap (cn k24 [(lp 1), (lp 0)]) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (bv 0))))))))) false false true)]
def p17 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k27 [0] (pi pN (st (ls (lp 0))) (pi pN (bv 0) (pi pN (ap (cn k25 [(lp 0)]) (bv 1)) (ap (cn k25 [(lp 0)]) (bv 2)))))) 1 2
def p18 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k26 [0] (pi pN (st (ls (lp 0))) (ap (cn k25 [(lp 0)]) (bv 0)))) 1 0
def p19 : ConstantInfo .anon :=
  ConstantInfo.indInfo (cv k25 [0] (pi pN (st (ls (lp 0))) (st (ls (lp 0))))) { eta := false, etaCtor := none, etaParams := 0, etaFields := 0, unitlike := false, unitParams := 0, ruleK := false, sortZ := (pZ []) }
def p20 : ConstantInfo .anon :=
  ConstantInfo.recInfo (cv k28 [1, 0] (pi (pZ [1]) (pi pN (cn k29 [(lp 0)]) (st (lp 1))) (pi (pZ [1]) (ap (bv 0) (cn k30 [(lp 0)])) (pi (pZ [1]) (cn k29 [(lp 0)]) (ap (bv 2) (bv 0)))))) 2 2 [(RecRule.mk k30 0 0 RecRuleFire.plain (lm (pZ [1]) (pi pN (cn k29 [(lp 0)]) (st (lp 1))) (lm (pZ [1]) (ap (bv 0) (cn k30 [(lp 0)])) (bv 0))) false true true)]
def p21 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k30 [0] (cn k29 [(lp 0)])) 0 0
def p22 : ConstantInfo .anon :=
  ConstantInfo.indInfo (cv k29 [0] (st (lp 0))) { eta := true, etaCtor := (some k30), etaParams := 0, etaFields := 0, unitlike := true, unitParams := 0, ruleK := false, sortZ := (pZ [0]) }
def p23 : ConstantInfo .anon :=
  ConstantInfo.recInfo (cv k31 [1, 0] (pi (pZ [1]) (st (lp 0)) (pi (pZ [1]) (bv 0) (pi (pZ [1]) (pi pN (bv 1) (pi pN (ap (ap (ap (cn k11 [(lp 0)]) (bv 2)) (bv 1)) (bv 0)) (st (lp 1)))) (pi (pZ [1]) (ap (ap (bv 0) (bv 1)) (ap (ap (cn k13 [(lp 0)]) (bv 2)) (bv 1))) (pi (pZ [1]) (bv 3) (pi (pZ [1]) (ap (ap (ap (cn k11 [(lp 0)]) (bv 4)) (bv 3)) (bv 0)) (ap (ap (bv 3) (bv 1)) (bv 0))))))))) 5 4 [(RecRule.mk k13 0 2 RecRuleFire.plain (lm (pZ [1]) (st (lp 0)) (lm (pZ [1]) (bv 0) (lm (pZ [1]) (pi pN (bv 1) (pi pN (ap (ap (ap (cn k11 [(lp 0)]) (bv 2)) (bv 1)) (bv 0)) (st (lp 1)))) (lm (pZ [1]) (ap (ap (bv 0) (bv 1)) (ap (ap (cn k13 [(lp 0)]) (bv 2)) (bv 1))) (bv 0))))) true false true)]
def p24 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k13 [0] (pi (pZ []) (st (lp 0)) (pi (pZ []) (bv 0) (ap (ap (ap (cn k11 [(lp 0)]) (bv 1)) (bv 0)) (bv 0))))) 2 0
def p25 : ConstantInfo .anon :=
  ConstantInfo.indInfo (cv k11 [0] (pi pN (st (lp 0)) (pi pN (bv 0) (pi pN (bv 1) (st lz))))) { eta := false, etaCtor := none, etaParams := 0, etaFields := 0, unitlike := false, unitParams := 0, ruleK := true, sortZ := (pZ []) }
def pre : List (ConstantInfo .anon) :=
  [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25]

/-- The alias group, newest first. -/
def a0 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k33 [1, 0] (pi (pZ []) (pi pN (cn k7 [(lp 0)]) (st (lp 1))) (pi (pZ []) (pi pN (cn k8 [(lp 0)]) (st (lp 1))) (pi (pZ []) (ap (bv 1) (cn k9 [(lp 0)])) (pi (pZ []) (ap (bv 1) (cn k10 [(lp 0)])) (ap (ap (ap (cn k11 [(lp 1)]) (ap (bv 2) (cn k10 [(lp 0)]))) (ap (ap (ap (ap (ap (cn k32 [(lp 1), (lp 0)]) (bv 3)) (bv 2)) (bv 1)) (bv 0)) (cn k34 [(lp 0)]))) (bv 0))))))) (cn k6 [(lp 1), (lp 0)]) ReducibilityHint.abbrev
def a1 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k36 [1, 0] (pi (pZ []) (pi pN (cn k7 [(lp 0)]) (st (lp 1))) (pi (pZ []) (pi pN (cn k8 [(lp 0)]) (st (lp 1))) (pi (pZ []) (ap (bv 1) (cn k9 [(lp 0)])) (pi (pZ []) (ap (bv 1) (cn k10 [(lp 0)])) (ap (ap (ap (cn k11 [(lp 1)]) (ap (bv 3) (cn k9 [(lp 0)]))) (ap (ap (ap (ap (ap (cn k35 [(lp 1), (lp 0)]) (bv 3)) (bv 2)) (bv 1)) (bv 0)) (cn k37 [(lp 0)]))) (bv 1))))))) (cn k14 [(lp 1), (lp 0)]) ReducibilityHint.abbrev
def a2 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k32 [1, 0] (pi (pZ [1]) (pi pN (cn k38 [(lp 0)]) (st (lp 1))) (pi (pZ [1]) (pi pN (cn k39 [(lp 0)]) (st (lp 1))) (pi (pZ [1]) (ap (bv 1) (cn k37 [(lp 0)])) (pi (pZ [1]) (ap (bv 1) (cn k34 [(lp 0)])) (pi (pZ [1]) (cn k39 [(lp 0)]) (ap (bv 3) (bv 0)))))))) (cn k12 [(lp 1), (lp 0)]) ReducibilityHint.abbrev
def a3 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k35 [1, 0] (pi (pZ [1]) (pi pN (cn k38 [(lp 0)]) (st (lp 1))) (pi (pZ [1]) (pi pN (cn k39 [(lp 0)]) (st (lp 1))) (pi (pZ [1]) (ap (bv 1) (cn k37 [(lp 0)])) (pi (pZ [1]) (ap (bv 1) (cn k34 [(lp 0)])) (pi (pZ [1]) (cn k38 [(lp 0)]) (ap (bv 4) (bv 0)))))))) (cn k15 [(lp 1), (lp 0)]) ReducibilityHint.abbrev
def a4 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k34 [0] (cn k39 [(lp 0)])) (cn k10 [(lp 0)]) ReducibilityHint.abbrev
def a5 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k37 [0] (cn k38 [(lp 0)])) (cn k9 [(lp 0)]) ReducibilityHint.abbrev
def a6 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k39 [0] (st (ls (lp 0)))) (cn k8 [(lp 0)]) ReducibilityHint.abbrev
def a7 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k38 [0] (st (ls (lp 0)))) (cn k7 [(lp 0)]) ReducibilityHint.abbrev
def aliases : List (ConstantInfo .anon) :=
  [a0, a1, a2, a3, a4, a5, a6, a7]

/-- The alias table. -/
def tbl : List (KKey × KKey) :=
  [(k33, k6), (k36, k14), (k32, k12), (k35, k15), (k34, k10), (k37, k9), (k39, k8), (k38, k7)]

/-- The annotated types of the types and constructors. -/
def tysM : List KExpr :=
  [(st (ls (lp 0))),
   (st (ls (lp 0))),
   (cn k0 [(lp 0)]),
   (cn k1 [(lp 0)])]

/-- The annotated types of the recursors. -/
def tysR : List KExpr :=
  [(pi (pZ [1]) (pi pN (cn k0 [(lp 0)]) (st (lp 1))) (pi (pZ [1]) (pi pN (cn k1 [(lp 0)]) (st (lp 1))) (pi (pZ [1]) (ap (bv 1) (cn k2 [(lp 0)])) (pi (pZ [1]) (ap (bv 1) (cn k3 [(lp 0)])) (pi (pZ [1]) (cn k0 [(lp 0)]) (ap (bv 4) (bv 0))))))),
   (pi (pZ [1]) (pi pN (cn k0 [(lp 0)]) (st (lp 1))) (pi (pZ [1]) (pi pN (cn k1 [(lp 0)]) (st (lp 1))) (pi (pZ [1]) (ap (bv 1) (cn k2 [(lp 0)])) (pi (pZ [1]) (ap (bv 1) (cn k3 [(lp 0)])) (pi (pZ [1]) (cn k1 [(lp 0)]) (ap (bv 3) (bv 0)))))))]

/-- The annotated right-hand sides of the recursors' rules. -/
def rhsss : List (List KExpr) :=
  [[(lm (pZ [1]) (pi pN (cn k0 [(lp 0)]) (st (lp 1))) (lm (pZ [1]) (pi pN (cn k1 [(lp 0)]) (st (lp 1))) (lm (pZ [1]) (ap (bv 1) (cn k2 [(lp 0)])) (lm (pZ [1]) (ap (bv 1) (cn k3 [(lp 0)])) (bv 1)))))],
   [(lm (pZ [1]) (pi pN (cn k0 [(lp 0)]) (st (lp 1))) (lm (pZ [1]) (pi pN (cn k1 [(lp 0)]) (st (lp 1))) (lm (pZ [1]) (ap (bv 1) (cn k2 [(lp 0)])) (lm (pZ [1]) (ap (bv 1) (cn k3 [(lp 0)])) (bv 0)))))]]

/-- **The aliases are an alias group over the prefix** (evaluated). -/
theorem group_ok : isOk (aliasGroupCheck ⟨pre⟩ tbl aliases) = true := by decide +kernel

set_option maxHeartbeats 40000000 in
/-- **The search for the renamed record over the family package succeeds** (evaluated). -/
theorem record_ok :
    isOk (famRecordCheck 200 tbl ⟨aliases ++ pre⟩ blk tysM tysR rhsss) = true := by
  decide +kernel

/-- Each alias is rooted at a member of the block (evaluated). -/
theorem roots_ok : ∀ a ∈ aliases, ∃ ci ∈ blk, a.name.base = ci.name := by decide +kernel

/-- **The family step's conclusion holds of this family**: an alias group over the prefix, each
alias rooted at a member of the block, and IxC's renamed record of the block over the family
package at the environment that stores the aliases. -/
theorem inhabited :
    ∃ (h : KKey → KKey) (as : List (ConstantInfo .anon)) (env₂ : Env .anon),
      AliasGroup ⟨pre⟩ h as ∧ (∀ a ∈ as, ∃ ci ∈ blk, a.name.base = ci.name) ∧
      DeclIndRenRunJ (famJ h) ⟨as ++ pre⟩ blk env₂ := by
  obtain ⟨env₂, -, hd⟩ := famRecord_of_check record_ok
  exact ⟨aliasMap tbl, aliases, env₂, aliasGroup_of_check group_ok, roots_ok, hd⟩

end IxVM.Refinement.Decl.FamilyAlias.Fixtures.LargePair
