import IxVMRefinement.FamilyAlias.AdviceLayout
import IxVMRefinement.FamilyAlias.Fixtures.Terms

/-! # A mutual pair of families indexed by `Nat`

The family step's conclusion at a concrete family (`inhabited`):

    mutual
      inductive EvT : Nat → Type | zero : EvT Nat.zero | succ : (n : Nat) → OdT n → EvT (Nat.succ n)
      inductive OdT : Nat → Type | succ : (n : Nat) → EvT n → OdT (Nat.succ n)
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

namespace IxVM.Refinement.Decl.FamilyAlias.Fixtures.IndexedPair

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule RecRuleFire ReducibilityHint)

set_option maxRecDepth 100000

universe u

def k0 : KKey := Key.id (adr [176, 0, 0])
def k1 : KKey := Key.role (Ix.Kernel.Role.nat)
def k2 : KKey := Key.id (adr [176, 0, 1])
def k3 : KKey := Key.id (adr [176, 0, 2])
def k4 : KKey := Key.role (Ix.Kernel.Role.natZero)
def k5 : KKey := Key.id (adr [176, 0, 3])
def k6 : KKey := Key.role (Ix.Kernel.Role.natSucc)
def k7 : KKey := Key.id (adr [176, 0, 4])
def k8 : KKey := Key.id (adr [176, 0, 5])
def k9 : KKey := Key.id (adr [176, 0, 6])
def k10 : KKey := Key.id (adr [173, 0, 18])
def k11 : KKey := Key.id (adr [173, 0, 9])
def k12 : KKey := Key.id (adr [173, 0, 10])
def k13 : KKey := Key.id (adr [173, 0, 11])
def k14 : KKey := Key.id (adr [173, 0, 12])
def k15 : KKey := Key.id (adr [173, 0, 13])
def k16 : KKey := Key.role (Ix.Kernel.Role.eq)
def k17 : KKey := Key.id (adr [173, 0, 15])
def k18 : KKey := Key.id (adr [173, 0, 14])
def k19 : KKey := Key.role (Ix.Kernel.Role.eqRefl)
def k20 : KKey := Key.id (adr [173, 0, 17])
def k21 : KKey := Key.id (adr [173, 0, 16])
def k22 : KKey := Key.id (adr [173, 0, 8])
def k23 : KKey := Key.id (adr [173, 0, 0])
def k24 : KKey := Key.id (adr [173, 0, 4])
def k25 : KKey := Key.id (adr [173, 0, 3])
def k26 : KKey := Key.id (adr [173, 0, 2])
def k27 : KKey := Key.id (adr [173, 0, 1])
def k28 : KKey := Key.id (adr [173, 0, 7])
def k29 : KKey := Key.id (adr [173, 0, 6])
def k30 : KKey := Key.id (adr [173, 0, 5])
def k31 : KKey := Key.id (adr [176, 0, 200])
def k32 : KKey := Key.role (Ix.Kernel.Role.list)
def k33 : KKey := Key.role (Ix.Kernel.Role.listNil)
def k34 : KKey := Key.role (Ix.Kernel.Role.listCons)
def k35 : KKey := Key.role (Ix.Kernel.Role.natRec)
def k36 : KKey := Key.role (Ix.Kernel.Role.punitRec)
def k37 : KKey := Key.role (Ix.Kernel.Role.punit)
def k38 : KKey := Key.role (Ix.Kernel.Role.punitUnit)
def k39 : KKey := Key.role (Ix.Kernel.Role.eqRec)
def k40 : KKey := Key.aux k9 (Ix.Kernel.Derived.model)
def k41 : KKey := Key.aux k40 (Ix.Kernel.Derived.iota 0)
def k42 : KKey := Key.aux k7 (Ix.Kernel.Derived.model)
def k43 : KKey := Key.aux k8 (Ix.Kernel.Derived.model)
def k44 : KKey := Key.aux k43 (Ix.Kernel.Derived.iota 1)
def k45 : KKey := Key.aux k5 (Ix.Kernel.Derived.model)
def k46 : KKey := Key.aux k43 (Ix.Kernel.Derived.iota 0)
def k47 : KKey := Key.aux k3 (Ix.Kernel.Derived.model)
def k48 : KKey := Key.aux k0 (Ix.Kernel.Derived.model)
def k49 : KKey := Key.aux k2 (Ix.Kernel.Derived.model)

/-- The block, as read. -/
def b0 : ConstantInfo .anon :=
  ConstantInfo.indInfo (cv k0 [] (pi pN (cn k1 []) (st (ls lz)))) { eta := false, etaCtor := none, etaParams := 0, etaFields := 0, unitlike := false, unitParams := 0, ruleK := false, sortZ := (pZ []) }
def b1 : ConstantInfo .anon :=
  ConstantInfo.indInfo (cv k2 [] (pi pN (cn k1 []) (st (ls lz)))) { eta := false, etaCtor := none, etaParams := 0, etaFields := 0, unitlike := false, unitParams := 0, ruleK := false, sortZ := (pZ []) }
def b2 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k3 [] (ap (cn k0 []) (cn k4 []))) 0 0
def b3 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k5 [] (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (ap (cn k0 []) (ap (cn k6 []) (bv 1)))))) 0 2
def b4 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k7 [] (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (ap (cn k2 []) (ap (cn k6 []) (bv 1)))))) 0 2
def b5 : ConstantInfo .anon :=
  ConstantInfo.recInfo (cv k8 [0] (pi pN (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (st (lp 0)))) (pi pN (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (st (lp 0)))) (pi pN (ap (ap (bv 1) (cn k4 [])) (cn k3 [])) (pi pN (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (pi pN (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k5 []) (bv 2)) (bv 1)))))) (pi pN (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (pi pN (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k7 []) (bv 2)) (bv 1)))))) (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (ap (ap (bv 6) (bv 1)) (bv 0)))))))))) 6 5 [(RecRule.mk k3 0 0 RecRuleFire.inert (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (st (lp 0)))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (st (lp 0)))) (lm pN (ap (ap (bv 1) (cn k4 [])) (cn k3 [])) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (pi pN (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k5 []) (bv 2)) (bv 1)))))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (pi pN (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k7 []) (bv 2)) (bv 1)))))) (bv 2)))))) false false false), (RecRule.mk k5 2 0 RecRuleFire.inert (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (st (lp 0)))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (st (lp 0)))) (lm pN (ap (ap (bv 1) (cn k4 [])) (cn k3 [])) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (pi pN (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k5 []) (bv 2)) (bv 1)))))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (pi pN (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k7 []) (bv 2)) (bv 1)))))) (lm pN (cn k1 []) (lm pN (ap (cn k2 []) (bv 0)) (ap (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (ap (ap (ap (ap (ap (cn k9 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0)))))))))) false false false)]
def b6 : ConstantInfo .anon :=
  ConstantInfo.recInfo (cv k9 [0] (pi pN (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (st (lp 0)))) (pi pN (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (st (lp 0)))) (pi pN (ap (ap (bv 1) (cn k4 [])) (cn k3 [])) (pi pN (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (pi pN (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k5 []) (bv 2)) (bv 1)))))) (pi pN (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (pi pN (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k7 []) (bv 2)) (bv 1)))))) (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (ap (ap (bv 5) (bv 1)) (bv 0)))))))))) 6 5 [(RecRule.mk k7 2 0 RecRuleFire.inert (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (st (lp 0)))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (st (lp 0)))) (lm pN (ap (ap (bv 1) (cn k4 [])) (cn k3 [])) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (pi pN (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k5 []) (bv 2)) (bv 1)))))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (pi pN (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k7 []) (bv 2)) (bv 1)))))) (lm pN (cn k1 []) (lm pN (ap (cn k0 []) (bv 0)) (ap (ap (ap (bv 2) (bv 1)) (bv 0)) (ap (ap (ap (ap (ap (ap (ap (cn k8 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0)))))))))) false false false)]
def blk : List (ConstantInfo .anon) :=
  [b0, b1, b2, b3, b4, b5, b6]

/-- The prefix in the advice layout, newest first. -/
def p0 : ConstantInfo .anon :=
  ConstantInfo.thmInfo (cv k10 [0] (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (pi (pZ []) (cn k1 []) (pi (pZ []) (ap (cn k11 []) (bv 0)) (ap (ap (ap (cn k16 [(lp 0)]) (ap (ap (bv 5) (ap (cn k6 []) (bv 1))) (ap (ap (cn k15 []) (bv 1)) (bv 0)))) (ap (ap (ap (ap (ap (ap (ap (cn k17 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (ap (cn k6 []) (bv 1))) (ap (ap (cn k15 []) (bv 1)) (bv 0)))) (ap (ap (ap (bv 2) (bv 1)) (bv 0)) (ap (ap (ap (ap (ap (ap (ap (cn k18 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0)))))))))))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (lm pN (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (pi pN (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (pi pN (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (lm pN (cn k1 []) (lm pN (ap (cn k11 []) (bv 0)) (ap (ap (cn k19 [(lp 0)]) (ap (ap (bv 5) (ap (cn k6 []) (bv 1))) (ap (ap (cn k15 []) (bv 1)) (bv 0)))) (ap (ap (ap (ap (ap (ap (ap (cn k17 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (ap (cn k6 []) (bv 1))) (ap (ap (cn k15 []) (bv 1)) (bv 0)))))))))))
def p1 : ConstantInfo .anon :=
  ConstantInfo.thmInfo (cv k20 [0] (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (pi (pZ []) (cn k1 []) (pi (pZ []) (ap (cn k12 []) (bv 0)) (ap (ap (ap (cn k16 [(lp 0)]) (ap (ap (bv 6) (ap (cn k6 []) (bv 1))) (ap (ap (cn k14 []) (bv 1)) (bv 0)))) (ap (ap (ap (ap (ap (ap (ap (cn k18 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (ap (cn k6 []) (bv 1))) (ap (ap (cn k14 []) (bv 1)) (bv 0)))) (ap (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (ap (ap (ap (ap (ap (cn k17 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0)))))))))))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (lm pN (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (pi pN (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (pi pN (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (lm pN (cn k1 []) (lm pN (ap (cn k12 []) (bv 0)) (ap (ap (cn k19 [(lp 0)]) (ap (ap (bv 6) (ap (cn k6 []) (bv 1))) (ap (ap (cn k14 []) (bv 1)) (bv 0)))) (ap (ap (ap (ap (ap (ap (ap (cn k18 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (ap (cn k6 []) (bv 1))) (ap (ap (cn k14 []) (bv 1)) (bv 0)))))))))))
def p2 : ConstantInfo .anon :=
  ConstantInfo.thmInfo (cv k21 [0] (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (ap (ap (ap (cn k16 [(lp 0)]) (ap (ap (bv 4) (cn k4 [])) (cn k13 []))) (ap (ap (ap (ap (ap (ap (ap (cn k18 [(lp 0)]) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0)) (cn k4 [])) (cn k13 []))) (bv 2)))))))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (lm pN (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (pi pN (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (pi pN (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (ap (ap (cn k19 [(lp 0)]) (ap (ap (bv 4) (cn k4 [])) (cn k13 []))) (ap (ap (ap (ap (ap (ap (ap (cn k18 [(lp 0)]) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0)) (cn k4 [])) (cn k13 []))))))))
def p3 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k17 [0] (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (ap (ap (bv 5) (bv 1)) (bv 0)))))))))) (lm (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (cn k1 []) (lm (pZ [0]) (ap (cn k12 []) (bv 0)) (ap (ap (ap (ap (ap (ap (cn k22 [(lp 0)]) (lm pN (cn k23 []) (lm pN (ap (cn k24 []) (bv 0)) (ap (ap (ap (ap (ap (cn k25 [(lim (ls lz) (ls (lp 0)))]) (lm pN (cn k23 []) (pi pN (ap (cn k24 []) (bv 0)) (st (lp 0))))) (bv 8)) (bv 7)) (bv 1)) (bv 0))))) (bv 4)) (bv 3)) (bv 2)) (ap (cn k26 []) (bv 1))) (bv 0))))))))) (ReducibilityHint.regular 3)
def p4 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k18 [0] (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (ap (ap (bv 6) (bv 1)) (bv 0)))))))))) (lm (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (cn k1 []) (lm (pZ [0]) (ap (cn k11 []) (bv 0)) (ap (ap (ap (ap (ap (ap (cn k22 [(lp 0)]) (lm pN (cn k23 []) (lm pN (ap (cn k24 []) (bv 0)) (ap (ap (ap (ap (ap (cn k25 [(lim (ls lz) (ls (lp 0)))]) (lm pN (cn k23 []) (pi pN (ap (cn k24 []) (bv 0)) (st (lp 0))))) (bv 8)) (bv 7)) (bv 1)) (bv 0))))) (bv 4)) (bv 3)) (bv 2)) (ap (cn k27 []) (bv 1))) (bv 0))))))))) (ReducibilityHint.regular 3)
def p5 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k15 [] (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (ap (cn k12 []) (ap (cn k6 []) (bv 1)))))) (lm pN (cn k1 []) (lm pN (ap (cn k11 []) (bv 0)) (ap (ap (cn k28 []) (bv 1)) (bv 0)))) (ReducibilityHint.regular 2)
def p6 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k14 [] (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (ap (cn k11 []) (ap (cn k6 []) (bv 1)))))) (lm pN (cn k1 []) (lm pN (ap (cn k12 []) (bv 0)) (ap (ap (cn k29 []) (bv 1)) (bv 0)))) (ReducibilityHint.regular 2)
def p7 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k13 [] (ap (cn k11 []) (cn k4 []))) (cn k30 []) (ReducibilityHint.regular 1)
def p8 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k12 [] (pi pN (cn k1 []) (st (ls lz)))) (lm pN (cn k1 []) (ap (cn k24 []) (ap (cn k26 []) (bv 0)))) (ReducibilityHint.regular 1)
def p9 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k11 [] (pi pN (cn k1 []) (st (ls lz)))) (lm pN (cn k1 []) (ap (cn k24 []) (ap (cn k27 []) (bv 0)))) (ReducibilityHint.regular 1)
def p10 : ConstantInfo .anon :=
  ConstantInfo.recInfo (cv k22 [0] (pi (pZ [0]) (pi pN (cn k23 []) (pi pN (ap (cn k24 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (ap (ap (bv 0) (ap (cn k27 []) (cn k4 []))) (cn k30 [])) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k24 []) (ap (cn k26 []) (bv 0))) (pi (pZ [0]) (ap (ap (bv 3) (ap (cn k26 []) (bv 1))) (bv 0)) (ap (ap (bv 4) (ap (cn k27 []) (ap (cn k6 []) (bv 2)))) (ap (ap (cn k29 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k24 []) (ap (cn k27 []) (bv 0))) (pi (pZ [0]) (ap (ap (bv 4) (ap (cn k27 []) (bv 1))) (bv 0)) (ap (ap (bv 5) (ap (cn k26 []) (ap (cn k6 []) (bv 2)))) (ap (ap (cn k28 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (cn k23 []) (pi (pZ [0]) (ap (cn k24 []) (bv 0)) (ap (ap (bv 5) (bv 1)) (bv 0))))))))) 5 4 [(RecRule.mk k30 0 0 RecRuleFire.plain (lm (pZ [0]) (pi pN (cn k23 []) (pi pN (ap (cn k24 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (ap (ap (bv 0) (ap (cn k27 []) (cn k4 []))) (cn k30 [])) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k24 []) (ap (cn k26 []) (bv 0))) (pi (pZ [0]) (ap (ap (bv 3) (ap (cn k26 []) (bv 1))) (bv 0)) (ap (ap (bv 4) (ap (cn k27 []) (ap (cn k6 []) (bv 2)))) (ap (ap (cn k29 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k24 []) (ap (cn k27 []) (bv 0))) (pi (pZ [0]) (ap (ap (bv 4) (ap (cn k27 []) (bv 1))) (bv 0)) (ap (ap (bv 5) (ap (cn k26 []) (ap (cn k6 []) (bv 2)))) (ap (ap (cn k28 []) (bv 2)) (bv 1)))))) (bv 2))))) false false true), (RecRule.mk k29 2 0 RecRuleFire.plain (lm (pZ [0]) (pi pN (cn k23 []) (pi pN (ap (cn k24 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (ap (ap (bv 0) (ap (cn k27 []) (cn k4 []))) (cn k30 [])) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k24 []) (ap (cn k26 []) (bv 0))) (pi (pZ [0]) (ap (ap (bv 3) (ap (cn k26 []) (bv 1))) (bv 0)) (ap (ap (bv 4) (ap (cn k27 []) (ap (cn k6 []) (bv 2)))) (ap (ap (cn k29 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k24 []) (ap (cn k27 []) (bv 0))) (pi (pZ [0]) (ap (ap (bv 4) (ap (cn k27 []) (bv 1))) (bv 0)) (ap (ap (bv 5) (ap (cn k26 []) (ap (cn k6 []) (bv 2)))) (ap (ap (cn k28 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (cn k1 []) (lm (pZ [0]) (ap (cn k24 []) (ap (cn k26 []) (bv 0))) (ap (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (ap (ap (ap (ap (cn k22 [(lp 0)]) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (ap (cn k26 []) (bv 1))) (bv 0))))))))) false false true), (RecRule.mk k28 2 0 RecRuleFire.plain (lm (pZ [0]) (pi pN (cn k23 []) (pi pN (ap (cn k24 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (ap (ap (bv 0) (ap (cn k27 []) (cn k4 []))) (cn k30 [])) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k24 []) (ap (cn k26 []) (bv 0))) (pi (pZ [0]) (ap (ap (bv 3) (ap (cn k26 []) (bv 1))) (bv 0)) (ap (ap (bv 4) (ap (cn k27 []) (ap (cn k6 []) (bv 2)))) (ap (ap (cn k29 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k24 []) (ap (cn k27 []) (bv 0))) (pi (pZ [0]) (ap (ap (bv 4) (ap (cn k27 []) (bv 1))) (bv 0)) (ap (ap (bv 5) (ap (cn k26 []) (ap (cn k6 []) (bv 2)))) (ap (ap (cn k28 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (cn k1 []) (lm (pZ [0]) (ap (cn k24 []) (ap (cn k27 []) (bv 0))) (ap (ap (ap (bv 2) (bv 1)) (bv 0)) (ap (ap (ap (ap (ap (ap (cn k22 [(lp 0)]) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (ap (cn k27 []) (bv 1))) (bv 0))))))))) false false true)]
def p11 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k28 [] (pi pN (cn k1 []) (pi pN (ap (cn k24 []) (ap (cn k27 []) (bv 0))) (ap (cn k24 []) (ap (cn k26 []) (ap (cn k6 []) (bv 1))))))) 0 2
def p12 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k29 [] (pi pN (cn k1 []) (pi pN (ap (cn k24 []) (ap (cn k26 []) (bv 0))) (ap (cn k24 []) (ap (cn k27 []) (ap (cn k6 []) (bv 1))))))) 0 2
def p13 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k30 [] (ap (cn k24 []) (ap (cn k27 []) (cn k4 [])))) 0 0
def p14 : ConstantInfo .anon :=
  ConstantInfo.indInfo (cv k24 [] (pi pN (cn k23 []) (st (ls lz)))) { eta := false, etaCtor := none, etaParams := 0, etaFields := 0, unitlike := false, unitParams := 0, ruleK := false, sortZ := (pZ []) }
def p15 : ConstantInfo .anon :=
  ConstantInfo.recInfo (cv k25 [0] (pi (pZ [0]) (pi pN (cn k23 []) (st (lp 0))) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (ap (bv 1) (ap (cn k27 []) (bv 0)))) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (ap (bv 2) (ap (cn k26 []) (bv 0)))) (pi (pZ [0]) (cn k23 []) (ap (bv 3) (bv 0))))))) 3 3 [(RecRule.mk k27 1 0 RecRuleFire.plain (lm (pZ [0]) (pi pN (cn k23 []) (st (lp 0))) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (ap (bv 1) (ap (cn k27 []) (bv 0)))) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (ap (bv 2) (ap (cn k26 []) (bv 0)))) (lm (pZ [0]) (cn k1 []) (ap (bv 2) (bv 0)))))) false false true), (RecRule.mk k26 1 0 RecRuleFire.plain (lm (pZ [0]) (pi pN (cn k23 []) (st (lp 0))) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (ap (bv 1) (ap (cn k27 []) (bv 0)))) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (ap (bv 2) (ap (cn k26 []) (bv 0)))) (lm (pZ [0]) (cn k1 []) (ap (bv 1) (bv 0)))))) false false true)]
def p16 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k26 [] (pi pN (cn k1 []) (cn k23 []))) 0 1
def p17 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k27 [] (pi pN (cn k1 []) (cn k23 []))) 0 1
def p18 : ConstantInfo .anon :=
  ConstantInfo.indInfo (cv k23 [] (st (lmx (lmx (ls lz) (ls lz)) (ls lz)))) { eta := false, etaCtor := none, etaParams := 0, etaFields := 0, unitlike := false, unitParams := 0, ruleK := false, sortZ := (pZ []) }
def p19 : ConstantInfo .anon :=
  ConstantInfo.recInfo (cv k31 [1, 0] (pi (pZ [1]) (st (ls (lp 0))) (pi (pZ [1]) (pi pN (ap (cn k32 [(lp 0)]) (bv 0)) (st (lp 1))) (pi (pZ [1]) (ap (bv 0) (ap (cn k33 [(lp 0)]) (bv 1))) (pi (pZ [1]) (pi (pZ [1]) (bv 2) (pi (pZ [1]) (ap (cn k32 [(lp 0)]) (bv 3)) (pi (pZ [1]) (ap (bv 3) (bv 0)) (ap (bv 4) (ap (ap (ap (cn k34 [(lp 0)]) (bv 5)) (bv 2)) (bv 1)))))) (pi (pZ [1]) (ap (cn k32 [(lp 0)]) (bv 3)) (ap (bv 3) (bv 0)))))))) 4 4 [(RecRule.mk k33 0 1 RecRuleFire.plain (lm (pZ [1]) (st (ls (lp 0))) (lm (pZ [1]) (pi pN (ap (cn k32 [(lp 0)]) (bv 0)) (st (lp 1))) (lm (pZ [1]) (ap (bv 0) (ap (cn k33 [(lp 0)]) (bv 1))) (lm (pZ [1]) (pi (pZ [1]) (bv 2) (pi (pZ [1]) (ap (cn k32 [(lp 0)]) (bv 3)) (pi (pZ [1]) (ap (bv 3) (bv 0)) (ap (bv 4) (ap (ap (ap (cn k34 [(lp 0)]) (bv 5)) (bv 2)) (bv 1)))))) (bv 1))))) false false true), (RecRule.mk k34 2 1 RecRuleFire.plain (lm (pZ [1]) (st (ls (lp 0))) (lm (pZ [1]) (pi pN (ap (cn k32 [(lp 0)]) (bv 0)) (st (lp 1))) (lm (pZ [1]) (ap (bv 0) (ap (cn k33 [(lp 0)]) (bv 1))) (lm (pZ [1]) (pi (pZ [1]) (bv 2) (pi (pZ [1]) (ap (cn k32 [(lp 0)]) (bv 3)) (pi (pZ [1]) (ap (bv 3) (bv 0)) (ap (bv 4) (ap (ap (ap (cn k34 [(lp 0)]) (bv 5)) (bv 2)) (bv 1)))))) (lm (pZ [1]) (bv 3) (lm (pZ [1]) (ap (cn k32 [(lp 0)]) (bv 4)) (ap (ap (ap (bv 2) (bv 1)) (bv 0)) (ap (ap (ap (ap (ap (cn k31 [(lp 1), (lp 0)]) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (bv 0))))))))) false false true)]
def p20 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k34 [0] (pi pN (st (ls (lp 0))) (pi pN (bv 0) (pi pN (ap (cn k32 [(lp 0)]) (bv 1)) (ap (cn k32 [(lp 0)]) (bv 2)))))) 1 2
def p21 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k33 [0] (pi pN (st (ls (lp 0))) (ap (cn k32 [(lp 0)]) (bv 0)))) 1 0
def p22 : ConstantInfo .anon :=
  ConstantInfo.indInfo (cv k32 [0] (pi pN (st (ls (lp 0))) (st (ls (lp 0))))) { eta := false, etaCtor := none, etaParams := 0, etaFields := 0, unitlike := false, unitParams := 0, ruleK := false, sortZ := (pZ []) }
def p23 : ConstantInfo .anon :=
  ConstantInfo.recInfo (cv k35 [0] (pi (pZ [0]) (pi pN (cn k1 []) (st (lp 0))) (pi (pZ [0]) (ap (bv 0) (cn k4 [])) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (bv 2) (bv 0)) (ap (bv 3) (ap (cn k6 []) (bv 1))))) (pi (pZ [0]) (cn k1 []) (ap (bv 3) (bv 0))))))) 3 3 [(RecRule.mk k4 0 0 RecRuleFire.plain (lm (pZ [0]) (pi pN (cn k1 []) (st (lp 0))) (lm (pZ [0]) (ap (bv 0) (cn k4 [])) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (bv 2) (bv 0)) (ap (bv 3) (ap (cn k6 []) (bv 1))))) (bv 1)))) false false true), (RecRule.mk k6 1 0 RecRuleFire.plain (lm (pZ [0]) (pi pN (cn k1 []) (st (lp 0))) (lm (pZ [0]) (ap (bv 0) (cn k4 [])) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (bv 2) (bv 0)) (ap (bv 3) (ap (cn k6 []) (bv 1))))) (lm (pZ [0]) (cn k1 []) (ap (ap (bv 1) (bv 0)) (ap (ap (ap (ap (cn k35 [(lp 0)]) (bv 3)) (bv 2)) (bv 1)) (bv 0))))))) false false true)]
def p24 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k6 [] (pi pN (cn k1 []) (cn k1 []))) 0 1
def p25 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k4 [] (cn k1 [])) 0 0
def p26 : ConstantInfo .anon :=
  ConstantInfo.indInfo (cv k1 [] (st (ls lz))) { eta := false, etaCtor := none, etaParams := 0, etaFields := 0, unitlike := false, unitParams := 0, ruleK := false, sortZ := (pZ []) }
def p27 : ConstantInfo .anon :=
  ConstantInfo.recInfo (cv k36 [1, 0] (pi (pZ [1]) (pi pN (cn k37 [(lp 0)]) (st (lp 1))) (pi (pZ [1]) (ap (bv 0) (cn k38 [(lp 0)])) (pi (pZ [1]) (cn k37 [(lp 0)]) (ap (bv 2) (bv 0)))))) 2 2 [(RecRule.mk k38 0 0 RecRuleFire.plain (lm (pZ [1]) (pi pN (cn k37 [(lp 0)]) (st (lp 1))) (lm (pZ [1]) (ap (bv 0) (cn k38 [(lp 0)])) (bv 0))) false true true)]
def p28 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k38 [0] (cn k37 [(lp 0)])) 0 0
def p29 : ConstantInfo .anon :=
  ConstantInfo.indInfo (cv k37 [0] (st (lp 0))) { eta := true, etaCtor := (some k38), etaParams := 0, etaFields := 0, unitlike := true, unitParams := 0, ruleK := false, sortZ := (pZ [0]) }
def p30 : ConstantInfo .anon :=
  ConstantInfo.recInfo (cv k39 [1, 0] (pi (pZ [1]) (st (lp 0)) (pi (pZ [1]) (bv 0) (pi (pZ [1]) (pi pN (bv 1) (pi pN (ap (ap (ap (cn k16 [(lp 0)]) (bv 2)) (bv 1)) (bv 0)) (st (lp 1)))) (pi (pZ [1]) (ap (ap (bv 0) (bv 1)) (ap (ap (cn k19 [(lp 0)]) (bv 2)) (bv 1))) (pi (pZ [1]) (bv 3) (pi (pZ [1]) (ap (ap (ap (cn k16 [(lp 0)]) (bv 4)) (bv 3)) (bv 0)) (ap (ap (bv 3) (bv 1)) (bv 0))))))))) 5 4 [(RecRule.mk k19 0 2 RecRuleFire.plain (lm (pZ [1]) (st (lp 0)) (lm (pZ [1]) (bv 0) (lm (pZ [1]) (pi pN (bv 1) (pi pN (ap (ap (ap (cn k16 [(lp 0)]) (bv 2)) (bv 1)) (bv 0)) (st (lp 1)))) (lm (pZ [1]) (ap (ap (bv 0) (bv 1)) (ap (ap (cn k19 [(lp 0)]) (bv 2)) (bv 1))) (bv 0))))) true false true)]
def p31 : ConstantInfo .anon :=
  ConstantInfo.ctorInfo (cv k19 [0] (pi (pZ []) (st (lp 0)) (pi (pZ []) (bv 0) (ap (ap (ap (cn k16 [(lp 0)]) (bv 1)) (bv 0)) (bv 0))))) 2 0
def p32 : ConstantInfo .anon :=
  ConstantInfo.indInfo (cv k16 [0] (pi pN (st (lp 0)) (pi pN (bv 0) (pi pN (bv 1) (st lz))))) { eta := false, etaCtor := none, etaParams := 0, etaFields := 0, unitlike := false, unitParams := 0, ruleK := true, sortZ := (pZ []) }
def pre : List (ConstantInfo .anon) :=
  [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32]

/-- The alias group, newest first. -/
def a0 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k41 [0] (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (pi (pZ []) (cn k1 []) (pi (pZ []) (ap (cn k11 []) (bv 0)) (ap (ap (ap (cn k16 [(lp 0)]) (ap (ap (bv 5) (ap (cn k6 []) (bv 1))) (ap (ap (cn k15 []) (bv 1)) (bv 0)))) (ap (ap (ap (ap (ap (ap (ap (cn k40 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (ap (cn k6 []) (bv 1))) (ap (ap (cn k42 []) (bv 1)) (bv 0)))) (ap (ap (ap (bv 2) (bv 1)) (bv 0)) (ap (ap (ap (ap (ap (ap (ap (cn k18 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0)))))))))))) (cn k10 [(lp 0)]) ReducibilityHint.abbrev
def a1 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k44 [0] (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (pi (pZ []) (cn k1 []) (pi (pZ []) (ap (cn k12 []) (bv 0)) (ap (ap (ap (cn k16 [(lp 0)]) (ap (ap (bv 6) (ap (cn k6 []) (bv 1))) (ap (ap (cn k14 []) (bv 1)) (bv 0)))) (ap (ap (ap (ap (ap (ap (ap (cn k43 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (ap (cn k6 []) (bv 1))) (ap (ap (cn k45 []) (bv 1)) (bv 0)))) (ap (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (ap (ap (ap (ap (ap (cn k17 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0)))))))))))) (cn k20 [(lp 0)]) ReducibilityHint.abbrev
def a2 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k46 [0] (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (ap (ap (ap (cn k16 [(lp 0)]) (ap (ap (bv 4) (cn k4 [])) (cn k13 []))) (ap (ap (ap (ap (ap (ap (ap (cn k43 [(lp 0)]) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0)) (cn k4 [])) (cn k47 []))) (bv 2)))))))) (cn k21 [(lp 0)]) ReducibilityHint.abbrev
def a3 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k40 [0] (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k48 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k49 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k47 [])) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k49 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k45 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k48 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k42 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k49 []) (bv 0)) (ap (ap (bv 5) (bv 1)) (bv 0)))))))))) (cn k17 [(lp 0)]) ReducibilityHint.abbrev
def a4 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k43 [0] (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k48 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k49 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k47 [])) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k49 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k45 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k48 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k42 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k48 []) (bv 0)) (ap (ap (bv 6) (bv 1)) (bv 0)))))))))) (cn k18 [(lp 0)]) ReducibilityHint.abbrev
def a5 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k42 [] (pi pN (cn k1 []) (pi pN (ap (cn k48 []) (bv 0)) (ap (cn k49 []) (ap (cn k6 []) (bv 1)))))) (cn k15 []) ReducibilityHint.abbrev
def a6 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k45 [] (pi pN (cn k1 []) (pi pN (ap (cn k49 []) (bv 0)) (ap (cn k48 []) (ap (cn k6 []) (bv 1)))))) (cn k14 []) ReducibilityHint.abbrev
def a7 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k47 [] (ap (cn k48 []) (cn k4 []))) (cn k13 []) ReducibilityHint.abbrev
def a8 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k49 [] (pi pN (cn k1 []) (st (ls lz)))) (cn k12 []) ReducibilityHint.abbrev
def a9 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k48 [] (pi pN (cn k1 []) (st (ls lz)))) (cn k11 []) ReducibilityHint.abbrev
def aliases : List (ConstantInfo .anon) :=
  [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]

/-- The alias table. -/
def tbl : List (KKey × KKey) :=
  [(k41, k10), (k44, k20), (k46, k21), (k40, k17), (k43, k18), (k42, k15), (k45, k14), (k47, k13), (k49, k12), (k48, k11)]

/-- The annotated types of the types and constructors. -/
def tysM : List KExpr :=
  [(pi pN (cn k1 []) (st (ls lz))),
   (pi pN (cn k1 []) (st (ls lz))),
   (ap (cn k0 []) (cn k4 [])),
   (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (ap (cn k0 []) (ap (cn k6 []) (bv 1))))),
   (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (ap (cn k2 []) (ap (cn k6 []) (bv 1)))))]

/-- The annotated types of the recursors. -/
def tysR : List KExpr :=
  [(pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k3 [])) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k2 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k5 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k0 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k7 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k0 []) (bv 0)) (ap (ap (bv 6) (bv 1)) (bv 0))))))))),
   (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k3 [])) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k2 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k5 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k0 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k7 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k2 []) (bv 0)) (ap (ap (bv 5) (bv 1)) (bv 0)))))))))]

/-- The annotated right-hand sides of the recursors' rules. -/
def rhsss : List (List KExpr) :=
  [[(lm (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k3 [])) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k2 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k5 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k0 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k7 []) (bv 2)) (bv 1)))))) (bv 2)))))),
    (lm (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k3 [])) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k2 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k5 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k0 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k7 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (cn k1 []) (lm (pZ [0]) (ap (cn k2 []) (bv 0)) (ap (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (ap (ap (ap (ap (ap (cn k9 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0))))))))))],
   [(lm (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k0 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k2 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k3 [])) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k2 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k5 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k0 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k7 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (cn k1 []) (lm (pZ [0]) (ap (cn k0 []) (bv 0)) (ap (ap (ap (bv 2) (bv 1)) (bv 0)) (ap (ap (ap (ap (ap (ap (ap (cn k8 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0))))))))))]]

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

/-- No basis pin hits the block (evaluated). -/
theorem pin_ok : Ix.Kernel.basisPinHit blk = none := by decide +kernel

/-- The block's names are base keys (evaluated). -/
theorem base_ok : ∀ ci ∈ blk, isBaseKey ci.name = true := by decide +kernel

/-- **The model side at this family**: the declaration layer's invariant passes from the prefix to
the environment after the block, in every set theory, and every recursor the block stores has a
model companion. -/
theorem model_side :
    ∃ env₂ : Env .anon, DeclIndRenRunJ (famJ (aliasMap tbl)) ⟨aliases ++ pre⟩ blk env₂ ∧
      (∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V ⟨pre⟩ → FullDeclInv V env₂) ∧
      (∀ (k : KKey) (c : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon)),
        env₂.find? k = some (.recInfo c mI rP rules) →
        (⟨aliases ++ pre⟩ : Env .anon).find? k = none → Ix.Kernel.Model.HasModel env₂ k) := by
  obtain ⟨env₂, -, hd⟩ := famRecord_of_check record_ok
  exact ⟨env₂, hd,
    fullDeclInv_famStep (aliasGroup_of_check group_ok) pin_ok
      (fun ci hci => isBaseKey_iff_nonAuxKey.mp (base_ok ci hci)) roots_ok hd,
    fun _ _ _ _ _ hf hn => hasModel_declIndRenJ hd hf hn⟩

end IxVM.Refinement.Decl.FamilyAlias.Fixtures.IndexedPair
