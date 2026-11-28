import IxVMRefinement.FamilyAlias.AdviceLayout
import IxVMRefinement.FamilyAlias.Fixtures.Terms

/-! # IndexedPair, at its compiled records' keys

The family step's conclusion (`inhabited`) for the family of `Fixtures/IndexedPair.lean`, with the keys
of the compiled records: `blk` is the reading, by IxCK's reader, of the block record and the
recursor family record Ix's compiler makes of the family; a member's key is the address of its
projection record, and an advice constant's key is the address of the advice record
`IxVM.Model` encodes for it. `pre` is the environment IxCK's fold stores for the pinned basis,
the reading of `List`'s compiled record and the readings of the compiled advice records;
`aliases` and `tbl` are built from it (`familyAliases`, `familyTable`): a member's alias has the
type IxCK stores for the member's model, a rule copy is the copy of the stored advice statement. -/

namespace IxVM.Refinement.Decl.FamilyAlias.Fixtures.IndexedPairCompiled

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule RecRuleFire ReducibilityHint)

set_option maxRecDepth 100000

universe u

def k0 : KKey := Key.id (adr [38, 178, 81, 145, 100, 108, 226, 18, 53, 242, 39, 222, 204, 198, 81, 56, 236, 147, 115, 20, 9, 232, 133, 59, 29, 61, 51, 121, 159, 141, 165, 103])
def k1 : KKey := Key.role (Ix.Kernel.Role.nat)
def k2 : KKey := Key.id (adr [121, 124, 149, 219, 211, 235, 156, 14, 105, 40, 252, 106, 180, 190, 3, 130, 198, 78, 255, 84, 91, 157, 70, 242, 217, 221, 19, 86, 252, 59, 246, 226])
def k3 : KKey := Key.id (adr [182, 136, 179, 217, 57, 110, 204, 221, 18, 246, 137, 216, 233, 87, 73, 94, 67, 236, 79, 173, 166, 46, 196, 241, 171, 179, 50, 244, 2, 135, 53, 240])
def k4 : KKey := Key.role (Ix.Kernel.Role.natZero)
def k5 : KKey := Key.id (adr [6, 44, 149, 97, 166, 100, 163, 42, 60, 224, 104, 69, 255, 112, 209, 61, 221, 191, 213, 158, 9, 233, 85, 137, 232, 191, 30, 48, 72, 102, 74, 224])
def k6 : KKey := Key.role (Ix.Kernel.Role.natSucc)
def k7 : KKey := Key.id (adr [187, 92, 7, 219, 163, 171, 139, 141, 227, 177, 100, 60, 115, 203, 189, 179, 88, 114, 154, 159, 28, 98, 46, 81, 85, 239, 255, 133, 22, 93, 21, 219])
def k8 : KKey := Key.id (adr [115, 91, 131, 41, 92, 135, 224, 156, 116, 163, 205, 177, 50, 165, 38, 119, 27, 113, 100, 209, 95, 224, 66, 32, 102, 106, 215, 130, 52, 127, 11, 70])
def k9 : KKey := Key.id (adr [218, 49, 217, 152, 139, 211, 215, 170, 182, 182, 216, 207, 211, 234, 5, 139, 209, 238, 253, 55, 179, 210, 103, 108, 145, 224, 221, 244, 55, 242, 217, 158])
def k10 : KKey := Key.id (adr [246, 180, 59, 171, 221, 84, 175, 134, 159, 253, 0, 212, 229, 215, 15, 242, 172, 143, 49, 55, 65, 50, 49, 77, 166, 22, 153, 141, 52, 28, 139, 83])
def k11 : KKey := Key.id (adr [216, 5, 209, 143, 57, 37, 116, 207, 67, 223, 103, 107, 181, 213, 68, 234, 148, 103, 59, 193, 70, 53, 49, 55, 156, 165, 250, 122, 57, 87, 213, 56])
def k12 : KKey := Key.id (adr [245, 2, 250, 33, 218, 210, 139, 155, 172, 85, 116, 153, 202, 44, 85, 201, 12, 74, 157, 87, 14, 107, 72, 136, 103, 120, 85, 209, 102, 228, 80, 22])
def k13 : KKey := Key.id (adr [199, 25, 135, 27, 58, 47, 217, 81, 198, 36, 175, 112, 163, 55, 130, 9, 209, 209, 142, 140, 217, 180, 78, 48, 185, 115, 200, 148, 166, 170, 162, 91])
def k14 : KKey := Key.id (adr [96, 166, 13, 201, 238, 147, 1, 181, 245, 52, 54, 234, 40, 48, 219, 61, 111, 180, 88, 143, 134, 109, 116, 96, 125, 72, 55, 97, 177, 74, 33, 68])
def k15 : KKey := Key.id (adr [37, 106, 32, 103, 244, 245, 133, 129, 25, 181, 6, 36, 123, 103, 199, 98, 249, 211, 118, 154, 196, 125, 69, 29, 214, 27, 73, 212, 165, 84, 84, 145])
def k16 : KKey := Key.role (Ix.Kernel.Role.eq)
def k17 : KKey := Key.id (adr [37, 55, 126, 208, 8, 52, 216, 171, 153, 22, 192, 47, 107, 199, 27, 81, 144, 24, 229, 92, 236, 92, 80, 89, 213, 96, 53, 86, 155, 104, 93, 44])
def k18 : KKey := Key.id (adr [220, 8, 175, 221, 30, 159, 45, 158, 233, 175, 62, 88, 224, 159, 41, 41, 196, 8, 38, 48, 84, 228, 39, 254, 218, 175, 64, 54, 219, 95, 205, 96])
def k19 : KKey := Key.role (Ix.Kernel.Role.eqRefl)
def k20 : KKey := Key.id (adr [238, 104, 118, 231, 216, 8, 2, 244, 68, 203, 54, 106, 224, 116, 147, 66, 5, 26, 71, 157, 140, 240, 14, 234, 245, 79, 119, 26, 148, 195, 172, 30])
def k21 : KKey := Key.id (adr [49, 96, 27, 159, 3, 124, 199, 97, 193, 162, 99, 81, 102, 110, 21, 0, 76, 106, 97, 11, 58, 203, 73, 22, 220, 183, 217, 249, 233, 164, 50, 30])
def k22 : KKey := Key.id (adr [11, 50, 255, 104, 78, 145, 247, 155, 44, 202, 76, 57, 161, 70, 218, 231, 145, 227, 70, 118, 235, 227, 126, 62, 210, 233, 176, 77, 25, 150, 139, 181])
def k23 : KKey := Key.role (Ix.Kernel.Role.int)
def k24 : KKey := Key.id (adr [41, 129, 136, 217, 201, 111, 161, 81, 91, 134, 180, 55, 201, 163, 228, 97, 0, 75, 143, 156, 82, 242, 169, 91, 223, 46, 161, 219, 73, 10, 18, 159])
def k25 : KKey := Key.id (adr [231, 70, 47, 224, 6, 129, 136, 109, 138, 30, 201, 172, 92, 153, 238, 94, 10, 220, 111, 228, 39, 134, 106, 224, 130, 100, 61, 5, 248, 187, 129, 139])
def k26 : KKey := Key.role (Ix.Kernel.Role.intNegSucc)
def k27 : KKey := Key.role (Ix.Kernel.Role.intOfNat)
def k28 : KKey := Key.id (adr [178, 42, 169, 19, 125, 225, 36, 147, 233, 234, 2, 108, 213, 187, 86, 3, 108, 81, 205, 27, 166, 22, 68, 201, 4, 60, 2, 250, 254, 52, 49, 95])
def k29 : KKey := Key.id (adr [204, 253, 235, 183, 230, 105, 125, 200, 88, 240, 227, 6, 55, 212, 36, 168, 88, 220, 144, 127, 237, 14, 149, 255, 215, 217, 11, 133, 78, 31, 144, 140])
def k30 : KKey := Key.id (adr [102, 242, 198, 129, 40, 204, 79, 61, 212, 105, 243, 142, 78, 66, 191, 213, 74, 138, 175, 64, 183, 16, 119, 85, 33, 173, 215, 53, 81, 21, 137, 58])
def k31 : KKey := Key.id (adr [57, 166, 198, 146, 122, 185, 95, 178, 93, 224, 16, 15, 136, 177, 222, 162, 248, 41, 31, 33, 105, 150, 134, 56, 247, 32, 227, 218, 82, 25, 124, 14])
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
  ConstantInfo.thmInfo (cv k10 [0] (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (pi (pZ []) (cn k1 []) (pi (pZ []) (ap (cn k12 []) (bv 0)) (ap (ap (ap (cn k16 [(lp 0)]) (ap (ap (bv 6) (ap (cn k6 []) (bv 1))) (ap (ap (cn k14 []) (bv 1)) (bv 0)))) (ap (ap (ap (ap (ap (ap (ap (cn k17 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (ap (cn k6 []) (bv 1))) (ap (ap (cn k14 []) (bv 1)) (bv 0)))) (ap (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (ap (ap (ap (ap (ap (cn k18 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0)))))))))))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (lm pN (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (pi pN (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (pi pN (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (lm pN (cn k1 []) (lm pN (ap (cn k12 []) (bv 0)) (ap (ap (cn k19 [(lp 0)]) (ap (ap (bv 6) (ap (cn k6 []) (bv 1))) (ap (ap (cn k14 []) (bv 1)) (bv 0)))) (ap (ap (ap (ap (ap (ap (ap (cn k17 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (ap (cn k6 []) (bv 1))) (ap (ap (cn k14 []) (bv 1)) (bv 0)))))))))))
def p1 : ConstantInfo .anon :=
  ConstantInfo.thmInfo (cv k20 [0] (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (ap (ap (ap (cn k16 [(lp 0)]) (ap (ap (bv 4) (cn k4 [])) (cn k13 []))) (ap (ap (ap (ap (ap (ap (ap (cn k17 [(lp 0)]) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0)) (cn k4 [])) (cn k13 []))) (bv 2)))))))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (lm pN (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (pi pN (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (pi pN (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (ap (ap (cn k19 [(lp 0)]) (ap (ap (bv 4) (cn k4 [])) (cn k13 []))) (ap (ap (ap (ap (ap (ap (ap (cn k17 [(lp 0)]) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0)) (cn k4 [])) (cn k13 []))))))))
def p2 : ConstantInfo .anon :=
  ConstantInfo.thmInfo (cv k21 [0] (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (pi (pZ []) (cn k1 []) (pi (pZ []) (ap (cn k11 []) (bv 0)) (ap (ap (ap (cn k16 [(lp 0)]) (ap (ap (bv 5) (ap (cn k6 []) (bv 1))) (ap (ap (cn k15 []) (bv 1)) (bv 0)))) (ap (ap (ap (ap (ap (ap (ap (cn k18 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (ap (cn k6 []) (bv 1))) (ap (ap (cn k15 []) (bv 1)) (bv 0)))) (ap (ap (ap (bv 2) (bv 1)) (bv 0)) (ap (ap (ap (ap (ap (ap (ap (cn k17 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0)))))))))))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (lm pN (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (pi pN (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (lm pN (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (pi pN (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (lm pN (cn k1 []) (lm pN (ap (cn k11 []) (bv 0)) (ap (ap (cn k19 [(lp 0)]) (ap (ap (bv 5) (ap (cn k6 []) (bv 1))) (ap (ap (cn k15 []) (bv 1)) (bv 0)))) (ap (ap (ap (ap (ap (ap (ap (cn k18 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (ap (cn k6 []) (bv 1))) (ap (ap (cn k15 []) (bv 1)) (bv 0)))))))))))
def p3 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k18 [0] (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (ap (ap (bv 5) (bv 1)) (bv 0)))))))))) (lm (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (cn k1 []) (lm (pZ [0]) (ap (cn k12 []) (bv 0)) (ap (ap (ap (ap (ap (ap (cn k22 [(lp 0)]) (lm pN (cn k23 []) (lm pN (ap (cn k24 []) (bv 0)) (ap (ap (ap (ap (ap (cn k25 [(ls (lp 0))]) (lm pN (cn k23 []) (pi pN (ap (cn k24 []) (bv 0)) (st (lp 0))))) (bv 8)) (bv 7)) (bv 1)) (bv 0))))) (bv 4)) (bv 3)) (bv 2)) (ap (cn k26 []) (bv 1))) (bv 0))))))))) (ReducibilityHint.regular 3)
def p4 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k17 [0] (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (ap (ap (bv 6) (bv 1)) (bv 0)))))))))) (lm (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (lm (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (lm (pZ [0]) (cn k1 []) (lm (pZ [0]) (ap (cn k11 []) (bv 0)) (ap (ap (ap (ap (ap (ap (cn k22 [(lp 0)]) (lm pN (cn k23 []) (lm pN (ap (cn k24 []) (bv 0)) (ap (ap (ap (ap (ap (cn k25 [(ls (lp 0))]) (lm pN (cn k23 []) (pi pN (ap (cn k24 []) (bv 0)) (st (lp 0))))) (bv 8)) (bv 7)) (bv 1)) (bv 0))))) (bv 4)) (bv 3)) (bv 2)) (ap (cn k27 []) (bv 1))) (bv 0))))))))) (ReducibilityHint.regular 3)
def p5 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k15 [] (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (ap (cn k12 []) (ap (cn k6 []) (bv 1)))))) (lm pN (cn k1 []) (lm pN (ap (cn k11 []) (bv 0)) (ap (ap (cn k28 []) (bv 1)) (bv 0)))) (ReducibilityHint.regular 2)
def p6 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k14 [] (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (ap (cn k11 []) (ap (cn k6 []) (bv 1)))))) (lm pN (cn k1 []) (lm pN (ap (cn k12 []) (bv 0)) (ap (ap (cn k29 []) (bv 1)) (bv 0)))) (ReducibilityHint.regular 2)
def p7 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k13 [] (ap (cn k11 []) (cn k4 []))) (cn k30 []) (ReducibilityHint.regular 1)
def p8 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k11 [] (pi pN (cn k1 []) (st (ls lz)))) (lm pN (cn k1 []) (ap (cn k24 []) (ap (cn k27 []) (bv 0)))) (ReducibilityHint.regular 1)
def p9 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k12 [] (pi pN (cn k1 []) (st (ls lz)))) (lm pN (cn k1 []) (ap (cn k24 []) (ap (cn k26 []) (bv 0)))) (ReducibilityHint.regular 1)
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
  ConstantInfo.indInfo (cv k23 [] (st (ls lz))) { eta := false, etaCtor := none, etaParams := 0, etaFields := 0, unitlike := false, unitParams := 0, ruleK := false, sortZ := (pZ []) }
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
  ConstantInfo.defnInfo (cv k41 [0] (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (pi (pZ []) (cn k1 []) (pi (pZ []) (ap (cn k11 []) (bv 0)) (ap (ap (ap (cn k16 [(lp 0)]) (ap (ap (bv 5) (ap (cn k6 []) (bv 1))) (ap (ap (cn k15 []) (bv 1)) (bv 0)))) (ap (ap (ap (ap (ap (ap (ap (cn k40 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (ap (cn k6 []) (bv 1))) (ap (ap (cn k42 []) (bv 1)) (bv 0)))) (ap (ap (ap (bv 2) (bv 1)) (bv 0)) (ap (ap (ap (ap (ap (ap (ap (cn k17 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0)))))))))))) (cn k21 [(lp 0)]) ReducibilityHint.abbrev
def a1 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k44 [0] (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (pi (pZ []) (cn k1 []) (pi (pZ []) (ap (cn k12 []) (bv 0)) (ap (ap (ap (cn k16 [(lp 0)]) (ap (ap (bv 6) (ap (cn k6 []) (bv 1))) (ap (ap (cn k14 []) (bv 1)) (bv 0)))) (ap (ap (ap (ap (ap (ap (ap (cn k43 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (ap (cn k6 []) (bv 1))) (ap (ap (cn k45 []) (bv 1)) (bv 0)))) (ap (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (ap (ap (ap (ap (ap (cn k18 [(lp 0)]) (bv 6)) (bv 5)) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0)))))))))))) (cn k10 [(lp 0)]) ReducibilityHint.abbrev
def a2 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k46 [0] (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k11 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (pi pN (cn k1 []) (pi pN (ap (cn k12 []) (bv 0)) (st (lp 0)))) (pi (pZ []) (ap (ap (bv 1) (cn k4 [])) (cn k13 [])) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k12 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k14 []) (bv 2)) (bv 1)))))) (pi (pZ []) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k11 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k15 []) (bv 2)) (bv 1)))))) (ap (ap (ap (cn k16 [(lp 0)]) (ap (ap (bv 4) (cn k4 [])) (cn k13 []))) (ap (ap (ap (ap (ap (ap (ap (cn k43 [(lp 0)]) (bv 4)) (bv 3)) (bv 2)) (bv 1)) (bv 0)) (cn k4 [])) (cn k47 []))) (bv 2)))))))) (cn k20 [(lp 0)]) ReducibilityHint.abbrev
def a3 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k40 [0] (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k48 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k49 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k47 [])) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k49 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k45 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k48 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k42 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k49 []) (bv 0)) (ap (ap (bv 5) (bv 1)) (bv 0)))))))))) (cn k18 [(lp 0)]) ReducibilityHint.abbrev
def a4 : ConstantInfo .anon :=
  ConstantInfo.defnInfo (cv k43 [0] (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k48 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (pi pN (cn k1 []) (pi pN (ap (cn k49 []) (bv 0)) (st (lp 0)))) (pi (pZ [0]) (ap (ap (bv 1) (cn k4 [])) (cn k47 [])) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k49 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 3) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k45 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k48 []) (bv 0)) (pi (pZ [0]) (ap (ap (bv 5) (bv 1)) (bv 0)) (ap (ap (bv 5) (ap (cn k6 []) (bv 2))) (ap (ap (cn k42 []) (bv 2)) (bv 1)))))) (pi (pZ [0]) (cn k1 []) (pi (pZ [0]) (ap (cn k48 []) (bv 0)) (ap (ap (bv 6) (bv 1)) (bv 0)))))))))) (cn k17 [(lp 0)]) ReducibilityHint.abbrev
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
  [(k41, k21), (k44, k10), (k46, k20), (k40, k18), (k43, k17), (k42, k15), (k45, k14), (k47, k13), (k49, k12), (k48, k11)]

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
/-- **The search for the renamed record over the family package succeeds, and each member is
stored after the block as a constant that stores it** (evaluated). -/
theorem record_ok :
    isOk (famStepCheck 200 tbl ⟨aliases ++ pre⟩ blk tysM tysR rhsss) = true := by
  decide +kernel

/-- Each alias is rooted at a member of the block (evaluated). -/
theorem roots_ok : ∀ a ∈ aliases, ∃ ci ∈ blk, a.name.base = ci.name := by decide +kernel

/-- **The family step's conclusion holds of this family**: an alias group over the prefix, each
alias rooted at a member of the block, IxCK's renamed record of the block over the family package
at the environment that stores the aliases, and each member stored as its reading. -/
theorem inhabited :
    ∃ (h : KKey → KKey) (as : List (ConstantInfo .anon)) (env₂ : Env .anon),
      AliasGroup ⟨pre⟩ h as ∧ (∀ a ∈ as, ∃ ci ∈ blk, a.name.base = ci.name) ∧
      DeclIndRenRunJ (famJ h) ⟨as ++ pre⟩ blk env₂ ∧
      (∀ ci ∈ blk, ∃ c, env₂.find? ci.name = some c ∧ IxVM.Consistency.StoredAs c ci) := by
  obtain ⟨env₂, -, hd, hs⟩ := famStep_of_check record_ok
  exact ⟨aliasMap tbl, aliases, env₂, aliasGroup_of_check group_ok, roots_ok, hd, hs⟩

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
  obtain ⟨env₂, -, hd, -⟩ := famStep_of_check record_ok
  exact ⟨env₂, hd,
    fullDeclInv_famStep (aliasGroup_of_check group_ok) pin_ok
      (fun ci hci => isBaseKey_iff_nonAuxKey.mp (base_ok ci hci)) roots_ok hd,
    fun _ _ _ _ _ hf hn => hasModel_declIndRenJ hd hf hn⟩

end IxVM.Refinement.Decl.FamilyAlias.Fixtures.IndexedPairCompiled
