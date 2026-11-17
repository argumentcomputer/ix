import IxVMRefinement.Assembly.TypingRecLateStep
import IxVMRefinement.Decl.LateNatRecCheckT

/-! # The registry entry's data for the native recursor comparison at the arm

The native recursor comparison (`Decl.late_nat_rec_check_specT`) reads the matched family's
stored constructors as a list of entries `(C, nF, R₀, C₀, recIdx)` (`lateCtorsInfo`: the stored
constructor's key, field count and type, and the recursive field indices of its kinds), and
asks, of each entry, the well-formedness facts `Decl.NatCtorInfoWfT`. This module states:

* `FamCtorNoProj`: no constructor type of the family projects out of the family, a fact of the
  registry entry (the constructor stage of the native block's step) that the store does not
  carry;
* `RecArmBounds`: the count bounds the comparison's specifications are stated under, on the
  record's and the registry entry's data;
* `lateCtorsInfo` and its facts: the entries are the family's `nativeCtors4`, and each entry
  meets `NatCtorInfoWfT` at the family; the former's and the constructors' stored types are
  `GenScoped` at the environment.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantVal LevelParam)
open Ix.Kernel.Semantics (NativeFam NativeFamStored)

/-- **No stored constructor type of the family projects out of the family**
(`Decl.NatCtorInfoWfT.noProj_C`, read by `nat_rec_idx`'s specification through
`natT_ctor_spec`). The constructor stage of the native block's step gives it at admission
(`Decl.noProjAt_of_infer_full`, where the family has no projection yet); neither the store nor
the registry entry carries it, and the recursor's run does not check it. -/
def FamCtorNoProj (fam : NativeFam .anon) : Prop :=
  ∀ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA →
    Decl.noProjAt fam.p.cvT.name cA.1.type = true

/-- **The count bounds of the comparison's specifications**, on the record's and the registry
entry's data: the member's level count (`hk_lt`), parameter count (`hnP_lt`), index count
(`hnIdx_lt`), constructor count (`hnCtors_lt`), the recursor's binder count (`hnall_lt`), the
member index (`hidx`), and per constructor of the family (`nativeCtors4`): its parameter and
field count (`NatCtorInfoWfT.nf_lt`), its minor premise's binder count
(`NatCtorInfoWfT.minor_base_lt`) and, per recursive field, the induction hypothesis's binder
count (`NatCtorInfoWfT.tele_lt`). These are bounds the specifications of the circuit's
generators are stated under; the circuit checks none of them, and a bounded run gives counts
below `2^39` only. -/
def RecArmBounds (ip : Ixon.InductiveProj) (ind : Ixon.Inductive) (fam : NativeFam .anon) :
    Prop :=
  ind.lvls.toNat < 2147483648 ∧
  ind.params.toNat < 2147483648 ∧
  ind.indices.toNat < 2147483648 ∧
  ind.ctors.size < 2147483648 ∧
  ind.params.toNat + 1 + ind.ctors.size + ind.indices.toNat + 1 < 4294967296 ∧
  ip.idx.toNat < 4294967296 ∧
  ∀ c4 ∈ Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds,
    ind.params.toNat + c4.2.1 < 2147483648 ∧
    ind.params.toNat + 1 + ind.ctors.size + c4.2.1 + c4.2.2.2.length < 4294967296 ∧
    ∀ i ∈ c4.2.2.2,
      ind.params.toNat + 1 + ind.ctors.size + c4.2.1 + c4.2.2.2.length +
        (Ix.Kernel.structFieldTeleOf c4.2.2.1 ind.params.toNat c4.2.1 i).length < 4294967296

/-- **The comparison's constructor entries at a family**: per stored constructor, its key, its
field count, its stored type (twice: the raw slot is not read by the stored-type
specifications) and the recursive field indices of its kinds. -/
def lateCtorsInfo (fam : NativeFam .anon) :
    List (Core.KKey × Nat × Core.KExpr × Core.KExpr × List Nat) :=
  List.zipWith (fun cA ks => (cA.1.name, cA.2, cA.1.type, cA.1.type, Ix.Kernel.recIdxOf ks))
    fam.ctorsA fam.p.kinds

end IxVM.Refinement.Typing
