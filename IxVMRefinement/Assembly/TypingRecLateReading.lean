import IxVMRefinement.Assembly.TypingRecLateFamilyKey

/-! # The reading of a late recursor record

A standalone recursor record `c` at `A` whose family is a registered native family, checked on
the native arm, with its parent `P` tied to it, declares the recursor that the late step
installs: `Reads t E₀ A` of the recursor constant built from the reading `ty` of its type under
its level parameters, its major premise's position, its rule prefix's length and its rules as
read (`RuleReads`).

`RecReads` asks, besides `ty` and the rules (which the caller has), for the reading `tyP` with
positional level parameters, the inductive heading its family (`familyKey`) and the inductive
heading its major premise (`majorKey`), each an `IndKeyAt` key of the run's store; the level
parameters are the family's member's behind one more for a large eliminator; one rule per
constructor.

* the major side: `rec_major_key_reading` (the major key is the parent's key) and
  `rec_major_indKeyAt` (the parent's key is member `ip.idx` of block `ip.block` in the run's
  store, the block in Lean's logic by the registered family's record);
* the family side: `rec_motive_letFree_reading` (the first motive is literal and let-free) and
  `familyKey_of_wrapRel` (the declared/generated relation puts the family, the parent, at the end
  of the motive);
* the counts: `rec_counts_of_arm` (one rule per constructor, one motive, the parent's
  parameter count).
-/

universe u

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam NativeFamStored)

/-- **The reading of a late recursor record.** At a standalone recursor record `c` at `A`,
checked on the native arm, with its parent `P` (record `iPrj ip`, member `ind` of the block
`ip.block`) tied to it and the registered family `fam` read off the parent: given the reading
`ty` of the record's type and its rules under the recursor's level parameters, an annotation
`tyC` of `ty`, and the declared/generated relation of the generated recursor type with `tyC`,
the record at `A` declares the recursor of those parts (`Reads`). -/
theorem rec_reads_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) (hlogic : InLogic c)
    (hlim : lim = some n) (hnat : NativeRecArm calls bAddr t A n) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind))
    {fam : Ix.Kernel.Semantics.NativeFam .anon} (hm : MatchedAt t E env P ip fam)
    {ty tyC recTy : Ix.Kernel.Expr .anon} {rules : List (Ix.Kernel.RecRule .anon)}
    (hty : (exprReader t (fun x => E₀.blobs.get? x) c
        (Ix.Kernel.Reader.recParam (Ix.Kernel.Reader.recLps
          (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)))
        (soloSelf t A)).read rc.typ = .ok ty)
    (hrules : List.Forall₂ (RuleReads t (exprReader t (fun x => E₀.blobs.get? x) c
          (Ix.Kernel.Reader.recParam (Ix.Kernel.Reader.recLps
            (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)))
          (soloSelf t A)) ip.block ip.idx.toNat)
        rc.rules.toList.zipIdx rules)
    (hann : Annotates tyC ty)
    (hgen : Ix.Kernel.structRecTyR fam.p.cvT.name fam.p.cvT.levelParams
        (if decide (rc.lvls.toNat = ind.lvls.toNat + 1) then ind.lvls.toNat else 0)
        (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) fam.p.nP fam.p.nIdx fam.cvTa.type
        (Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds) = some recTy)
    (hwrap : Ix.Kernel.Semantics.WrapRel env.find? recTy tyC) :
    Reads t E₀ A (.recInfo ⟨keyOf t A, Ix.Kernel.Reader.recLps
        (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat), ty⟩
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules) := by
  -- the counts
  obtain ⟨hpar, -, hmot, hrsz, -⟩ := rec_counts_of_arm ht hS hst hc hinfo hlim hnat hinert
    hcover hstep hcm hcmi htie hcb hms hind
  -- the parent's block in Lean's logic, and the parent's key an inductive's key of the run's store
  obtain ⟨hlogicB, -⟩ := hm.1.logic_lvls ht hm.2.1 hcm hcmi hcb hms hind
  obtain ⟨-, -, hIK⟩ := rec_major_indKeyAt ht hS hcov hst hc hinfo hlim hnat hinert hcover
    hstep hcm hcmi htie hcb hms hind hlogicB
  -- the major key of the reading
  obtain ⟨tyP, htyP, hmajP⟩ := rec_major_key_reading ht hS hst hc hinfo hnat htie
  -- the family key of the reading
  obtain ⟨tyP', htyP', bs, D, B, mD, hstripP', hletD⟩ :=
    rec_motive_letFree_reading ht hS hst hc hinfo hnat hmot
  have htyEq : tyP' = tyP := Except.ok.inj (htyP'.symm.trans htyP)
  have hstripP : tyP.stripPis rc.params.toNat = some (bs, .forallE D B mD) := by
    rw [← htyEq]
    exact hstripP'
  obtain ⟨hat, hname, cb', ms', ind', hcb', hms', hind', hnP, -⟩ := hm
  have hcbEq : cb' = cb := Option.some.inj (hcb'.symm.trans hcb)
  rw [hcbEq, hms] at hms'
  have hmsEq : ms' = ms := (Ixon.ConstantInfo.muts.inj hms').symm
  rw [hmsEq, hind] at hind'
  have hindEq : ind' = ind := (Ixon.MutConst.indc.inj (Option.some.inj hind')).symm
  rw [hindEq] at hnP
  have hnP' : fam.p.nP = rc.params.toNat := hnP.trans hpar.symm
  rw [hnP'] at hgen
  have hshape : KeyShape tyP ty := exprReader_keyShape htyP hty
  have hfam : familyKey rc tyP = some fam.p.cvT.name :=
    familyKey_of_wrapRel hshape hstripP hletD hann hgen hwrap ⟨_, _, hat.stored.former⟩
  rw [hname] at hfam
  -- assemble the reading
  unfold Reads ReadsIn
  refine ⟨c, hc, ?_⟩
  rw [hinfo]
  simp only [ReadsRecord]
  refine ⟨hlogic, ?_⟩
  unfold RecReads
  exact ⟨tyP, ty, keyOf t P, keyOf t P, ip.block, ip.block, ip.idx.toNat, ip.idx.toNat, ind, ind,
    Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
      (List.range ind.lvls.toNat), rules,
    htyP, hfam, hIK, hmajP, hIK, rfl, hty, hrsz, hrules, rfl⟩

end IxVM.Refinement.Typing
