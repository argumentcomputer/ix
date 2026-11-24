import IxVMRefinement.Assembly.TypingRecLateNativeFront
import IxVMRefinement.Assembly.TypingRecLateNativeAsm
import IxVMRefinement.Assembly.TypingRecLateNativeScope

/-! # The native recursor stage of a late recursor, at the arm

At the arm of a late recursor record (a standalone recursor whose canonical comparison runs
`nat_rec_check` against its tied parent, matched to a registered family `fam`), the record is
read under the level parameters `ps := recLps large (range k)` (`k` the member's level count,
`large` whether the record has one more), its stored constant is the canonical annotation of
that reading (`LoadedReads.canonAnn`, `canonRules`: what every load of the record represents),
and IxCK's recursor stage holds at the step's environment: `NativeRecJ` at
`fam.recParts ⟨keyOf t A, ps, ty⟩ elim large (rules.map rhs)`, with the declared arm of
`RecStoredJ` storing the canonical recursor.

The proof composes:
* `rec_native_front` (the circuit side: the reading, the canonical annotations, the front
  check of the declared recursor at the prefix, and the native recursor comparison
  `Decl.late_nat_rec_check_spec_traced` instantiated at the arm);
* `nativeRecJ_of_parts` (the kernel side: `NativeRecRunJ` and the declared arm of
  `RecStoredJ` from the comparison's outputs);
* the registry entry's stored types (`late_former_genScoped`, `late_ctors_genScoped`) and the
  level parameters of the canonical rules (`wrapRelSem_annot_allLevelParamsDefined`).

Two hypotheses are not consequences of the arm alone, and are named: `FamCtorNoProj fam` (a
fact of the registry entry, which the fold's clause carries with it) and the scoping of the
rules as read (which the run gives only at the raw level: `wrap_rel` compares
the stored rule with the closed generated one cell by cell, a `let` only against a `let`).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantVal)
open Ix.Kernel.Semantics (NativeFam)
open Ix.Kernel.Model (rulesJ)

/-- **The recursor's stage and the stored recursor at the arm** (module docstring). -/
theorem rec_nativeRecJ_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) (hlogic : InLogic c)
    (hnat : RecArmRun calls t A lim)
    (hkey : Decl.KeyFree (keyOf t A)) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    (hlv : LvClauses env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind))
    {fam : NativeFam .anon} (hm : FamReadAt FormerOpenTraceAt t E env P ip fam)
    (hhead : Decl.CtorRetHeadAt cb ind)
    (hnoProj : FamCtorNoProj fam)
    (hrscoped : ∀ rules : List (Ix.Kernel.RecRule .anon),
      List.Forall₂ (fun ru rl₀ => (exprReader t (fun x => E₀.blobs.get? x) c
          (Ix.Kernel.Reader.recParam (Ix.Kernel.Reader.recLps
            (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)))
          (soloSelf t A)).read ru.rhs = .ok rl₀.rhs) rc.rules.toList rules →
      ∀ rl₀ ∈ rules, rl₀.rhs.looseBVarsBounded 0 = true ∧
        rl₀.rhs.allLevelParamsDefined (Ix.Kernel.Reader.recLps
          (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)) = true) :
    ∃ (ty : Ix.Kernel.Expr .anon) (rules : List (Ix.Kernel.RecRule .anon))
      (tyC : Ix.Kernel.Expr .anon) (rlsC : List (Ix.Kernel.RecRule .anon))
      (recTy : Ix.Kernel.Expr .anon),
      (exprReader t (fun x => E₀.blobs.get? x) c
        (Ix.Kernel.Reader.recParam (Ix.Kernel.Reader.recLps
          (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)))
        (soloSelf t A)).read rc.typ = .ok ty ∧
      ty.looseBVarsBounded 0 = true ∧
      ty.allLevelParamsDefined (Ix.Kernel.Reader.recLps
        (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)) = true ∧
      List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
        (exprReader t (fun x => E₀.blobs.get? x) c
          (Ix.Kernel.Reader.recParam (Ix.Kernel.Reader.recLps
            (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)))
          (soloSelf t A)).read ru.rhs = .ok rl₀.rhs ∧
        rl₀.rhs.looseBVarsBounded 0 = true ∧
        rl₀.rhs.allLevelParamsDefined (Ix.Kernel.Reader.recLps
          (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)) = true)
        rc.rules.toList rules ∧
      List.Forall₂ (RuleReads t (exprReader t (fun x => E₀.blobs.get? x) c
          (Ix.Kernel.Reader.recParam (Ix.Kernel.Reader.recLps
            (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)))
          (soloSelf t A)) ip.block ip.idx.toNat)
        rc.rules.toList.zipIdx rules ∧
      LoadedReads.canonAnn c (Ix.Kernel.Reader.recLps
        (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)) 0 rc.typ ty =
        some tyC ∧
      LoadedReads.canonRules c (Ix.Kernel.Reader.recLps
        (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)) rc.k
        rc.params.toNat (0 + 1) rc.rules.toList rules = some rlsC ∧
      Ix.Kernel.Semantics.NativeRecJ Ix.Kernel.Model.rulesJ env
        (fam.recParts ⟨keyOf t A, Ix.Kernel.Reader.recLps
            (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat), ty⟩
          (if decide (rc.lvls.toNat = ind.lvls.toNat + 1) then ind.lvls.toNat else 0)
          (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (rules.map (·.rhs)))
        fam.cvTa fam.ctorsA
        ⟨keyOf t A, Ix.Kernel.Reader.recLps
          (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat), tyC⟩
        (rlsC.map (·.rhs)) ∧
      Ix.Kernel.structRecTyR fam.p.cvT.name fam.p.cvT.levelParams
        (if decide (rc.lvls.toNat = ind.lvls.toNat + 1) then ind.lvls.toNat else 0)
        (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) fam.p.nP fam.p.nIdx fam.cvTa.type
        (Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds) = some recTy ∧
      Ix.Kernel.Semantics.WrapRel env.find? recTy tyC ∧
      Annotates tyC ty ∧ List.Forall₂ RuleStored rlsC rules ∧
      (Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
        (List.range ind.lvls.toNat)).length = rc.lvls.toNat := by
  obtain ⟨ty, rules, tyC, rlsC, recTy, hty, hlbb, hdef, hrd, hrr, hcT, hcR, hannT, hstR, hM, hcv,
    hrec, hwrap, hlenC, hrules, hmaj⟩ :=
    rec_native_front ht hS hcov hst hc hinfo hlogic hnat hkey hinert hcover hstep hlv hcm
      hcmi htie hcb hms hind hm hhead hnoProj hrscoped
  have hat : FamRead FormerOpenTraceAt t E env fam := hm.1
  have hL1 : fam.p.cvT.levelParams = List.range ind.lvls.toNat :=
    (hat.logic_lvls ht hm.2.1 hcm hcmi hcb hms hind).2
  have henv : Ix.Kernel.EnvWF env := hstep.inv.store.store.wf
  have hsub : ∀ x ∈ fam.p.cvT.levelParams, x ∈ Ix.Kernel.Reader.recLps
      (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat) := by
    intro x hx
    rw [hL1] at hx
    cases decide (rc.lvls.toNat = ind.lvls.toNat + 1) <;>
      simp [Ix.Kernel.Reader.recLps, hx]
  have hctors := late_ctors_genScoped hat henv hlv hsub
  have hRfresh : env.find? (keyOf t A) = none :=
    hstep.fresh A (Or.inl ⟨rfl, Or.inr (Or.inl ⟨rc, hinfo⟩)⟩)
  obtain ⟨bs, hsort⟩ := hat.sort
  have hlenR : rules.length = rlsC.length := hstR.length_eq.symm
  have hrdE : ∀ (j : Nat) (hj : j < rules.length),
      (rules[j]'hj).rhs.looseBVarsBounded 0 = true ∧
      (rules[j]'hj).rhs.allLevelParamsDefined (Ix.Kernel.Reader.recLps
        (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)) = true ∧
      (rules[j]'hj).rhs.hasFvar = false := by
    intro j hj
    have hjr : j < rc.rules.toList.length := by rw [hrd.length_eq]; exact hj
    obtain ⟨-, hread, hl, hd⟩ := (List.forall₂_iff_get.mp hrd).2 j hjr hj
    exact ⟨hl, hd, Assembly.memberReader_read_noFvar hread⟩
  have hNR := nativeRecJ_of_parts (hat.stored.former)
    (fun c4 hc4 => ⟨(hctors c4 hc4).1, (hctors c4 hc4).2.1⟩) hL1
    (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
    (late_former_genScoped hat hsub) ⟨bs, _, hsort⟩
    (fun c4 hc4 => (hctors c4 hc4).2.2) hRfresh hcv hrec hwrap hannT hstR hlenC hrules
    (fun rl hrl => by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hrl
      exact ⟨(hrdE j hj).2.2, (hrdE j hj).1⟩)
    (fun j hlt rhsG hrhs hG => by
      obtain ⟨rhsG', hrhs', hw⟩ := hrules j hlt
      rw [hrhs] at hrhs'
      cases hrhs'
      have hjR : j < rules.length := by rw [hlenR]; exact hlt
      have hstj := (List.forall₂_iff_get.mp hstR).2 j hlt hjR
      exact wrapRelSem_annot_allLevelParamsDefined hw hG hstj.2.2 (hrdE j hjR).2.1)
    hmaj
  exact ⟨ty, rules, tyC, rlsC, recTy, hty, hlbb, hdef, hrd, hrr, hcT, hcR, hNR, hrec,
    Decl.WrapRelSem.toWrapRel hwrap, hannT, hstR, hM⟩

end IxVM.Refinement.Typing
