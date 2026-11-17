import IxVMRefinement.Assembly.TypingRecLateElim

/-! # The pins of the late relation at the tied parent

`late_pins_of` gives the four pin conjuncts of the late relation from the record's counts and the
rules as read. This module supplies them at the tied parent: the counts (`rec_counts_of_arm`),
the rules' field counts (`rec_rule_fields_of_arm`), and the rules as the reader reads them with
the parent's member as the block member they name (`LoadedReads.rules_reading` at
`(ip.block, ip.idx)`, on the record's converted rule list). The reading is under any level
parameters `ps` (the relation's choice), and needs no `IndKeyAt`: `RuleReads` names the member by
its block address and index.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantVal)

/-- **The pins at the tied parent**: the record's rules as read (any level parameters `ps`),
naming the constructor projections of the parent's member, are the late relation's pinned rules
for the matched family, with the record's major index and rule prefix the family's. -/
theorem rec_pins_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) (hlim : lim = some n)
    (hnat : NativeRecArm calls bAddr t A n) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P) {fam : Ix.Kernel.Semantics.NativeFam .anon}
    (hm : MatchedAt t E env P ip fam)
    (ps : List Ix.Kernel.LevelParam) (cvR : ConstantVal .anon) (elim : Ix.Kernel.LevelParam)
    (large : Bool) :
    ∃ rules : List (Ix.Kernel.RecRule .anon),
      List.Forall₂ (RuleReads t (exprReader t (fun x => E₀.blobs.get? x) c
        (Ix.Kernel.Reader.recParam ps) (soloSelf t A)) ip.block ip.idx.toNat)
        rc.rules.toList.zipIdx rules ∧
      List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
        (exprReader t (fun x => E₀.blobs.get? x) c (Ix.Kernel.Reader.recParam ps)
          (soloSelf t A)).read ru.rhs = .ok rl₀.rhs) rc.rules.toList rules ∧
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat =
        (fam.recParts cvR elim large (rules.map (·.rhs))).majorIdx ∧
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat =
        (fam.recParts cvR elim large (rules.map (·.rhs))).rulePrefix ∧
      rules.length = fam.ctorsA.length ∧
      ∀ (j : Nat) (r : Ix.Kernel.RecRule .anon) (cA : ConstantVal .anon × Nat),
        rules[j]? = some r → fam.ctorsA[j]? = some cA → r.ctor = cA.1.name ∧ r.nfields = cA.2 := by
  obtain ⟨hat, hTP, cb, ms, ind, hcb, hms, hind, hnP, hnI, hlenC, hnames⟩ := hm
  obtain ⟨hp, hi, hmot, hrules, hmin⟩ :=
    rec_counts_of_arm ht hS hst hc hinfo hlim hnat hinert hcover hstep hcm hcmi htie hcb hms hind
  have hfields := rec_rule_fields_of_arm ht hS hst hc hinfo hlim hnat hinert hcover hstep hcm
    hcmi htie hcb hms hind hat.stored hnames
  obtain ⟨rcv, apv, parentV, tyPtr, rulesPtr, blkPtr, tyPtrP, unsP, blkPtrP, kTarget, result,
    bA, bR, bT, bP, blobs, tree, loadedHeap, kHeap, kAfter, canonHeap, final, kCalls,
    canonCalls, hrc, hbA, hbA', hbR, hbR', hbT, hbT', hbP, hbP', hblob, rty, hrulesTr, hrules_lt,
    hidx56, eK, evK, hsK, hkEq, eC, evCanon, hsCanon⟩ :=
    rec_canon_of_arm ht hS hst hc hinfo hlim hnat hinert hcover hstep hcm hcmi htie hcb hms hind
  obtain ⟨rules, hrr, hrd⟩ := LoadedReads.rules_reading (t := t)
    (blob := fun x => E₀.blobs.get? x) (param := Ix.Kernel.Reader.recParam ps)
    (self := soloSelf t A) ht (LoadedReads.soloSelf_ok t A) hblob ip.block ip.idx.toNat
    hrulesTr.toRaw
  have hlen : rc.rules.toList.length = fam.ctorsA.length := by
    rw [Array.length_toList, hrules, hlenC]
  obtain ⟨hl, hat'⟩ := ruleReads_pins hrr hlen hnames hfields
  exact ⟨rules, hrr, hrd, late_pins_of hat.stored.lenA hnP hnI hlenC hp hi hmot hmin hl hat'⟩

end IxVM.Refinement.Typing
