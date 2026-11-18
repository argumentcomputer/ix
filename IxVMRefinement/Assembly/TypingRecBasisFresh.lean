import IxVMRefinement.Assembly.TypingRecBasisGuard
import IxVMRefinement.Assembly.TypingRecLatePins
import IxVMRefinement.Assembly.TypingRecLateRegistered
import IxVMRefinement.Assembly.TypingKeyFree
import IxVMRefinement.StatementRel.ClosedFacts

/-! # A fresh recursor record's major premise is headed by no basis family

`RecMajorFreshNotBasis` (the one fact the step of a standalone recursor record asks beside the
walk's): at an environment a step is asked at, a parent that heads the record's major premise,
is stored as an inductive type and has for record an inductive projection of a native block is
at no reserved basis name. This module proves it from the walk's check of the record.

The parent's key is a role's (`keyOf_cases`), bound at the parent, and a reserved name is one
of 19 roles, all of the prelude, which a valid table binds where the default table does
(`PreludePinned`). Two cases, decided over the 19 names (`reservedBasisNames_ok`):

* the role is one of the five basis families. The member check's scan read the same key
  (`recGuard_of_arm`, two annotations of one type have one major key), so the scanned address is
  the family's committed address, and the guard `basis_rec_at_pin` asserted that the record's
  address is the committed address of the family's recursor (`basis_rec_at_pin_spec`). The
  table binds the recursor's role there, so the key of the record's address is a reserved name,
  against the record's key being free (which holds because the witness's environment does not
  store the record's address: `keyFree_of_not_stored`);
* the role is one of the 14 others (a constructor's, a recursor's, a role of the quotient
  package). The default table binds it at a committed prelude record that is no inductive
  projection, and a store for the witness store holds that record there
  (`recordAt_of_committedPrelude`), against the parent's record being one.

* `recMajorFreshNotBasis_of_arm`: from the check of the record at the recursor arm;
* `recMajorFreshNotBasis_of_walk`: for a top-walked record, from what the walk hands every
  unit's step.
-/

universe u

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency

/-! ## The committed prelude records in a store -/

/-- **A store for a witness store holds each decoded committed prelude record at its
address**: it holds the committed row's bytes there and decodes what it holds. -/
theorem recordAt_of_committedPrelude {R E : Ixon.Env} (hE : RecordsFor R E)
    {e : _root_.Address × Ixon.Constant} (he : e ∈ RoleVal.committedPreludeList) :
    Ix.Cert.recordAt E e.1 = some e.2 := by
  obtain ⟨hrow, hdec⟩ := ClosedFacts.committedPrelude_rows e he
  obtain ⟨lc, hget, hbytes⟩ := hE.2.2.2 (e.1, Ixon.serConstant e.2) hrow
  have hget' : E.consts.get? e.1 = some lc := hget
  have hbytes' : lc.rawBytes = Ixon.serConstant e.2 := hbytes
  obtain ⟨c', hlc, hex⟩ := hE.1 e.1 lc hget'
  rw [hbytes', hdec] at hex
  have e' : e.2 = c' := Except.ok.inj hex
  rw [← e'] at hlc
  exact recordAt_of_get hget' hlc

/-! ## The reserved names, decided -/

/-- An inductive projection record. -/
private def isInductiveProjection : Ixon.ConstantInfo → Bool
  | .iPrj _ => true
  | _ => false

/-- A prelude role. -/
private def preludeRoleB (r : Ix.Kernel.Role) : Bool := decide (r ∈ preludeRoles)

/-- A role of one of the five basis families the guard pairs with a recursor. -/
private def basisFamilyB (r : Ix.Kernel.Role) : Bool := basisRecPairs.any fun p => p.1 == r

/-- The default table binds the role at a committed prelude record that is no inductive
projection. -/
private def rowNotInductiveB (r : Ix.Kernel.Role) : Bool :=
  match RoleVal.committedDefaultRoleTable.addressOf? r with
  | some a => RoleVal.committedPreludeList.any fun p =>
      p.1 == a && !isInductiveProjection p.2.info
  | none => false

/-- What is decided of a reserved basis name: it is the key of a prelude role that is a basis
family's, or that the default table binds at a committed record that is no inductive
projection. -/
private def reservedNameOk : Ix.Kernel.Key .anon → Bool
  | .role r => preludeRoleB r && (basisFamilyB r || rowNotInductiveB r)
  | _ => false

/-- What is decided of a pair of the guard: the recursor's role is a prelude role and its key a
reserved basis name. -/
private def recPairOk (p : Ix.Kernel.Role × Ix.Kernel.Role) : Bool :=
  preludeRoleB p.2 &&
    (Ix.Kernel.reservedBasisNames : List (Ix.Kernel.Key .anon)).contains (.role p.2)

set_option maxRecDepth 100000 in
private theorem reservedBasisNames_ok :
    (Ix.Kernel.reservedBasisNames : List (Ix.Kernel.Key .anon)).all reservedNameOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem basisRecPairs_ok : basisRecPairs.all recPairOk = true := by
  decide +kernel

private theorem contains_false_of_all (f : Ix.Kernel.Key .anon → Bool) :
    ∀ (L : List (Ix.Kernel.Key .anon)), L.all f = true →
      ∀ {k : Ix.Kernel.Key .anon}, f k = false → L.contains k = false
  | [], _, _, _ => rfl
  | x :: xs, hall, k, hk => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    simp only [List.contains, List.elem]
    cases hbeq : (k == x) with
    | true =>
      have e : k = x := beq_iff_eq.mp hbeq
      have h1 : f x = true := hall.1
      rw [← e, hk] at h1
      cases h1
    | false => exact contains_false_of_all f xs hall.2 hk

private theorem basisFamily_spec {r : Ix.Kernel.Role} (h : basisFamilyB r = true) :
    ∃ p ∈ basisRecPairs, p.1 = r := by
  have h' : (basisRecPairs.any fun p => p.1 == r) = true := h
  obtain ⟨p, hp, hpr⟩ := List.any_eq_true.mp h'
  exact ⟨p, hp, beq_iff_eq.mp hpr⟩

private theorem rowNotInductive_spec {r : Ix.Kernel.Role} (h : rowNotInductiveB r = true) :
    ∃ e ∈ RoleVal.committedPreludeList,
      RoleVal.committedDefaultRoleTable.addressOf? r = some e.1 ∧
        isInductiveProjection e.2.info = false := by
  cases hadr : RoleVal.committedDefaultRoleTable.addressOf? r with
  | none =>
    unfold rowNotInductiveB at h
    rw [hadr] at h
    exact Bool.noConfusion (show false = true from h)
  | some a =>
    unfold rowNotInductiveB at h
    rw [hadr] at h
    have h1 : (RoleVal.committedPreludeList.any fun p =>
        p.1 == a && !isInductiveProjection p.2.info) = true := h
    obtain ⟨e, he, hea⟩ := List.any_eq_true.mp h1
    have hea' : (e.1 == a && !isInductiveProjection e.2.info) = true := hea
    cases hb : (e.1 == a) with
    | false =>
      rw [hb] at hea'
      exact Bool.noConfusion (show false = true from hea')
    | true =>
      rw [hb] at hea'
      have ha : e.1 = a := beq_iff_eq.mp hb
      cases hi : isInductiveProjection e.2.info with
      | true =>
        rw [hi] at hea'
        exact Bool.noConfusion (show false = true from hea')
      | false =>
        refine ⟨e, he, ?_, ?_⟩
        · first
            | exact congrArg some ha.symm
            | exact hadr.trans (congrArg some ha.symm)
        · first
            | rfl
            | exact hi

private theorem reservedNameOk_role {r : Ix.Kernel.Role}
    (h : reservedNameOk (.role r) = true) :
    r ∈ preludeRoles ∧ ((∃ p ∈ basisRecPairs, p.1 = r) ∨
      ∃ e ∈ RoleVal.committedPreludeList,
        RoleVal.committedDefaultRoleTable.addressOf? r = some e.1 ∧
          isInductiveProjection e.2.info = false) := by
  have h' : (preludeRoleB r && (basisFamilyB r || rowNotInductiveB r)) = true := h
  cases hd : preludeRoleB r with
  | false =>
    rw [hd] at h'
    exact Bool.noConfusion (show false = true from h')
  | true =>
    rw [hd] at h'
    have hpre : r ∈ preludeRoles := of_decide_eq_true hd
    cases hfam : basisFamilyB r with
    | true => exact ⟨hpre, Or.inl (basisFamily_spec hfam)⟩
    | false =>
      rw [hfam] at h'
      have hrow : rowNotInductiveB r = true := h'
      exact ⟨hpre, Or.inr (rowNotInductive_spec hrow)⟩

private theorem recPair_spec {p : Ix.Kernel.Role × Ix.Kernel.Role} (hp : p ∈ basisRecPairs) :
    p.2 ∈ preludeRoles ∧
      (Ix.Kernel.reservedBasisNames : List (Ix.Kernel.Key .anon)).contains (.role p.2) =
        true := by
  have h : recPairOk p = true := List.all_eq_true.mp basisRecPairs_ok p hp
  have h' : (preludeRoleB p.2 &&
      (Ix.Kernel.reservedBasisNames : List (Ix.Kernel.Key .anon)).contains (.role p.2)) =
        true := h
  cases hd : preludeRoleB p.2 with
  | false =>
    rw [hd] at h'
    exact Bool.noConfusion (show false = true from h')
  | true =>
    rw [hd] at h'
    exact ⟨of_decide_eq_true hd, h'⟩

/-! ## The exclusion -/

/-- **A fresh recursor record's major premise is headed by no basis family, from the check of
the record** (module docstring). Inputs: the table's check, the run's store and the step's, the
record, its check at the recursor arm, the record's used references stored (`hinert`,
`hcover`), the prelude pinned, the step's store a store for the witness store, and the key of
the record's address free. -/
theorem recMajorFreshNotBasis_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E R : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat}
    {A : _root_.Address} {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (hnat : RecArmRun calls t A lim) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    (hpin : PreludePinned t) (hrows : RecordsFor R E)
    (hkey : Decl.KeyFree (keyOf t A)) :
    RecMajorFreshNotBasis.{u} t envT E₀ E lim A c rc := by
  intro env P ip hstep hfP hrecP hnatP htie
  refine eq_false_of_ne_true (fun hres => ?_)
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  obtain ⟨b₀, t₀, hdef, hadm, hpinEq⟩ := hpin
  have ht₀ : t₀ = RoleVal.committedDefaultRoleTable :=
    RoleVal.admitBinding_committedDefault hdef hadm
  subst ht₀
  -- the guard, on the scanned parent and the record's address
  obtain ⟨a, parent, addr, result, guardHeap, final, guardCalls, htieA, hPa, hAa, evGuard⟩ :=
    recGuard_of_arm ht hS hst hc hinfo hnat hinert hcover env hstep
  have hguard := basis_rec_at_pin_spec evGuard hPa hAa
  -- the scanned parent's key is the parent's
  have hkeyEq : keyOf t (Core.ixAddr a) = keyOf t P := by
    obtain ⟨tyP₁, E₁, hty₁, hann₁, hmaj₁⟩ := htieA
    obtain ⟨tyP₂, E₂, hty₂, hann₂, hmaj₂⟩ := htie
    have e : tyP₁ = tyP₂ := Except.ok.inj (hty₁.symm.trans hty₂)
    rw [e] at hann₁
    have hm := majorKey_annotates_eq (rc := rc) hann₁ hann₂
    rw [hmaj₁, hmaj₂] at hm
    exact Option.some.inj hm
  rcases keyOf_cases t P with ⟨hk, -⟩ | ⟨r, hr, hk⟩
  · -- an address key is no reserved name
    have hfalse : Ix.Kernel.reservedBasisNames.contains (keyOf t P) = false := by
      rw [hk]
      exact (keyFree_id P).1
    exact Bool.noConfusion (hfalse.symm.trans hres)
  · rw [hk] at hres hkeyEq
    have haP : t.addressOf? r = some P := Claim.addressOf_eq_some_of_mem_bound ht hr
    have hok : reservedNameOk (.role r) = true :=
      Classical.byContradiction fun hne =>
        Bool.noConfusion ((contains_false_of_all reservedNameOk _ reservedBasisNames_ok
          (eq_false_of_ne_true hne)).symm.trans hres)
    obtain ⟨hpre, hcase⟩ := reservedNameOk_role hok
    have hcP : RoleVal.committedDefaultRoleTable.addressOf? r = some P :=
      (hpinEq r hpre).symm.trans haP
    rcases hcase with ⟨p, hp, hpr⟩ | ⟨e, he, hea, hnot⟩
    · -- a basis family: the guard put the record at the family's committed recursor
      subst hpr
      have hca : RoleVal.committedDefaultRoleTable.addressOf? p.1 = some (Core.ixAddr a) :=
        (hpinEq p.1 hpre).symm.trans (Core.addressOf_of_keyOf htwf hkeyEq)
      have hcA := hguard p hp hca
      obtain ⟨hpre₂, hresv⟩ := recPair_spec hp
      have htA : t.addressOf? p.2 = some A := (hpinEq p.2 hpre₂).trans hcA
      have hkA : keyOf t A = .role p.2 := Core.keyOf_of_addressOf htwf htA
      have hfree : Ix.Kernel.reservedBasisNames.contains
          (Ix.Kernel.Key.role p.2 : Ix.Kernel.Key .anon) = false := by
        rw [← hkA]
        exact hkey.1
      exact Bool.noConfusion (hfree.symm.trans hresv)
    · -- another reserved role: its committed record is no inductive projection
      have hPe : P = e.1 := Option.some.inj (hcP.symm.trans hea)
      obtain ⟨cm, hcm, hcmi⟩ := hrecP
      have hrow := recordAt_of_committedPrelude hrows he
      rw [← hPe, hcm] at hrow
      have hcc : cm = e.2 := Option.some.inj hrow
      have h1 : isInductiveProjection cm.info = true :=
        (congrArg isInductiveProjection hcmi).trans rfl
      rw [hcc, hnot] at h1
      exact Bool.noConfusion h1

/-- **A fresh recursor record's major premise is headed by no basis family**, for a top-walked
standalone recursor record, from what the walk hands every unit's step: the table's check, the
run's store, the step's store and context, the inert clause, the cover clause, and that the
witness's environment does not store the record's address. No premise beside the walk's. -/
theorem recMajorFreshNotBasis_of_walk {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address} {E₀ E R : Ixon.Env}
    {lim : Option Nat} {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hW : Claim.TopWalkCore calls bAddr t seeds E₀ lim Top rank)
    {envT : Ix.Kernel.Env .anon} (hctx : StepCtx.{u} calls t R envT E₀ E)
    {A : _root_.Address} {c : Ixon.Constant} {rc : Ixon.Recursor}
    (hT : Top A) (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    (hns : ¬ StoredAt t envT A) :
    RecMajorFreshNotBasis.{u} t envT E₀ E lim A c rc :=
  recMajorFreshNotBasis_of_arm ht hS hst hc hinfo (recArmRun_of_walk hW hT hc hinfo) hinert
    hcover hctx.shape.prelude hctx.recordsFor (keyFree_of_not_stored hctx.shape ht hns)

end IxVM.Refinement.Typing
