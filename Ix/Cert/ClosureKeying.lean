import Ix.Cert.ReadingKeys

/-! # The closure's reading context keys every published name as its renaming

`ReadingKeys.readingAt_renamed` keys quotient Source's constants in the context of an accepted
run. This module keys them in the context the reader's streams are stated over
(`closureContext`), from the compile alone: a published name whose record resolves there is
keyed by its quotient key renamed to the artifact's addresses (`closure_keyAt`).

* **The store is authentic** (`closure_authentic`): a stream record is the canonical decoding of
  its stored bytes (`Stream.StoredCanonical`), which sit at the admission hash of themselves
  (`compileAuthentic`); a fallback record is the pinned configuration's
  (`FallbackStore.fallback_authentic`). So resolution is injective on it
  (`ReadingKeys.resolve_inj`), and the role bindings key a reference by the role bound at its
  own address.
* **A quotient key sits at the name's published address** (`ReadingKeys.keyAddress_quotientKey`):
  a role key at its role's bound address, an input key at an address no role is bound to (the
  representative under the table rule, `ReadingKeys.qrepAt_unbound`), which reads as itself. -/

namespace Ix.Cert.ClosureKeying

open Ix.Kernel Ix.Kernel.Reader

/-- A record of the closure order the artifact stores is in the closure context's store. -/
theorem closure_store {ixe : Ixon.Env} {t : RoleTable} {preA : Prelude .anon} {order : List Address}
    (nodup : order.Nodup) {a : Address} {c : Ixon.Constant} (ha : a ∈ order) (hc : recordAt ixe a = some c) :
    (closureContext ixe t preA order).store a = some c := by
  have unique : ((Stream.decodedOf ixe order).map Prod.fst).Nodup := (Stream.decodedOf_keys ixe order).nodup nodup
  have present : (a, c) ∈ Stream.decodedOf ixe order :=
    List.mem_filterMap.mpr ⟨a, ha, by simp [hc]⟩
  exact ReaderClosureKeys.context_input t (Stream.decodedOf ixe order).toArray (preA.records ++ preA.evidence)
    (blobsOf ixe order) preA.blobs (hintsOf ixe) (Admission.projectionAddress Address.admissionHash)
    (by simpa only [List.toList_toArray] using unique) (by simpa only [List.mem_toArray] using present)

/-- **The closure context's store is authentic**: every record it holds sits at the admission
hash of its canonical bytes. -/
theorem closure_authentic {env : Ix.Environment} {ixe : Ixon.Env} (compiled : compile env = .ok ixe)
    (hashed : RoleClosure.FallbackHashed) {t : RoleTable} {preA : Prelude .anon} (prelude : preludeFor t = .ok preA)
    {order : List Address} (canonical : Stream.StoredCanonical ixe order) {a : Address} {c : Ixon.Constant}
    (h : (closureContext ixe t preA order).store a = some c) :
    a = Address.admissionHash (Ixon.serConstant c) := by
  rcases ReadingKeys.context_store h with stream | fallback
  · obtain ⟨a', ha', he⟩ := List.mem_filterMap.mp stream
    cases hr : recordAt ixe a' with
    | none => rw [hr] at he; cases he
    | some c' =>
      rw [hr] at he
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨lc, hlc, hget⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨c'', hget', -, enc⟩ := canonical _ ha' lc hlc
      rw [hget] at hget'
      cases hget'
      rw [enc, Address.admissionHash_eq]
      exact (compileAuthentic env ixe compiled).1 _ lc hlc
  · exact (FallbackStore.fallback_authentic hashed prelude fallback).1

/-- An input key is in quotient Source's input scope at a published name. -/
theorem ingressKey_good {ixe : Ixon.Env} (agree : PublishedAgree ixe) {m : Ix.Name} {named : Ixon.Named}
    (hm : (m, named) ∈ ixe.named.toList) :
    (Ix.LeanIngress.ingressKey m).Good (KeyScope.ofId (Ix.LeanIngress.QIn ixe)) := by
  unfold Ix.LeanIngress.ingressKey
  cases hr : Ix.LeanIngress.roleOf (Ix.LeanIngress.ingressName m) with
  | some r => rw [Ix.LeanIngress.roleOf_eq_some hr]; trivial
  | none =>
    rw [Ix.LeanIngress.roleOf_eq_none hr]
    exact ⟨hr, by rw [agree m named hm]; rfl⟩

set_option maxRecDepth 4096 in
/-- **The closure context keys a published name by its quotient key renamed**, at the name's
published address, wherever that address resolves. -/
theorem closure_keyAt {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : RoleTable} {envQ : Env .source}
    (P : Premises env roots sub ixe failures t envQ) {preA : Prelude .anon} (prelude : preludeFor t = .ok preA)
    {order : List Address} (canonical : Stream.StoredCanonical ixe order) (b : Ix.RoleEvidence.Bundle)
    {m : Ix.Name} {named : Ixon.Named} (hm : (m, named) ∈ ixe.named.toList) {q : ConstRef Address}
    (hq : resolve (closureContext ixe t preA order).store named.addr = some q) :
    (closureContext ixe t preA order).keyAt named.addr =
      .ok ((quotientKey ixe t m).map (Ix.LeanIngress.evAddr ixe b)) := by
  have checked := defaultTable_check P.table
  have tableBound := tableBound_of checked P.bound
  have compiled : compile env = .ok ixe := by unfold compile; rw [P.compiled]; rfl
  have auth := fun a c h => closure_authentic compiled P.evidence.2.1 prelude canonical (a := a) (c := c) h
  have inj : ∀ a', resolve (closureContext ixe t preA order).store a' = some q → a' = named.addr :=
    fun a' h' => ReadingKeys.resolve_inj auth h' hq
  have roles : (closureContext ixe t preA order).roles = bindingsOf (closureContext ixe t preA order).store t := rfl
  have hk := ReadingKeys.keyAddress_quotientKey checked P.bound P.agree hm
  have good : (quotientKey ixe t m).Good (KeyScope.ofId (Ix.LeanIngress.QRepAt ixe (Ix.LeanIngress.roleAtMap t))) :=
    Ix.LeanIngress.Key.subst_goodAt tableBound (ingressKey_good P.agree hm)
  rw [Ctx.keyAt_eq_ok]
  unfold keyOfAddress
  rw [hq]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases hqk : quotientKey ixe t m with
  | aux k d => rw [hqk] at hk; simp [keyAddress] at hk
  | role r =>
    rw [hqk] at hk
    simp only [keyAddress] at hk
    rw [roles, ReadingKeys.bindings_bound checked (ReadingKeys.bound_of_addressOf hk) hq inj]
    rfl
  | id n =>
    rw [hqk] at hk good
    simp only [keyAddress] at hk
    simp only [Key.good_id, KeyScope.ofId_id] at good
    have unboundRole := ReadingKeys.qrepAt_unbound tableBound good hk
    have unbound : ∀ r, (r, named.addr) ∉ t.bound.toList := by
      intro r hmem
      have := (Ix.LeanIngress.roleAtMap_spec checked).mpr (ReadingKeys.addressOf_of_bound checked hmem)
      rw [unboundRole] at this
      cases this
    rw [roles, ReadingKeys.bindings_unbound unbound inj]
    simp only [Mode.addressId?, Option.map_some, Key.map, ReadingKeys.evAddr_published hk]

/--
info: 'Ix.Cert.ClosureKeying.closure_keyAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closure_keyAt

end Ix.Cert.ClosureKeying
