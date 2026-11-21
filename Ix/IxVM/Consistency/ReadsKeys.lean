import Ix.IxVM.Consistency.StatementRel
import Ix.Cert.ReadingKeys

/-! # The reading context keys an address by the role table

`Reads` converts a record's expressions with the kernel reader's own function, in the
context `readCtx`. This module shows what that context does with a reference: under a table
the admission accepts, the reader's key of the address `a` there is `keyOf t a`, the role the
table binds to `a`, otherwise the address key. So every `ref` and `prj` node of a record
reads as the key of the constant at the address the node names, and `Reads` uses the kernel
reader for conversion (sharing, universe tables, literal blobs) and for nothing else.
-/

namespace IxVM.Consistency

open Ix.Kernel Ix.Kernel.Reader

/-- In the reading context's store every address resolves to itself. -/
theorem readCtx_resolve (t : RoleTable) (blob : _root_.Address → Option ByteArray)
    (a : _root_.Address) :
    resolve (readCtx t blob).store a = some (ConstRef.member a 0) := rfl

/-- **The reading context's key of an address is `keyOf`**: the role the table binds to it,
otherwise the address itself. -/
theorem readCtx_keyAt {t : RoleTable} (checked : t.check = .ok ())
    (blob : _root_.Address → Option ByteArray) (a : _root_.Address) :
    (readCtx t blob).keyAt a = .ok (keyOf t a) := by
  have hres : resolve (readCtx t blob).store a = some (ConstRef.member a 0) := rfl
  have hinj : ∀ a', resolve (readCtx t blob).store a' = some (ConstRef.member a 0) → a' = a := by
    intro a' h
    have h2 : (some (ConstRef.member a' 0) : Option (ConstRef _root_.Address)) =
        some (ConstRef.member a 0) := h
    injection h2 with h3
    injection h3 with h4
  rw [Ctx.keyAt_eq_ok]
  rcases keyOf_cases t a with ⟨hk, hunb⟩ | ⟨r, hr, hk⟩
  · have hroles : (readCtx t blob).roles.names[ConstRef.member a 0]? = none :=
      Ix.Cert.ReadingKeys.bindings_unbound hunb hinj
    simp [keyOfAddress, hres, hroles, hk, Mode.addressId?]
  · have hroles : (readCtx t blob).roles.names[ConstRef.member a 0]? = some (Key.role r) :=
      Ix.Cert.ReadingKeys.bindings_bound checked hr hres hinj
    simp [keyOfAddress, hres, hroles, hk]

/-- The reading context's literal blobs are the given ones. -/
theorem readCtx_blob (t : RoleTable) (blob : _root_.Address → Option ByteArray) :
    (readCtx t blob).blob = blob := rfl

/-- An admitted table binds no role twice, so `Reads` is a function under it
(`ReadsIn.functional`). -/
theorem roles_nodup_of_admitBinding {hash : ByteArray → _root_.Address}
    {b : Admission.Binding} {t : RoleTable} (h : Admission.admitBinding hash b = .ok t) :
    (t.bound.toList.map (·.1)).Nodup :=
  (RoleTable.check_nodup ((Admission.admitBinding_ok_iff hash b t).mp h).wellFormed).1

/-! ## Building a reading

`ReadsIn` at each kind of constant address, from its parts. A member index or constructor
index below `2^64` is its own projection record's index. -/

private theorem toUInt64_toNat {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

/-- A standalone definition record's reading. -/
theorem ReadsIn.of_defn {t : RoleTable} {store : Store}
    {blob : _root_.Address → Option ByteArray} {a : _root_.Address} {c : Ixon.Constant}
    {d : Ixon.Definition} {ci₀ : ConstantInfo .anon} (hs : store a = some c)
    (hi : c.info = .defn d) (hl : InLogic c)
    (hr : DefnReads (exprReader t blob c id (soloSelf t a)) (keyOf t a) d ci₀) :
    ReadsIn t store blob a ci₀ := by
  unfold ReadsIn
  refine ⟨c, hs, ?_⟩
  rw [hi]
  exact And.intro hl hr

/-- A standalone axiom record's reading. -/
theorem ReadsIn.of_axio {t : RoleTable} {store : Store}
    {blob : _root_.Address → Option ByteArray} {a : _root_.Address} {c : Ixon.Constant}
    {ax : Ixon.Axiom} {ci₀ : ConstantInfo .anon} (hs : store a = some c)
    (hi : c.info = .axio ax) (hl : InLogic c)
    (hr : AxiomReads (exprReader t blob c id (fun _ => none)) (keyOf t a) ax ci₀) :
    ReadsIn t store blob a ci₀ := by
  unfold ReadsIn
  refine ⟨c, hs, ?_⟩
  rw [hi]
  exact And.intro hl hr

/-- An inductive member's reading, at its projection record's address. -/
theorem ReadsIn.of_ind {t : RoleTable} {store : Store}
    {blob : _root_.Address → Option ByteArray} {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {i : Nat} {ind : Ixon.Inductive} {ci₀ : ConstantInfo .anon}
    (hi : i < UInt64.size) (hs : store B = some cb) (hinfo : cb.info = .muts ms)
    (hm : ms[i]? = some (.indc ind)) (hl : InLogic cb)
    (hp : store (memberAddr B i (.indc ind)) = some (memberProjection B i (.indc ind)))
    (hr : IndReads (exprReader t blob cb id (blockSelf t B ms))
      (keyOf t (memberAddr B i (.indc ind))) ind ci₀) :
    ReadsIn t store blob (memberAddr B i (.indc ind)) ci₀ := by
  unfold ReadsIn
  refine ⟨memberProjection B i (.indc ind), hp, ?_⟩
  show ∃ cb' ms' ind',
    MemberAt store (memberAddr B i (.indc ind)) (memberProjection B i (.indc ind)) B cb' ms'
      i.toUInt64.toNat (.indc ind') ∧
    IndReads (exprReader t blob cb' id (blockSelf t B ms'))
      (keyOf t (memberAddr B i (.indc ind))) ind' ci₀
  rw [toUInt64_toNat hi]
  exact ⟨cb, ms, ind,
    And.intro hs (And.intro hinfo (And.intro hm (And.intro rfl (And.intro rfl hl)))), hr⟩

/-- A constructor's reading, at its projection record's address. -/
theorem ReadsIn.of_ctor {t : RoleTable} {store : Store}
    {blob : _root_.Address → Option ByteArray} {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {i j : Nat} {ind : Ixon.Inductive} {ct : Ixon.Constructor}
    {ci₀ : ConstantInfo .anon} (hi : i < UInt64.size) (hj : j < UInt64.size)
    (hs : store B = some cb) (hinfo : cb.info = .muts ms) (hm : ms[i]? = some (.indc ind))
    (hct : ind.ctors[j]? = some ct) (hcidx : ct.cidx.toNat = j) (hl : InLogic cb)
    (hp : store (ctorAddr B i j) = some (constructorProjection B i j))
    (hr : CtorReads (exprReader t blob cb id (blockSelf t B ms)) (keyOf t (ctorAddr B i j))
      ct ci₀) :
    ReadsIn t store blob (ctorAddr B i j) ci₀ := by
  unfold ReadsIn
  refine ⟨constructorProjection B i j, hp, ?_⟩
  show ∃ cb' ms' ind' ct', store B = some cb' ∧ cb'.info = .muts ms' ∧
    ms'[i.toUInt64.toNat]? = some (.indc ind') ∧ ind'.ctors[j.toUInt64.toNat]? = some ct' ∧
    ct'.cidx.toNat = j.toUInt64.toNat ∧
    constructorProjection B i j = constructorProjection B i.toUInt64.toNat j.toUInt64.toNat ∧
    ctorAddr B i j = ctorAddr B i.toUInt64.toNat j.toUInt64.toNat ∧ InLogic cb' ∧
    CtorReads (exprReader t blob cb' id (blockSelf t B ms')) (keyOf t (ctorAddr B i j)) ct' ci₀
  rw [toUInt64_toNat hi, toUInt64_toNat hj]
  exact ⟨cb, ms, ind, ct, hs, hinfo, hm, hct, hcidx, rfl, rfl, hl, hr⟩

end IxVM.Consistency
