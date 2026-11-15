import IxVMRefinement.Assembly.ProjSafe
import IxVMRefinement.Assembly.ModelSupport

/-! # Reference and literal support from the actual reader closure

These facts use closure membership and concrete stored role bindings. Literal support is
obtained from the record's ground edges only when the record contains that literal kind.
-/

namespace IxVM.Refinement.Assembly

open IxVM.Consistency
open Ix.Kernel

def ReadOrderKey (t : RoleTable) (order : List _root_.Address) (k : Key .anon) : Prop :=
  ∃ a ∈ order, Core.keyOf t a = k

theorem readOrder_ref {t : RoleTable} {E : Ixon.Env} {S : _root_.Address → Prop}
    {order : List _root_.Address} (horder : UsedClosureOrderAt t E S order)
    {a b : _root_.Address} {c : Ixon.Constant}
    (ha : a ∈ order) (hrecord : Ix.Cert.recordAt E a = some c)
    {i : Nat} (hi : i ∈ usedRefIdxs c) (href : c.refs[i]? = some b)
    (hstored : E.consts.contains b = true) : b ∈ order :=
  (horder.complete b).mpr
    (.step ((horder.complete a).mp ha) ⟨c, hrecord, .inr ⟨⟨i, hi, href⟩, hstored⟩⟩)

theorem readOrder_owner {t : RoleTable} {E : Ixon.Env} {S : _root_.Address → Prop}
    {order : List _root_.Address} (horder : UsedClosureOrderAt t E S order)
    {a : _root_.Address} {c : Ixon.Constant}
    (ha : a ∈ order) (hrecord : Ix.Cert.recordAt E a = some c) :
    Ix.Cert.ownerOf a c ∈ order := by
  by_cases hself : Ix.Cert.ownerOf a c = a
  · rwa [hself]
  · exact (horder.complete _).mpr
      (.step ((horder.complete a).mp ha) ⟨c, hrecord, .inl ⟨rfl, hself⟩⟩)

theorem readOrder_literal_role {t : RoleTable} {E : Ixon.Env} {S : _root_.Address → Prop}
    {order : List _root_.Address} (horder : UsedClosureOrderAt t E S order)
    {a b : _root_.Address} {c : Ixon.Constant} {r : Role}
    (ha : a ∈ order) (hrecord : Ix.Cert.recordAt E a = some c)
    (hr : r ∈ Ix.Cert.literalRoles c) (hbound : t.addressOf? r = some b)
    (hstored : E.consts.contains b = true) : b ∈ order :=
  (horder.complete b).mpr
    (.ground ((horder.complete a).mp ha)
      ⟨hstored, r, hbound, .inr ⟨c, hrecord, hr⟩⟩)

theorem readOrder_literal_role_key {t : RoleTable} {E : Ixon.Env} {S : _root_.Address → Prop}
    {order : List _root_.Address} (horder : UsedClosureOrderAt t E S order)
    (hcheck : t.check = .ok ()) {a b : _root_.Address} {c : Ixon.Constant} {r : Role}
    (ha : a ∈ order) (hrecord : Ix.Cert.recordAt E a = some c)
    (hr : r ∈ Ix.Cert.literalRoles c) (hbound : t.addressOf? r = some b)
    (hstored : E.consts.contains b = true) : ReadOrderKey t order (.role r) :=
  ⟨b, readOrder_literal_role horder ha hrecord hr hbound hstored,
    keyOf_eq_of_bound hcheck (Ix.Cert.ReadingKeys.bound_of_addressOf hbound)⟩

/-- A record containing a string literal brings the concrete bound literal-support records
into its closure, and hence supplies the keys needed by string-literal denotation. -/
theorem readOrder_string_support {t : RoleTable} {E : Ixon.Env} {S : _root_.Address → Prop}
    {order : List _root_.Address} (horder : UsedClosureOrderAt t E S order)
    (hcheck : t.check = .ok ()) {a : _root_.Address} {c : Ixon.Constant}
    (ha : a ∈ order) (hrecord : Ix.Cert.recordAt E a = some c)
    (hstring : (Reader.literalKinds c).2 = true)
    (havailable : ∀ r ∈ Ix.Cert.literalRoles c,
      ∃ b, t.addressOf? r = some b ∧ E.consts.contains b = true) :
    LitKeys (ReadOrderKey t order) := by
  have hroles : Ix.Cert.literalRoles c =
      [.nat, .natZero, .natSucc, .string, .stringOfList, .list, .listNil, .listCons,
        .char, .charOfNat] := by
    simp [Ix.Cert.literalRoles, hstring, Ix.Cert.keyRoles,
      Reader.strLitSupportNames, Reader.natLitSupportNames]
  have hk : ∀ r ∈ Ix.Cert.literalRoles c, ReadOrderKey t order (.role r) := by
    intro r hr
    obtain ⟨b, hb, hstored⟩ := havailable r hr
    exact readOrder_literal_role_key horder hcheck ha hrecord hr hb hstored
  refine ⟨hk .natZero ?_, hk .natSucc ?_, hk .stringOfList ?_, hk .listNil ?_,
    hk .listCons ?_, hk .char ?_, hk .charOfNat ?_⟩ <;> rw [hroles] <;> decide

end IxVM.Refinement.Assembly
