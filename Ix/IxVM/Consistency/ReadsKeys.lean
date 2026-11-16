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

end IxVM.Consistency
