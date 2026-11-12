import IxVMRefinement.Core.Specs.Common

/-! # Specs: the role lookups and the role-specification tables the core reads

The core reads the role table only through a few lookups of `KernelRoles` (is the constant at an
address bound to a given role? which address does the table bind to a role?) and a few constant
tables of `KernelRoleSpec` (a role's number, the native rule that fires on a role's constant).
Against `RCRep`/`TableRep` (`Ctx.lean`), whose maps hold only the table's entries, every
**positive** answer is the table's: `role_is(rc, a, r) = 1` gives `c.t.addressOf? r = some a`
(so `c.κ a = .role r` once `EnvFacts.tableWf` holds), and `role_addr(rc, r)` returns an address
the table binds to `r`. A failed lookup claims nothing (the maps' search order is not
constrained). A role's number is its index in `Ix.Kernel.Role.all` (`roleNum`, the binding
section's role byte); the generated constant tables agree with it (`role_nat` is `0`, …).

The role arguments are stated at a role's number: `∀ ro, args = [.., .field (roleNum ro)]`.
Callers obtain them from the constant tables, whose specs give exactly that form. -/

namespace IxVM.Refinement.Core.Specs.Roles

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

set_option linter.unusedVariables false

/-! ## Map lookups -/

/-- `KernelRoles::role_map_lookup_or_default<&[Field; 32]>(key, tree, default)` (the role →
address map): the default, or a value whose entry, at the key, satisfies whatever every entry of
the tree satisfies. Allocates nothing. -/
def role_map_lookup_or_default_addr : SpecFn := fun _c args h r h' calls =>
  ∀ kv tree dflt, args = [kv, tree, dflt] → ∀ k : F, kv = .field k →
    ∀ P : Heap F → F → SourceValue F → Prop, RoleMapAll roleAddrMapEnum P h tree →
      h' = h ∧ (r = dflt ∨ P h k r)

/-- `KernelRoles::role_map_lookup_or_default<&Lists::Node<KernelRoles::RoleEvidence>>(key, tree,
default)` (the role → evidence map), as `role_map_lookup_or_default_addr`. -/
def role_map_lookup_or_default_evidence : SpecFn := fun _c args h r h' calls =>
  ∀ kv tree dflt, args = [kv, tree, dflt] → ∀ k : F, kv = .field k →
    ∀ P : Heap F → F → SourceValue F → Prop, RoleMapAll roleEvMapEnum P h tree →
      h' = h ∧ (r = dflt ∨ P h k r)

/-- `RBTreeMap::rbtree_map_lookup_or_default<Field>(key, tree, default)` (the address → role
map): the default, or a value whose entry is at an address equal to the key (`canon_addr_cmp`
answers "equal" only on equal addresses) and satisfies whatever every entry satisfies. -/
def rbtree_map_lookup_or_default_field : SpecFn := fun _c args h r h' calls =>
  ∀ kp tree dflt, args = [kp, tree, dflt] → ∀ a : Bytes.Address, RepAddr h a kp →
    ∀ P : Heap F → Bytes.Address → SourceValue F → Prop, AddrMapAll addrMapEnum P h tree →
      h' = h ∧ (r = dflt ∨ P h a r)

/-! ## The table and the role context -/

/-- `KernelRoles::role_ctx_table(rc)`: the context's table. -/
def role_ctx_table : SpecFn := fun c args h r h' _calls =>
  ∀ rc, args = [rc] → c.rc h rc → h' = h ∧ TableRep c.t h r

/-- `KernelRoles::role_addr_index(tbl)`: the table's address → role map, every entry the table's
(`IndexEntry`). -/
def role_addr_index : SpecFn := fun c args h r h' _calls =>
  ∀ tbl, args = [tbl] → TableRep c.t h tbl →
    h' = h ∧ AddrMapAll addrMapEnum (IndexEntry c.t) h r

/-- `KernelRoles::role_bound_addr_or_zero(tbl, r)`: an address that the table binds to the role
numbered `k`, or the zero address. -/
def role_bound_addr_or_zero : SpecFn := fun c args h r h' calls =>
  ∀ tbl (k : F), args = [tbl, .field k] → Good c calls → TableRep c.t h tbl →
    ∃ a : Bytes.Address, RepAddr h' a r ∧
      ((∃ ro, k = roleNum ro ∧ c.t.addressOf? ro = some (ixAddr a)) ∨
        a.toList = List.replicate 32 0)

/-- `KernelRoles::role_is_bound(tbl, r)` at a role's number: `1` only if the table binds the
role. Nothing is claimed for `0`. -/
def role_is_bound : SpecFn := fun c args h r h' calls =>
  ∀ tbl (ro : Ix.Kernel.Role), args = [tbl, .field (roleNum ro)] → Good c calls →
    TableRep c.t h tbl → r = .field 1 → c.binds ro

/-- `KernelRoles::role_bound_addr(tbl, r)` at a role's number (it asserts `role_is_bound`): an
address the table binds to the role. -/
def role_bound_addr : SpecFn := fun c args h r h' calls =>
  ∀ tbl (ro : Ix.Kernel.Role), args = [tbl, .field (roleNum ro)] → Good c calls →
    TableRep c.t h tbl →
      ∃ a : Bytes.Address, RepAddr h' a r ∧ c.t.addressOf? ro = some (ixAddr a)

/-- `KernelRoles::role_index_of(rc, a)`: `0`, or one more than the number of a role the table
binds to `a`. Allocates nothing. -/
def role_index_of : SpecFn := fun c args h r h' calls =>
  ∀ rc ap (a : Bytes.Address), args = [rc, ap] → Good c calls → c.rc h rc → RepAddr h a ap →
    h' = h ∧ (r = .field 0 ∨
      ∃ ro : Ix.Kernel.Role, r = .field (roleNum ro + 1) ∧ c.t.addressOf? ro = some (ixAddr a))

/-- `KernelRoles::role_of(rc, a)`: `0` (no role, or one whose group is not yet in force), or one
more than the number of a role the table binds to `a`. -/
def role_of : SpecFn := fun c args h r h' calls =>
  ∀ rc ap (a : Bytes.Address), args = [rc, ap] → Good c calls → c.rc h rc → RepAddr h a ap →
    r = .field 0 ∨
      ∃ ro : Ix.Kernel.Role, r = .field (roleNum ro + 1) ∧ c.t.addressOf? ro = some (ixAddr a)

/-- `KernelRoles::role_is(rc, a, r)` at a role's number: `1` only if the table binds the role to
`a` (`Ctx.κ (ixAddr a) = .role ro` given `EnvFacts.tableWf`). Nothing is claimed for `0`. -/
def role_is : SpecFn := fun c args h r h' calls =>
  ∀ rc ap (a : Bytes.Address) (ro : Ix.Kernel.Role), args = [rc, ap, .field (roleNum ro)] →
    Good c calls → c.rc h rc → RepAddr h a ap → r = .field 1 →
      c.t.addressOf? ro = some (ixAddr a)

/-- `KernelRoles::role_addr(rc, r)` at a role's number: an address the table binds to the role
(the derivation exists only if the table binds it and its group is in force). -/
def role_addr : SpecFn := fun c args h r h' calls =>
  ∀ rc (ro : Ix.Kernel.Role), args = [rc, .field (roleNum ro)] → Good c calls → c.rc h rc →
    ∃ a : Bytes.Address, RepAddr h' a r ∧ c.t.addressOf? ro = some (ixAddr a)

/-- `KernelRoles::role_used_implicitly(rc, r)` at a role's number: `role_addr`'s address (the
call also checks the constant there; the core reads only the address). -/
def role_used_implicitly : SpecFn := fun c args h r h' calls =>
  ∀ rc (ro : Ix.Kernel.Role), args = [rc, .field (roleNum ro)] → Good c calls → c.rc h rc →
    ∃ a : Bytes.Address, RepAddr h' a r ∧ c.t.addressOf? ro = some (ixAddr a)

/-- `KernelRoles::role_evidence(tbl, r)` at a role's number: the table's evidence of the role, one
for one, or the empty list (no entry found). -/
def role_evidence : SpecFn := fun c args h r h' _calls =>
  ∀ tbl (ro : Ix.Kernel.Role), args = [tbl, .field (roleNum ro)] → TableRep c.t h tbl →
    ∃ es : List (Ix.Kernel.Evidence _root_.Address), RepList evListEnum EvRep h' es r ∧
      (es = [] ∨ ∃ arr, (ro, arr) ∈ c.t.evidence.toList ∧ arr.toList = es)

/-! ## The role-specification tables -/

/-- A constant table of `KernelRoleSpec`: the role's number. Allocates nothing. -/
def RoleConst (ro : Ix.Kernel.Role) : SpecFn := fun _c args h r h' _calls =>
  args = [] → r = .field (roleNum ro) ∧ h' = h

/-- `KernelRoleSpec::role_nat()`. -/
def role_nat : SpecFn := RoleConst .nat
/-- `KernelRoleSpec::role_nat_zero()`. -/
def role_nat_zero : SpecFn := RoleConst .natZero
/-- `KernelRoleSpec::role_nat_succ()`. -/
def role_nat_succ : SpecFn := RoleConst .natSucc
/-- `KernelRoleSpec::role_nat_add()`. -/
def role_nat_add : SpecFn := RoleConst .natAdd
/-- `KernelRoleSpec::role_bool_true()`. -/
def role_bool_true : SpecFn := RoleConst .boolTrue
/-- `KernelRoleSpec::role_bool_false()`. -/
def role_bool_false : SpecFn := RoleConst .boolFalse
/-- `KernelRoleSpec::role_char()`. -/
def role_char : SpecFn := RoleConst .char
/-- `KernelRoleSpec::role_char_of_nat()`. -/
def role_char_of_nat : SpecFn := RoleConst .charOfNat
/-- `KernelRoleSpec::role_list_nil()`. -/
def role_list_nil : SpecFn := RoleConst .listNil
/-- `KernelRoleSpec::role_list_cons()`. -/
def role_list_cons : SpecFn := RoleConst .listCons
/-- `KernelRoleSpec::role_string()`. -/
def role_string : SpecFn := RoleConst .string
/-- `KernelRoleSpec::role_string_of_list()`. -/
def role_string_of_list : SpecFn := RoleConst .stringOfList
/-- `KernelRoleSpec::role_quot_mk()`. -/
def role_quot_mk : SpecFn := RoleConst .quotMk
/-- `KernelRoleSpec::role_quot_lift()`. -/
def role_quot_lift : SpecFn := RoleConst .quotLift
/-- `KernelRoleSpec::role_quot_ind()`. -/
def role_quot_ind : SpecFn := RoleConst .quotInd

/-- `KernelRoleSpec::role_prim_family(r)` at a role's number: the native rule IxVM fires on the
role's constant, its family and operation (`Ix.SpecDigest.nativeOp`, which the specification
digest commits to; `(0, 0)`: none). Exact: the dispatcher reads which native operation the head
constant is from it. Allocates nothing. -/
def role_prim_family : SpecFn := fun _c args h r h' _calls =>
  ∀ ro : Ix.Kernel.Role, args = [.field (roleNum ro)] →
    r = .tuple [.field ((Ix.SpecDigest.nativeOp ro).1 : F), .field ((Ix.SpecDigest.nativeOp ro).2 : F)] ∧
      h' = h

/-! ## The family -/

/-- The functions of this family. -/
inductive Fn where
  | role_map_lookup_or_default_addr
  | role_map_lookup_or_default_evidence
  | rbtree_map_lookup_or_default_field
  | role_ctx_table
  | role_addr_index
  | role_bound_addr_or_zero
  | role_is_bound
  | role_bound_addr
  | role_index_of
  | role_of
  | role_is
  | role_addr
  | role_used_implicitly
  | role_evidence
  | role_nat
  | role_nat_zero
  | role_nat_succ
  | role_nat_add
  | role_bool_true
  | role_bool_false
  | role_char
  | role_char_of_nat
  | role_list_nil
  | role_list_cons
  | role_string
  | role_string_of_list
  | role_quot_mk
  | role_quot_lift
  | role_quot_ind
  | role_prim_family
  deriving DecidableEq, Repr

/-- The symbol `ObsFn` names each function by. -/
def Fn.name : Fn → String
  | .role_map_lookup_or_default_addr =>
    Obs.Names.«KernelRoles::role_map_lookup_or_default<&[Field; 32]>»
  | .role_map_lookup_or_default_evidence =>
    Obs.Names.«KernelRoles::role_map_lookup_or_default<&Lists::Node<KernelRoles::RoleEvidence>>»
  | .rbtree_map_lookup_or_default_field => Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>»
  | .role_ctx_table => "KernelRoles::role_ctx_table"
  | .role_addr_index => "KernelRoles::role_addr_index"
  | .role_bound_addr_or_zero => "KernelRoles::role_bound_addr_or_zero"
  | .role_is_bound => "KernelRoles::role_is_bound"
  | .role_bound_addr => "KernelRoles::role_bound_addr"
  | .role_index_of => "KernelRoles::role_index_of"
  | .role_of => "KernelRoles::role_of"
  | .role_is => "KernelRoles::role_is"
  | .role_addr => "KernelRoles::role_addr"
  | .role_used_implicitly => "KernelRoles::role_used_implicitly"
  | .role_evidence => "KernelRoles::role_evidence"
  | .role_nat => "KernelRoleSpec::role_nat"
  | .role_nat_zero => "KernelRoleSpec::role_nat_zero"
  | .role_nat_succ => "KernelRoleSpec::role_nat_succ"
  | .role_nat_add => "KernelRoleSpec::role_nat_add"
  | .role_bool_true => "KernelRoleSpec::role_bool_true"
  | .role_bool_false => "KernelRoleSpec::role_bool_false"
  | .role_char => "KernelRoleSpec::role_char"
  | .role_char_of_nat => "KernelRoleSpec::role_char_of_nat"
  | .role_list_nil => "KernelRoleSpec::role_list_nil"
  | .role_list_cons => "KernelRoleSpec::role_list_cons"
  | .role_string => "KernelRoleSpec::role_string"
  | .role_string_of_list => "KernelRoleSpec::role_string_of_list"
  | .role_quot_mk => "KernelRoleSpec::role_quot_mk"
  | .role_quot_lift => "KernelRoleSpec::role_quot_lift"
  | .role_quot_ind => "KernelRoleSpec::role_quot_ind"
  | .role_prim_family => "KernelRoleSpec::role_prim_family"

/-- Each function's spec. -/
def Fn.spec : Fn → SpecFn
  | .role_map_lookup_or_default_addr => Specs.Roles.role_map_lookup_or_default_addr
  | .role_map_lookup_or_default_evidence => Specs.Roles.role_map_lookup_or_default_evidence
  | .rbtree_map_lookup_or_default_field => Specs.Roles.rbtree_map_lookup_or_default_field
  | .role_ctx_table => Specs.Roles.role_ctx_table
  | .role_addr_index => Specs.Roles.role_addr_index
  | .role_bound_addr_or_zero => Specs.Roles.role_bound_addr_or_zero
  | .role_is_bound => Specs.Roles.role_is_bound
  | .role_bound_addr => Specs.Roles.role_bound_addr
  | .role_index_of => Specs.Roles.role_index_of
  | .role_of => Specs.Roles.role_of
  | .role_is => Specs.Roles.role_is
  | .role_addr => Specs.Roles.role_addr
  | .role_used_implicitly => Specs.Roles.role_used_implicitly
  | .role_evidence => Specs.Roles.role_evidence
  | .role_nat => Specs.Roles.role_nat
  | .role_nat_zero => Specs.Roles.role_nat_zero
  | .role_nat_succ => Specs.Roles.role_nat_succ
  | .role_nat_add => Specs.Roles.role_nat_add
  | .role_bool_true => Specs.Roles.role_bool_true
  | .role_bool_false => Specs.Roles.role_bool_false
  | .role_char => Specs.Roles.role_char
  | .role_char_of_nat => Specs.Roles.role_char_of_nat
  | .role_list_nil => Specs.Roles.role_list_nil
  | .role_list_cons => Specs.Roles.role_list_cons
  | .role_string => Specs.Roles.role_string
  | .role_string_of_list => Specs.Roles.role_string_of_list
  | .role_quot_mk => Specs.Roles.role_quot_mk
  | .role_quot_lift => Specs.Roles.role_quot_lift
  | .role_quot_ind => Specs.Roles.role_quot_ind
  | .role_prim_family => Specs.Roles.role_prim_family

end IxVM.Refinement.Core.Specs.Roles
