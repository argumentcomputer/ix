import IxVMRefinement.Core.Specs.Common

/-! # Specs: the role lookups and the role-specification tables the core reads

The core reads the role table only through a few lookups of `KernelRoles` (is the constant at an
address bound to a given role? which address does the table bind to a role?) and a few constant
tables of `KernelRoleSpec` (a role's number, the native rule that fires on a role's constant).
Against `RCRep`/`TableRep` (`Ctx.lean`), whose maps hold only the table's entries, every
**positive** answer is the table's: a nonzero `role_is(rc, a, r)` gives
`c.t.addressOf? r = some a` (so `c.κ a = .role r` once `EnvFacts.tableWf` holds), and
`role_addr(rc, r)` returns an address the table binds to `r`. A failed lookup claims nothing
(the maps' entries are the table's; that every entry of the table is found is not claimed). A
role's number is its index in `Ix.Kernel.Role.all` (`roleNum`, the binding section's role byte);
the generated constant tables agree with it (`role_nat` is `0`, …).

The role arguments are stated at a role's number: `∀ ro, args = [.., .field (roleNum ro)]`.
Callers obtain them from the constant tables, whose specs give exactly that form. -/

namespace IxVM.Refinement.Core.Specs.Roles

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

set_option linter.unusedVariables false

/-! ## The role maps' search

`role_map_lookup_or_default` is called twice on the same map by `role_bound_addr` (once inside
`role_is_bound`, once for the answer), and the two answers must agree. So its spec is functional:
the result is the outcome of the search the code runs, a relation that determines its outcome. -/

/-- **The search `KernelRoles::role_map_lookup_or_default` runs** for the key `k` in a role map
held by value (`Node(color, key, value, &left, &right)`): the value at a node whose key is `k`;
the left subtree where `k` is below the node's key, the right one where it is above (the code
compares with `UInt32::less_than_fields`, which answers `1` exactly on `<`); `none` at `Nil`. The
three node cases exclude one another, so a map and a key have at most one outcome, and the
outcome is the same in every extension of the heap. -/
inductive RoleMapSearch (en : String) (h : Heap F) (k : F) :
    SourceValue F → Option (SourceValue F) → Prop where
  | nil : RoleMapSearch en h k (.construct en "Nil" []) none
  | here {c v lp rp : SourceValue F} :
      RoleMapSearch en h k (.construct en "Node" [c, .field k, v, lp, rp]) (some v)
  | left {c v lp rp lv : SourceValue F} {key : F} {res : Option (SourceValue F)}
      (hlt : ZMod.val k < ZMod.val key) (hl : loadValue h lp = .ok lv)
      (hs : RoleMapSearch en h k lv res) :
      RoleMapSearch en h k (.construct en "Node" [c, .field key, v, lp, rp]) res
  | right {c v lp rp rv : SourceValue F} {key : F} {res : Option (SourceValue F)}
      (hgt : ZMod.val key < ZMod.val k) (hr : loadValue h rp = .ok rv)
      (hs : RoleMapSearch en h k rv res) :
      RoleMapSearch en h k (.construct en "Node" [c, .field key, v, lp, rp]) res

/-- The zero address (`&[UInt8::BYTE_0; 32]`, the role → address lookup's default). -/
def zeroAddr : Bytes.Address := Vector.ofFn fun _ => 0

/-- `byRole` is the role → address map of the table node `tbl` points to. -/
def ByRole (h : Heap F) (tbl byRole : SourceValue F) : Prop :=
  ∃ bp byAddr ev, loadValue h tbl = .ok (.construct rtEnum "Mk" [bp, byRole, byAddr, ev])

/-- **The outcome of the role → address search binds the role**: a found value is an address the
table binds to the role; a failed search means the table binds the role to the zero address
(what `role_is_bound`'s index test establishes for the default). -/
def BoundAt (c : Ctx) (h : Heap F) (ro : Ix.Kernel.Role) : Option (SourceValue F) → Prop
  | some v => ∃ a : Bytes.Address, RepAddr h a v ∧ c.t.addressOf? ro = some (ixAddr a)
  | none => c.t.addressOf? ro = some (ixAddr zeroAddr)

/-! ## Map lookups -/

/-- `KernelRoles::role_map_lookup_or_default<&[Field; 32]>(key, tree, default)` (the role →
address map): the outcome of the search (`RoleMapSearch`), or the default where it finds
nothing. -/
def role_map_lookup_or_default_addr : SpecFn := fun _c args h r h' calls =>
  ∀ kv tree dflt, args = [kv, tree, dflt] → ∀ k : F, kv = .field k →
    ∃ res, RoleMapSearch roleAddrMapEnum h k tree res ∧ r = res.getD dflt

/-- `KernelRoles::role_map_lookup_or_default<&Lists::Node<KernelRoles::RoleEvidence>>(key, tree,
default)` (the role → evidence map), as `role_map_lookup_or_default_addr`. -/
def role_map_lookup_or_default_evidence : SpecFn := fun _c args h r h' calls =>
  ∀ kv tree dflt, args = [kv, tree, dflt] → ∀ k : F, kv = .field k →
    ∃ res, RoleMapSearch roleEvMapEnum h k tree res ∧ r = res.getD dflt

/-- `RBTreeMap::rbtree_map_lookup_or_default<Field>(key, tree, default)` (the address → role
map): the default, or a value whose entry is at an address equal to the key (`canon_addr_cmp`
answers "equal" only on equal addresses) and satisfies whatever every entry satisfies. Which of
the two is not claimed. -/
def rbtree_map_lookup_or_default_field : SpecFn := fun _c args h r h' calls =>
  ∀ kp tree dflt, args = [kp, tree, dflt] → ∀ a : Bytes.Address, RepAddr h a kp →
    ∀ P : Heap F → Bytes.Address → SourceValue F → Prop, AddrMapAll addrMapEnum P h tree →
      r = dflt ∨ P h a r

/-! ## The table and the role context -/

/-- `KernelRoles::role_ctx_table(rc)`: the context's table. -/
def role_ctx_table : SpecFn := fun c args h r h' _calls =>
  ∀ rc, args = [rc] → c.rc h rc → h' = h ∧ TableRep c.t h r

/-- `KernelRoles::role_addr_index(tbl)`: the table's address → role map, every entry the table's
(`IndexEntry`). -/
def role_addr_index : SpecFn := fun c args h r h' _calls =>
  ∀ tbl, args = [tbl] → TableRep c.t h tbl →
    h' = h ∧ AddrMapAll addrMapEnum (IndexEntry c.t) h r

/-- `KernelRoles::role_bound_addr_or_zero(tbl, r)`: the outcome of the search for `r` in the
table's role → address map, or a fresh pointer to the zero address where it finds nothing. -/
def role_bound_addr_or_zero : SpecFn := fun _c args h r h' calls =>
  ∀ tbl (k : F), args = [tbl, .field k] → ∀ byRole, ByRole h tbl byRole →
    ∃ res, RoleMapSearch roleAddrMapEnum h k byRole res ∧
      (res = some r ∨ (res = none ∧ RepAddr h' zeroAddr r))

/-- `KernelRoles::role_is_bound(tbl, r)` at a role's number: a nonzero answer means the search
for the role in the table's role → address map has an outcome that binds the role (`BoundAt`):
the address found, or the zero address where nothing is found. In particular the table binds the
role. Nothing is claimed for `0`. -/
def role_is_bound : SpecFn := fun c args h r h' calls =>
  ∀ tbl (ro : Ix.Kernel.Role), args = [tbl, .field (roleNum ro)] → Good c calls →
    TableRep c.t h tbl → r ≠ .field 0 → ∀ byRole, ByRole h tbl byRole →
      ∃ res, RoleMapSearch roleAddrMapEnum h (roleNum ro) byRole res ∧ BoundAt c h ro res

/-- `KernelRoles::role_bound_addr(tbl, r)` at a role's number (it asserts `role_is_bound`): an
address the table binds to the role. -/
def role_bound_addr : SpecFn := fun c args h r h' calls =>
  ∀ tbl (ro : Ix.Kernel.Role), args = [tbl, .field (roleNum ro)] → Good c calls →
    TableRep c.t h tbl →
      ∃ a : Bytes.Address, RepAddr h' a r ∧ c.t.addressOf? ro = some (ixAddr a)

/-- `KernelRoles::role_index_of(rc, a)`: `0`, or one more than the number of a role the table
binds to `a`. -/
def role_index_of : SpecFn := fun c args h r h' calls =>
  ∀ rc ap (a : Bytes.Address), args = [rc, ap] → Good c calls → c.rc h rc → RepAddr h a ap →
    r = .field 0 ∨
      ∃ ro : Ix.Kernel.Role, r = .field (roleNum ro + 1) ∧ c.t.addressOf? ro = some (ixAddr a)

/-- `KernelRoles::role_of(rc, a)`: `0` (no role, or one whose group is not yet in force), or one
more than the number of a role the table binds to `a` and in force. -/
def role_of : SpecFn := fun c args h r h' calls =>
  ∀ rc ap (a : Bytes.Address), args = [rc, ap] → Good c calls → c.rc h rc → RepAddr h a ap →
    r = .field 0 ∨
      ∃ ro : Ix.Kernel.Role, r = .field (roleNum ro + 1) ∧ c.t.addressOf? ro = some (ixAddr a) ∧
        c.inForce ro

/-- `KernelRoles::role_is(rc, a, r)` at a role's number: a nonzero answer (the code answers `0`
or `1`) means the table binds the role to `a` (`Ctx.κ (ixAddr a) = .role ro` given
`EnvFacts.tableWf`) and the role is in force (`role_of`'s group test: its group is below the
context's limit). Nothing is claimed for `0`. -/
def role_is : SpecFn := fun c args h r h' calls =>
  ∀ rc ap (a : Bytes.Address) (ro : Ix.Kernel.Role), args = [rc, ap, .field (roleNum ro)] →
    Good c calls → c.rc h rc → RepAddr h a ap → r ≠ .field 0 →
      c.t.addressOf? ro = some (ixAddr a) ∧ c.inForce ro

/-- `KernelRoles::role_addr(rc, r)` at a role's number: an address the table binds to the role
(the derivation exists only if the table binds it and its group is in force). -/
def role_addr : SpecFn := fun c args h r h' calls =>
  ∀ rc (ro : Ix.Kernel.Role), args = [rc, .field (roleNum ro)] → Good c calls → c.rc h rc →
    ∃ a : Bytes.Address, RepAddr h' a r ∧ c.t.addressOf? ro = some (ixAddr a) ∧ c.inForce ro

/-- `KernelRoles::role_used_implicitly(rc, r)` at a role's number: `role_addr`'s address (the
call also checks the constant there; the core reads only the address). -/
def role_used_implicitly : SpecFn := fun c args h r h' calls =>
  ∀ rc (ro : Ix.Kernel.Role), args = [rc, .field (roleNum ro)] → Good c calls → c.rc h rc →
    ∃ a : Bytes.Address, RepAddr h' a r ∧ c.t.addressOf? ro = some (ixAddr a) ∧ c.inForce ro

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
