import IxVMRefinement.Decl.NativeFront
import IxVM.Obs.KernelModeled

/-! # A modeled recursor's type names no member of its own family record

`KernelModeled::check_recs` asserts, after the well-scopedness check of each modeled recursor's
type, `expr_mentions_addrs(ty, fam) = 0` with `fam` the family record's recursor addresses
(`family_recs(rec_block)`). This module states what that answer means of the converted type:

* `addr_list_contains_zero_spec`: `KernelCheck::addr_list_contains(xs, b)` answering `0` on a
  list of addresses means no address of the list is `b`, and the heap is unchanged.
* `expr_mentions_addrs_zero_spec`: `KernelModeled::expr_mentions_addrs(e, xs)` answering `0` on
  a term exactly represented at no free variable (`TmExact κ 0 Γ`) means the term mentions no key
  all of whose addresses are in the list, neither as a constant nor as a projection's structure
  (`Expr.mentionsConst`).

The consumer is the recursor's front door in IxCK's renamed record (`ConstantValRunJ`'s
`constsResolve` at the provisioning environment, which holds the recursors provisioned before this
one but not the later ones). -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open Ix.Kernel (Expr)

/-- **`addr_list_contains` answering `0`**: no address of the list is the target, and the heap
is unchanged. -/
theorem addr_list_contains_zero_spec {as : List Bytes.Address} {b : Bytes.Address}
    {xs tgt : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hxs : RepList addrListEnum (Bytes.RepAddressRef addrTy) h as xs)
    (htgt : Bytes.RepAddressRef addrTy h b tgt)
    (ev : ObsFn W "KernelCheck::addr_list_contains" [xs, tgt] h (.field 0) h' cs) :
    h' = h ∧ ∀ a ∈ as, ixAddr a ≠ ixAddr b := by
  match Obs.«KernelCheck::addr_list_contains».obs ev with
  | .Nil (ld12 := ld) (he21 := hh) .. =>
    have hnil := Lib.rep_nil_of_load hxs ld
    subst hnil
    exact ⟨hh, fun a ha => nomatch ha⟩
  | .Cons_n1 (he75 := hr) .. =>
    exact absurd (Value.field.inj hr) zero_ne_one
  | .Cons_other (ld12 := ld) (ev54 := ev_eq) (hne78 := hne) (ev87 := ev_rest)
      (hc104 := hc) .. =>
    obtain ⟨z, zs, rfl, hz, hzs⟩ := Lib.rep_cons_of_load hxs ld
    obtain ⟨heq_v, rfl⟩ := Lib.address_eq_spec ev_eq hz htgt
    have hne_addr : ixAddr z ≠ ixAddr b := by
      intro hsame
      have hzb : z = b := ixAddr_inj hsame
      rw [ite_eq_left hzb] at heq_v
      exact hne heq_v
    obtain ⟨hh, hrest⟩ := addr_list_contains_zero_spec hzs htgt ev_rest
    refine ⟨hh, fun a ha => ?_⟩
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact hne_addr
    · exact hrest a ha'
termination_by cs.length
decreasing_by
  simp only [hc, List.length_cons, List.length_append]
  omega

/-- A key all of whose addresses are listed is not the key of an unlisted address. -/
private theorem key_ne_of_unlisted {κ : _root_.Address → KKey} {as : List Bytes.Address}
    {T : KKey} (hT : ∀ a : Bytes.Address, κ (ixAddr a) = T → ∃ b ∈ as, ixAddr b = ixAddr a)
    {a : Bytes.Address} (hun : ∀ b ∈ as, ixAddr b ≠ ixAddr a) :
    κ (ixAddr a) ≠ T := by
  intro heq
  obtain ⟨b, hb, hba⟩ := hT a heq
  exact hun b hb hba

/-- **`expr_mentions_addrs` answering `0`**: the exactly represented term mentions no key all of
whose addresses are listed, as a constant or as a projection's structure. Read at no free
variable (`d = 0`): the walk does not descend into a free variable's annotation, which the
reading of a closed type never holds. -/
theorem expr_mentions_addrs_zero_spec {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {as : List Bytes.Address} {T : KKey}
    (hT : ∀ a : Bytes.Address, κ (ixAddr a) = T → ∃ b ∈ as, ixAddr b = ixAddr a)
    {k : Nat} {E : KExpr} {pe xs : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hE : TmExact κ 0 Γ h k E pe)
    (hxs : RepList addrListEnum (Bytes.RepAddressRef addrTy) h as xs)
    (ev : ObsFn W "KernelModeled::expr_mentions_addrs" [pe, xs] h (.field 0) h' cs) :
    E.mentionsConst T = false := by
  match Obs.«KernelModeled::expr_mentions_addrs».obs ev with
  | .Const (ld12 := ld) (ev36 := ev_in) .. =>
    obtain ⟨a, ls, rfl, ha, -⟩ := hE.const_of_load ld
    obtain ⟨-, hun⟩ := addr_list_contains_zero_spec hxs ha ev_in
    simp [Expr.mentionsConst, key_ne_of_unlisted hT hun]
  | .App_n0 (ld12 := ld) (ev85 := ev1) (ev111 := ev2) (hc128 := hc) .. =>
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld
    have hmf := expr_mentions_addrs_zero_spec hT hf hxs ev1
    have hma := expr_mentions_addrs_zero_spec hT (ha.mono ev1.heap_extends)
      (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
        ev1.heap_extends hxs) ev2
    simp [Expr.mentionsConst, hmf, hma]
  | .App_other (he133 := hr) .. => exact absurd (Value.field.inj hr) zero_ne_one
  | .Lam_n0 (ld12 := ld) (ev173 := ev1) (ev199 := ev2) (hc216 := hc) .. =>
    obtain ⟨Et, Eb, _, rfl, ht, hb, _⟩ := hE.lam_of_load ld
    have hmt := expr_mentions_addrs_zero_spec hT ht hxs ev1
    have hmb := expr_mentions_addrs_zero_spec hT (hb.mono ev1.heap_extends)
      (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
        ev1.heap_extends hxs) ev2
    simp [Expr.mentionsConst, hmt, hmb]
  | .Lam_other (he221 := hr) .. => exact absurd (Value.field.inj hr) zero_ne_one
  | .Forall_n0 (ld12 := ld) (ev261 := ev1) (ev287 := ev2) (hc304 := hc) .. =>
    obtain ⟨Et, Eb, _, rfl, ht, hb, _⟩ := hE.forallE_of_load ld
    have hmt := expr_mentions_addrs_zero_spec hT ht hxs ev1
    have hmb := expr_mentions_addrs_zero_spec hT (hb.mono ev1.heap_extends)
      (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
        ev1.heap_extends hxs) ev2
    simp [Expr.mentionsConst, hmt, hmb]
  | .Forall_other (he309 := hr) .. => exact absurd (Value.field.inj hr) zero_ne_one
  | .Let_n0_n0 (ld12 := ld) (ev348 := ev1) (ev383 := ev2) (ev409 := ev3) (hc426 := hc) .. =>
    obtain ⟨Et, Ev, Eb, rfl, _, hv, hb⟩ := hE.letE_of_load ld
    have ext12 := ev1.heap_extends.trans ev2.heap_extends
    have hmv := expr_mentions_addrs_zero_spec hT (hv.mono ev1.heap_extends)
      (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
        ev1.heap_extends hxs) ev2
    have hmb := expr_mentions_addrs_zero_spec hT (hb.mono ext12)
      (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) ext12 hxs) ev3
    exact mentionsConst_instantiate1Lift_false hmb (fun _ => hmv)
  | .Let_n0_other (he431 := hr) .. => exact absurd (Value.field.inj hr) zero_ne_one
  | .Let_other (he438 := hr) .. => exact absurd (Value.field.inj hr) zero_ne_one
  | .Proj_n0 (ld12 := ld) (ev478 := ev1) (ev504 := ev2) (hc521 := hc) .. =>
    obtain ⟨a, i, E₁, _, rfl, ha, he₁⟩ := hE.proj_of_load ld
    obtain ⟨hh, hun⟩ := addr_list_contains_zero_spec hxs ha ev1
    subst hh
    have hm₁ := expr_mentions_addrs_zero_spec hT he₁ hxs ev2
    simp [Expr.mentionsConst, key_ne_of_unlisted hT hun, hm₁]
  | .Proj_other (he526 := hr) .. => exact absurd (Value.field.inj hr) zero_ne_one
  | .other (ld12 := ld) (hne54 := n1) (hne136 := n2) (hne224 := n3) (hne312 := n4)
      (hne441 := n5) (hne529 := n6) .. =>
    cases hE with
    | bvarLocal => rfl
    | bvarFree _ _ _ hd => omega
    | sort => rfl
    | litNat => rfl
    | litStr => rfl
    | const cell =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv
      exact absurd hv.symm (n1 [_, _] rfl)
    | app cell =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv
      exact absurd hv.symm (n2 [_, _] rfl)
    | lam cell =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv
      exact absurd hv.symm (n3 [_, _, _] rfl)
    | forallE cell =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv
      exact absurd hv.symm (n4 [_, _, _] rfl)
    | letE cell =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv
      exact absurd hv.symm (n5 [_, _, _] rfl)
    | proj cell =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv
      exact absurd hv.symm (n6 [_, _, _] rfl)
termination_by cs.length
decreasing_by
  all_goals
    simp only [hc, List.length_cons, List.length_append]
    omega

end IxVM.Refinement.Decl
