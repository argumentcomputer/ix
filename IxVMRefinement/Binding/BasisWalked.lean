import IxVMRefinement.Binding.FoldFamily
import IxVMRefinement.Binding.RunPredicate

/-! # The family form at the six basis groups

The binding fold starts below group 6 at the store `Rs 6`, which has the entries of the 24
committed basis rows (the five one-inductive blocks of `Eq`, `Nat`, `PUnit`, `Empty`, `False` with
their members' records, and the quotient package), and at the environment of the kernel's pins
(`bndOver_basis_at`). Its family form asks two more facts there:

* `walkedStored_basis`: **the walked records stored.** Every basis row that is no block is at the
  key of a pinned basis role (`StoreInhabit.keys_pinned`, decided over the rows), which a table
  that pins the prelude binds there too (`keyOf_basis'`), and the environment of the pins stores
  every basis role (`StoreInhabit.basisEnv_find`); the walked roles of the basis groups are basis
  roles (`StoreInhabit.groupRole_basis`).
* `storedFamilies_basis`: **the empty family map**, since no basis block routes as modeled
  (`blockRoute_basisStore_ne_true`). Each basis block references nothing outside itself and has
  at most one inductive member (`basisRows_blocksClosed`, decided over the rows). The route of a
  block with one inductive member is the scan of its constructors' types for a nested occurrence
  (`Route.oneRoute`), and the scan reports one only at an application headed by a constant that
  is no member of the block; the trees of a block that references nothing are built from its
  members alone (`exprTree_leaves`), so the scan reports none (`nestedN_ne_true`).
* `basisOverW_of_run`, `basisOverW_bindingRun`: the basis hypothesis of the fold's family form,
  `BasisOverW`, for every run whose table pins the prelude and whose store after the basis groups
  has the basis rows' entries, the binding run predicate among them. The facts are lifted from the
  basis store to `Rs 6` through the run's agreement with the basis rows' entries.

The empty map selects nothing, so every predicate of the selected records (a stored-form
predicate among them) holds of it.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Route
open IxVM.Refinement.TableInhabit (basisEnv basisRoleOrder)
open IxVM.Refinement.StoreInhabit (basisStore basisRows)
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)

/-! ## The route of a block that references nothing outside itself -/

theorem orElse_ne_true : ∀ {x y : Option Bool}, x ≠ some true → y ≠ some true →
    orElse x y ≠ some true
  | none, _, _, _ => fun h => nomatch h
  | some true, _, hx, _ => absurd rfl hx
  | some false, _, _, hy => hy

theorem foldr_orElse_ne_true : ∀ (l : List (Option Bool)), (∀ x ∈ l, x ≠ some true) →
    l.foldr orElse (some false) ≠ some true
  | [], _ => fun h => nomatch h
  | x :: l, h => orElse_ne_true (h x List.mem_cons_self)
      (foldr_orElse_ne_true l fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem hereOf_ne_true {isInd : _root_.Address → Option Bool} {M : List _root_.Address}
    {H : ScanTree} {m : Bool} {w : Option Bool}
    (hH : ∀ a, H.constAddr? = some a → a ∈ M) (hw : w ≠ some true) :
    hereOf isInd M H m w ≠ some true := by
  unfold hereOf
  cases hc : H.constAddr? with
  | none => exact hw
  | some a =>
    show hereConst isInd a (memB M a) m ≠ some true
    rw [memB_pos (hH a hc)]
    exact fun h => nomatch h

/-- **The nested-occurrence scan reports none on a tree whose constants are all members.** -/
theorem nestedN_ne_true {isInd : _root_.Address → Option Bool} {M : List _root_.Address} :
    ∀ (n : Nat) (T : ScanTree), (∀ a, leafIn a T → a ∈ M) → nestedN isInd M n T ≠ some true
  | 0, _, _ => fun h => nomatch h
  | _ + 1, .atom, _ => fun h => nomatch h
  | _ + 1, .const _, _ => fun h => nomatch h
  | n + 1, .lam t b, hT =>
    orElse_ne_true (nestedN_ne_true n t fun a ha => hT a (Or.inl ha))
      (nestedN_ne_true n b fun a ha => hT a (Or.inr ha))
  | n + 1, .all t b, hT =>
    orElse_ne_true (nestedN_ne_true n t fun a ha => hT a (Or.inl ha))
      (nestedN_ne_true n b fun a ha => hT a (Or.inr ha))
  | n + 1, .letE t v b, hT =>
    orElse_ne_true (nestedN_ne_true n t fun a ha => hT a (Or.inl ha))
      (orElse_ne_true (nestedN_ne_true n v fun a ha => hT a (Or.inr (Or.inl ha)))
        (nestedN_ne_true n b fun a ha => hT a (Or.inr (Or.inr ha))))
  | n + 1, .proj x, hT => nestedN_ne_true n x hT
  | n + 1, .app f x, hT =>
    orElse_ne_true
      (hereOf_ne_true (fun a hc => hT a (leafIn_head (leafIn_constAddr hc)))
        (nestedN_ne_true n _ fun a ha => hT a (leafIn_head ha)))
      (foldr_orElse_ne_true _ fun y hy => by
        obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hy
        exact nestedN_ne_true n A fun a ha => hT a (leafIn_args hA ha))

theorem exprTree?_spec {refs M : List _root_.Address} {sharing : List Ixon.Expr}
    {e : Ixon.Expr} {T : ScanTree} (h : exprTree? refs M sharing e = some T) :
    ExprTree refs M sharing 4294967295 e T := by
  by_cases hex : ∃ T, ExprTree refs M sharing 4294967295 e T
  · unfold exprTree? at h
    rw [dite_eq_left hex] at h
    exact (Option.some.inj h) ▸ Classical.choose_spec hex
  · unfold exprTree? at h
    rw [dite_eq_right hex] at h
    cases h

/-- **A constructor of a block that references nothing reports no nested occurrence.** -/
theorem ctorAnswer_ne_true {isInd : _root_.Address → Option Bool} {M : List _root_.Address}
    {sharing : List Ixon.Expr} {ct : Ixon.Constructor} :
    ctorAnswer isInd M [] sharing ct ≠ some true := by
  unfold ctorAnswer
  split
  · exact fun h => nomatch h
  · next T hT =>
    have hleaf : ∀ a, leafIn a T → a ∈ M := by
      intro a ha
      rcases exprTree_leaves (exprTree?_spec hT) a ha with ⟨i, hi, -⟩ | hm
      · simp at hi
      · exact hm
    split
    · exact fun h => nomatch h
    · next Bd hp =>
      unfold ctorBody
      split
      · exact nestedN_ne_true _ Bd fun a ha => hleaf a (leafIn_peel hp ha)
      · exact fun h => nomatch h

theorem oneRoute_ne_true {E : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hrefs : cb.refs.toList = []) : oneRoute E B cb ms ≠ some true := by
  unfold oneRoute
  split
  · rw [hrefs]
    exact foldr_orElse_ne_true _ fun y hy => by
      obtain ⟨ct, -, rfl⟩ := List.mem_map.mp hy
      exact ctorAnswer_ne_true
  · exact fun h => nomatch h

theorem mutsRoute_ne_true {E : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hrefs : cb.refs.toList = [])
    (hone : (ms.toList.filter Core.Specs.Callees.isIndc).length ≤ 1) :
    mutsRoute E B cb ms ≠ some true := by
  unfold mutsRoute
  split
  · exact fun h => nomatch h
  · exact oneRoute_ne_true hrefs
  · omega

/-! ## The basis rows -/

/-- **A record that, if a block, references nothing and has at most one inductive member.** -/
def basisBlockClosed (c : Ixon.Constant) : Bool :=
  match c.info with
  | .muts ms =>
    decide (c.refs.toList = [] ∧ (ms.toList.filter Core.Specs.Callees.isIndc).length ≤ 1)
  | _ => true

set_option maxRecDepth 100000 in
/-- **Every basis block references nothing and has one inductive member** (decided over the
rows). -/
theorem basisRows_blocksClosed : basisRows.all (fun e => basisBlockClosed e.2) = true := by
  decide +kernel

/-- **No block of the basis store routes as modeled.** -/
theorem blockRoute_basisStore_ne_true (B : _root_.Address) :
    blockRoute basisStore B ≠ some true := by
  unfold blockRoute
  cases hB : recordOf basisStore B with
  | none => exact fun h => nomatch h
  | some cb =>
    show recordRoute basisStore B cb ≠ some true
    have hok : basisBlockClosed cb = true :=
      List.all_eq_true.mp basisRows_blocksClosed (B, cb) (StoreInhabit.store_record_inv hB)
    unfold recordRoute
    cases hi : cb.info with
    | muts ms =>
      have hok' : decide (cb.refs.toList = [] ∧
          (ms.toList.filter Core.Specs.Callees.isIndc).length ≤ 1) = true := by
        unfold basisBlockClosed at hok
        rw [hi] at hok
        exact hok
      obtain ⟨hrefs, hone⟩ := of_decide_eq_true hok'
      exact mutsRoute_ne_true hrefs hone
    | defn _ => exact fun h => nomatch h
    | axio _ => exact fun h => nomatch h
    | quot _ => exact fun h => nomatch h
    | recr _ => exact fun h => nomatch h
    | dPrj _ => exact fun h => nomatch h
    | iPrj _ => exact fun h => nomatch h
    | cPrj _ => exact fun h => nomatch h
    | rPrj _ => exact fun h => nomatch h

/-! ## The two facts at the basis -/

/-- **The walked records stored at the basis** (module docstring), at every store with the basis
rows' entries. -/
theorem walkedStored_basis {ρ : BRun} {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    (ht : t.check = .ok ()) (hpre : PreludePinned t)
    (hc : ∀ a, basisStore.consts.get? a = R.consts.get? a) :
    WalkedStored ρ t (· < 6) R basisEnv := by
  refine ⟨fun x c n hx hnb hlog hlogB hchk => ?_, fun r x hw hgr ha => ?_⟩
  · rw [← recordOf_storeCongr hc] at hx
    have hF : (StoreInhabit.isMutsInfo c.info || StoreInhabit.isBasisKey (keyOf ctab x)) = true :=
      List.all_eq_true.mp StoreInhabit.keys_pinned (x, c) (StoreInhabit.store_record_inv hx)
    have hnm : StoreInhabit.isMutsInfo c.info = false := by
      cases hi : c.info with
      | muts ms => exact absurd hi (hnb ms)
      | defn _ => rfl
      | axio _ => rfl
      | quot _ => rfl
      | recr _ => rfl
      | dPrj _ => rfl
      | iPrj _ => rfl
      | cPrj _ => rfl
      | rPrj _ => rfl
    rw [hnm, Bool.false_or] at hF
    obtain ⟨r, hrole, hkey⟩ := StoreInhabit.isBasisKey_role hF
    obtain ⟨ci, hfind, -⟩ := StoreInhabit.basisEnv_find hrole
    rw [(keyOf_basis' ht hpre hrole).mpr hkey]
    exact Option.isSome_iff_exists.mpr ⟨ci, hfind⟩
  · have hkey : keyOf t x = Ix.Kernel.Key.role r := Core.keyOf_of_addressOf (wf_of_check ht) ha
    obtain ⟨ci, hfind, -⟩ :=
      StoreInhabit.basisEnv_find (StoreInhabit.groupRole_basis hgr (role_mem_roleGroup r))
    rw [hkey]
    exact Option.isSome_iff_exists.mpr ⟨ci, hfind⟩

/-- **The empty family map is stored** at a store none of whose blocks routes as modeled. -/
theorem storedFamilies_basis {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {env : Ix.Kernel.Env .anon} (hroute : ∀ B, blockRoute R B ≠ some true) :
    StoredFamilies t R env (fun _ => none) where
  selected := fun B cb hB hr hst => absurd hr (hroute B)
  family := fun B rb h => nomatch h
  blockStored := fun B rb cb h => nomatch h
  installed := fun B rb crb h => nomatch h

/-! ## The basis hypothesis -/

/-- **The basis hypothesis of the family form** for every run whose table pins the prelude and
whose store after the basis groups has the basis rows' entries. -/
theorem basisOverW_of_run (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    (hrun : ∀ t ρ Rs, Run t ρ Rs → PreludePinned t ∧
      (∀ a, (Rs 6).consts.get? a = basisStore.consts.get? a) ∧
      ∀ a, (Rs 6).blobs.get? a = basisStore.blobs.get? a) :
    BasisOverW.{u} L Run := by
  intro t ρ Rs hr hall ht
  obtain ⟨hpre, hc, hb⟩ := hrun t ρ Rs hr
  have hc' : ∀ a, basisStore.consts.get? a = (Rs 6).consts.get? a := fun a => (hc a).symm
  have hb' : ∀ a, basisStore.blobs.get? a = (Rs 6).blobs.get? a := fun a => (hb a).symm
  refine ⟨basisEnv, bndOver_storeCongr hc' hb' (bndOver_basis_at L ht hpre hall),
    walkedStored_basis ht hpre hc', fun _ => none, storedFamilies_basis fun B => ?_⟩
  rw [blockRoute_storeCongr hc' B]
  exact blockRoute_basisStore_ne_true B

/-- **The basis hypothesis of the family form, for a binding run.** -/
theorem basisOverW_bindingRun (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (calls : List (Call F)) : BasisOverW.{u} L (BindingRun calls) :=
  basisOverW_of_run L fun _ _ _ h => ⟨h.preludePinned, h.basisConsts, h.basisBlobs⟩

end IxVM.Refinement.Binding
