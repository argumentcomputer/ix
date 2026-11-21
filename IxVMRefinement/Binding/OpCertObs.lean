import IxVMRefinement.Binding.CertStatement
import IxVMRefinement.Binding.OpRoleUnitW
import IxVMRefinement.Claim.RefSafetyExcept

/-! # The certificates an operation's validation checks

At a well-founded operation every entry of the evidence list is `Proof(thm)`, and the entry at
index `k` checks the `k`-th certificate statement (`KernelRoles.lean:1033-1077`): the theorem's
value, the operation replaced by its value and scope-checked closed and level-free, is applied to
the statement's variables and checked against the statement's equation (`k_check`). This file
reads that check at the keying of the closure's environment (`OpRefine.CertObs`).

* `RawConvExpr.projIn_prj`: the structure of a `Proj` cell of a converted expression is at a
  projection's structure index (`prjIdxs`).
* `walk_refs_except_notBlock`: the record at every reference a certificate uses, other than the
  operation's address, is no block (`walk_refs_except`'s `assert_not_block_ref`).
* `certObs_of_seg`, `certObs_of_evidence`: one certificate from the entry at its index; every
  certificate from the walk of the evidence list.
* `CertProjFree`: the substitution of the operation's value into a certificate's proof meets no
  projection of the operation (the one premise left). `certProjFree_of_inventory`: it follows
  from the same inequality at every projection index of the record's value and sharing table.
  `certProjFree_of_subst`: it follows from every successful `subst_const` reaching no
  projection at the address it replaces.
* `opCertFacts_of_projFree`: `OpCertFacts` from it; `operationRoleUnitW_of_projFree`.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Ingress

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.Core (ProjIn)

/-- **The structure indices of an expression's projections.** -/
def prjIdxs : Ixon.Expr → List Nat
  | .prj i _ e => i.toNat :: prjIdxs e
  | .app f a => prjIdxs f ++ prjIdxs a
  | .lam t b => prjIdxs t ++ prjIdxs b
  | .all t b => prjIdxs t ++ prjIdxs b
  | .letE _ _ t v b => prjIdxs t ++ prjIdxs v ++ prjIdxs b
  | _ => []

/-- **`x` is at a projection's structure index** of the expression or of a shared
subexpression. -/
def PrjUsed (refs : List _root_.Address) (sharing : List Ixon.Expr) (e : Ixon.Expr)
    (x : _root_.Address) : Prop :=
  ∃ i, (i ∈ prjIdxs e ∨ ∃ s ∈ sharing, i ∈ prjIdxs s) ∧ refs[i]? = some x

private theorem cert_cell_args {h : Heap F} {addr : Nat} {e n n' : String}
    {xs ys : List (SourceValue F)}
    (c₁ : h[addr]? = some (.construct e n xs)) (c₂ : h[addr]? = some (.construct e n' ys)) :
    n = n' ∧ xs = ys := by
  have := Option.some.inj (c₁.symm.trans c₂)
  injection this with _ hn hx
  exact ⟨hn, hx⟩

private theorem PrjUsed.lift {refs : List _root_.Address} {sharing : List Ixon.Expr}
    {e e' : Ixon.Expr} {x : _root_.Address}
    (hsub : ∀ i, i ∈ prjIdxs e → i ∈ prjIdxs e')
    (h : PrjUsed refs sharing e x) : PrjUsed refs sharing e' x := by
  obtain ⟨i, hi | hs, hr⟩ := h
  · exact ⟨i, Or.inl (hsub i hi), hr⟩
  · exact ⟨i, Or.inr hs, hr⟩

/-- **The structure of a `Proj` cell of a converted expression is at a projection's structure
index.** -/
theorem RawConvExpr.projIn_prj {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)} {h : Heap F}
    {bound : Nat} {e : Ixon.Expr} {p : SourceValue F}
    (raw : RawConvExpr refs recurAddrs univs sharing blobs h bound e p) :
    ∀ a : Bytes.Address, ProjIn h p a → PrjUsed refs sharing e (Core.ixAddr a) := by
  induction raw with
  | var hidx cell =>
    intro a hin
    cases hin with
    | _ => rename_i c' _; exact absurd (cert_cell_args cell c').1 (by decide)
  | sort huIdx hu rl cell =>
    intro a hin
    cases hin with
    | _ => rename_i c' _; exact absurd (cert_cell_args cell c').1 (by decide)
  | @ref bound addr rIdx uIdxs x d ap lsp ls hrIdx href hd ra hls rls cell =>
    intro a hin
    cases hin with
    | _ => rename_i c' _; exact absurd (cert_cell_args cell c').1 (by decide)
  | @recur bound addr rIdx uIdxs x d ap lsp ls hrIdx hrec hd ra hls rls cell =>
    intro a hin
    cases hin with
    | _ => rename_i c' _; exact absurd (cert_cell_args cell c').1 (by decide)
  | @prj bound addr tIdx fIdx inner x d ap ip htIdx hfIdx href hd ra rin cell ih =>
    intro a hin
    cases hin with
    | head c' ra' =>
      obtain ⟨-, hargs⟩ := cert_cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at ra'
      have hda : d = a := Bytes.repAddressRef_inj U32.Goldilocks.compatible ra ra'
      refine ⟨tIdx.toNat, Or.inl (List.mem_cons.mpr (Or.inl rfl)), ?_⟩
      rw [← hda, hd]
      exact href
    | projArg c' sub =>
      obtain ⟨-, hargs⟩ := cert_cell_args cell c'
      injection hargs with _ hrest
      injection hrest with _ hrest'
      injection hrest' with h3 _
      rw [← h3] at sub
      exact (ih a sub).lift fun i hi => List.mem_cons_of_mem _ hi
    | _ => rename_i c' _; exact absurd (cert_cell_args cell c').1 (by decide)
  | str hbIdx href hmem rbs hs cell =>
    intro a hin
    cases hin with
    | _ => rename_i c' _; exact absurd (cert_cell_args cell c').1 (by decide)
  | nat hbIdx href hmem hcanon rlimbs hlast hval cell =>
    intro a hin
    cases hin with
    | _ => rename_i c' _; exact absurd (cert_cell_args cell c').1 (by decide)
  | app rf ra cell ihf iha =>
    intro a hin
    cases hin with
    | appFn c' sub =>
      obtain ⟨-, hargs⟩ := cert_cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at sub
      exact (ihf a sub).lift fun i hi => List.mem_append_left _ hi
    | appArg c' sub =>
      obtain ⟨-, hargs⟩ := cert_cell_args cell c'
      injection hargs with _ hrest
      injection hrest with h2 _
      rw [← h2] at sub
      exact (iha a sub).lift fun i hi => List.mem_append_right _ hi
    | _ => rename_i c' _; exact absurd (cert_cell_args cell c').1 (by decide)
  | lam rl rt rb cell iht ihb =>
    intro a hin
    cases hin with
    | lamTy c' sub =>
      obtain ⟨-, hargs⟩ := cert_cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at sub
      exact (iht a sub).lift fun i hi => List.mem_append_left _ hi
    | lamBody c' sub =>
      obtain ⟨-, hargs⟩ := cert_cell_args cell c'
      injection hargs with _ hrest
      injection hrest with h2 _
      rw [← h2] at sub
      exact (ihb a sub).lift fun i hi => List.mem_append_right _ hi
    | _ => rename_i c' _; exact absurd (cert_cell_args cell c').1 (by decide)
  | all rl rt rb cell iht ihb =>
    intro a hin
    cases hin with
    | forallTy c' sub =>
      obtain ⟨-, hargs⟩ := cert_cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at sub
      exact (iht a sub).lift fun i hi => List.mem_append_left _ hi
    | forallBody c' sub =>
      obtain ⟨-, hargs⟩ := cert_cell_args cell c'
      injection hargs with _ hrest
      injection hrest with h2 _
      rw [← h2] at sub
      exact (ihb a sub).lift fun i hi => List.mem_append_right _ hi
    | _ => rename_i c' _; exact absurd (cert_cell_args cell c').1 (by decide)
  | letE rt rv rb cell iht ihv ihb =>
    intro a hin
    cases hin with
    | letTy c' sub =>
      obtain ⟨-, hargs⟩ := cert_cell_args cell c'
      injection hargs with h1 _
      rw [← h1] at sub
      exact (iht a sub).lift fun i hi =>
        List.mem_append_left _ (List.mem_append_left _ hi)
    | letVal c' sub =>
      obtain ⟨-, hargs⟩ := cert_cell_args cell c'
      injection hargs with _ hrest
      injection hrest with h2 _
      rw [← h2] at sub
      exact (ihv a sub).lift fun i hi =>
        List.mem_append_left _ (List.mem_append_right _ hi)
    | letBody c' sub =>
      obtain ⟨-, hargs⟩ := cert_cell_args cell c'
      injection hargs with _ hrest
      injection hrest with _ hrest'
      injection hrest' with h3 _
      rw [← h3] at sub
      exact (ihb a sub).lift fun i hi => List.mem_append_right _ hi
    | _ => rename_i c' _; exact absurd (cert_cell_args cell c').1 (by decide)
  | @share bound idx s kp hidx hsh rs ih =>
    intro a hin
    obtain ⟨i, hi | hs, hr⟩ := ih a hin
    · exact ⟨i, Or.inr ⟨s, List.mem_of_getElem? hsh, hi⟩, hr⟩
    · exact ⟨i, Or.inr hs, hr⟩

end IxVM.Refinement.Ingress

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Role Expr)
open Ix.Kernel.Semantics (NativeFam)

/-! ## The walk of a certificate's references: no block -/

/-- `KernelRoles::walk_covered` on a validating context answers `0`. -/
private theorem walk_covered_mk' {t : Ix.Kernel.RoleTable} {n : Nat}
    {x_rc x_a r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCRep t (some n) h x_rc)
    (ev : ObsFn W "KernelRoles::walk_covered" [x_rc, x_a] h r h' calls) :
    r = .field 0 ∧ h' = h := by
  obtain ⟨tbl, ax, node, hl, hnode, _⟩ := hrc
  rcases hnode with ⟨n', _, _, rfl⟩ | ⟨hnone, _⟩
  · match Obs.«KernelRoles::walk_covered».obs ev with
    | .Mk (he38 := hr) (he39 := hh) .. => exact ⟨hr, hh⟩
    | .Assumed_n0 (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
    | .Assumed_other (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
  · cases hnone

/-- `1 - [b = a]` and a field `x` multiply to `1` only when `x = 1` and `b ≠ a`. -/
private theorem except_guard' {x y y' v : SourceValue F} {p : Prop} [Decidable p]
    (hy : y = .field (if p then 1 else 0))
    (op1 : evalBinOp .sub (.field 1) y = .ok y')
    (op2 : evalBinOp .mul x y' = .ok v)
    (hx : x = .field 1) (hp : ¬ p) : v = .field 1 := by
  subst hy hx
  simp only [hp, ↓reduceIte] at op1
  simp only [evalBinOp, Except.ok.injEq] at op1
  subst op1
  simp only [evalBinOp, Except.ok.injEq] at op2
  rw [← op2]
  simp

/-- **`KernelRoles::walk_refs_except(rc, refs, used, i, a)`** under a validating context: the
record at every reference `refs[j]` used at index `i + j`, other than `a`, is no block
(`assert_not_block_ref`). -/
theorem walk_refs_except_notBlock {t : Ix.Kernel.RoleTable} {n : Nat} {a : _root_.Address}
    {idxs : List Nat} :
    ∀ (refs : List _root_.Address) {i : Nat} {x_rc x_refs x_used x_a r : SourceValue F}
      {h h' : Heap F} {calls : List (Call F)},
      i + refs.length < 8589934592 →
      RCRep t (some n) h x_rc →
      RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem h refs x_refs →
      Claim.RepSortedIdxFrom h idxs i x_used →
      BaseSeams.addr h x_a a →
      ObsFn W "KernelRoles::walk_refs_except" [x_rc, x_refs, x_used, .field (i : F), x_a]
        h r h' calls →
      Heap.Extends h h' ∧
      ∀ j : Nat, (hj : j < refs.length) → i + j ∈ idxs → refs[j] ≠ a →
        Claim.NotBlockIn calls refs[j]
  | [], i, x_rc, x_refs, x_used, x_a, r, h, h', calls, _, _, hrefs, _, _, ev => by
    cases Obs.«KernelRoles::walk_refs_except».obs ev with
    | Nil _ _ he23 _ =>
      subst he23
      exact ⟨Heap.Extends.refl _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | Cons _ _ _ _ _ _ _ _ _ _ _ ld12 _ _ _ _ _ =>
      obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load hrefs ld12
      cases hbad
  | b :: rest, i, x_rc, x_refs, x_used, x_a, r, h, h', calls, hbound, hrc, hrefs, hidxs, ha, ev => by
    cases Obs.«KernelRoles::walk_refs_except».obs ev with
    | Nil ld12 _ _ _ => cases Lib.rep_nil_of_load hrefs ld12
    | Cons x_b x_rest m_pop cs_pop x_hit x_next_used v264 m265 cs267 cs276 v282
        ld12 ev_pop sg272 op318 ev278 hc327 =>
      obtain ⟨b', rest', heq, hb_rep, hrest_rep⟩ := Lib.rep_cons_of_load hrefs ld12
      injection heq with hb hrs
      subst hb hrs
      have hi : i < 72057594037927936 := by simp at hbound; omega
      obtain ⟨rfl, hiff, hidxs_next⟩ := Claim.sorted_pop_spec idxs hi hidxs ev_pop
      obtain ⟨b₀, hb₀, hbix⟩ := id hb_rep
      obtain ⟨a₀, ha₀, haix⟩ := id ha
      have hseg : Heap.Extends h m265 ∧ (i ∈ idxs → b ≠ a → Claim.NotBlockIn cs267 b) := by
        cases sg272 with
        | n1_n0 m43 y52 y82 cs92 v115 m116 cs126 m146 cs157 v180 m181 cs191
            cs205 v208 m211 cs219 ev94 _ _ ev128 ev159 ev193 ev221 ev207 hc245 =>
          obtain ⟨_, hh43⟩ := Lib.address_eq_spec ev94 hb₀ ha₀
          have hh43' : h = m43 := hh43.symm
          subst hh43'
          have e1 : Heap.Extends h m146 := ev128.heap_extends.trans ev159.heap_extends
          obtain ⟨e2, hnb⟩ := Claim.assert_not_block_ref_notBlock (BaseSeams.addr_mono e1 hb_rep) ev193
          exact ⟨e1.trans (e2.trans (ev221.heap_extends.trans ev207.heap_extends)),
            fun _ _ => hnb.mono (fun cl hm => by rw [hc245]; simp [hm])⟩
        | n1_other m43 y52 y82 cs92 v115 m116 cs126 v145 m146 cs157
            ev94 _ _ ev128 ev159 hne246 _ _ _ =>
          obtain ⟨_, hh43⟩ := Lib.address_eq_spec ev94 hb₀ ha₀
          have hh43' : h = m43 := hh43.symm
          subst hh43'
          obtain ⟨hv, _⟩ := walk_covered_mk' (hrc.mono ev128.heap_extends) ev159
          exact absurd hv hne246
        | other v42 m43 y52 y82 cs92 ev94 op88 op58 hne255 _ he262 _ =>
          obtain ⟨hy, hh43⟩ := Lib.address_eq_spec ev94 hb₀ ha₀
          have hh43' : h = m43 := hh43.symm
          subst hh43'
          refine ⟨by rw [he262], fun hin hne => ?_⟩
          exfalso
          have hba : ¬ b₀ = a₀ := fun e => hne (by rw [← hbix, ← haix, e])
          exact hne255 (except_guard' hy op88 op58 (hiff.mpr hin) hba)
      obtain ⟨ext1, hhead⟩ := hseg
      simp only [evalBinOp, Except.ok.injEq] at op318
      subst op318
      have hv_inc : ((i : F) + 1) = ((i + 1 : Nat) : F) := by push_cast; rfl
      rw [hv_inc] at ev278
      have hbound' : (i + 1) + rest.length < 8589934592 := by simp at hbound; omega
      obtain ⟨ext2, htail⟩ :=
        walk_refs_except_notBlock rest hbound' (hrc.mono ext1)
          (repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ ext1 hrest_rep)
          (hidxs_next.mono ext1)
          (BaseSeams.addr_mono ext1 ha) ev278
      have hsub1 : ∀ cl ∈ cs267, cl ∈ calls := fun cl hm => by rw [hc327]; simp [hm]
      have hsub2 : ∀ cl ∈ cs276, cl ∈ calls := fun cl hm => by rw [hc327]; simp [hm]
      refine ⟨ext1.trans ext2, fun j hj hij hne => ?_⟩
      cases j with
      | zero =>
        have hr := (hhead (by simpa using hij) (by simpa using hne)).mono hsub1
        simpa using hr
      | succ j' =>
        have hj' : j' < rest.length := by simpa using hj
        have hr := (htail j' hj'
          (by rw [show i + 1 + j' = i + (j' + 1) by omega]; exact hij) (by simpa using hne)).mono
          hsub2
        simpa using hr

/-! ## One certificate -/

private theorem claimInfo_defn' {h : Heap F} {info : Ixon.ConstantInfo} {dv : SourceValue F}
    (hinfo : Claim.RepConstantInfo h info (.construct "Ixon::ConstantInfo" "Defn" [dv])) :
    ∃ d : Ixon.Definition, info = .defn d := by
  cases info with
  | defn d => exact ⟨d, rfl⟩
  | recr _ | axio _ | quot _ | cPrj _ | rPrj _ | iPrj _ | dPrj _ | muts _ =>
    obtain ⟨_, hmk, _⟩ := hinfo
    simp at hmk

private theorem refs_size_lt_bound_cert {rawBytes : ByteArray} {c : Ixon.Constant}
    (hsz : rawBytes.size < 4294967296)
    (hdeExact : Ixon.deConstantExact rawBytes = .ok c) :
    c.refs.size < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound rawBytes c hdeExact
  have hrefs : c.refs.size ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  omega

/-- **The references a certificate's proof uses are stored**, other than the operation's at `b`,
once the walk found their records to be no block. -/
def CertRefsStoredAt (calls : List (Call F)) (t : Ix.Kernel.RoleTable)
    (env : Ix.Kernel.Env .anon) (b : Bytes.Address) (thm : _root_.Address) : Prop :=
  ∀ (rawBytes : ByteArray) (c : Ixon.Constant), Hashed calls rawBytes →
    rawBytes.size < 4294967296 → Address.blake3Pure rawBytes = thm →
    Ixon.deConstantExact rawBytes = .ok c →
    ∀ i ∈ IxVM.Consistency.usedRefIdxs c, ∀ x : Bytes.Address,
      c.refs.toList[i]? = some (ixAddr x) → x ≠ b → Claim.NotBlockIn calls (ixAddr x) →
      ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci

/-- **The substitution into the certificate's proof meets no projection at the operation's
address `b`**: a call of `KernelSubst::subst_const` in the run, on a conversion `p` of the
certificate's value with the operation's address as its second argument, reaches (`ProjIn`, at
the call's output heap) no projection whose structure is at `b`. -/
def CertProjFreeAt (calls : List (Call F)) (b : Bytes.Address) (thm : _root_.Address) : Prop :=
  ∀ (rawBytes : ByteArray) (c : Ixon.Constant), Hashed calls rawBytes →
    rawBytes.size < 4294967296 → Address.blake3Pure rawBytes = thm →
    Ixon.deConstantExact rawBytes = .ok c →
    ∀ d : Ixon.Definition, c.info = .defn d →
    ∀ (recurAddrs : List _root_.Address) (univs : List Ixon.Univ)
      (blobs : List (_root_.Address × ByteArray)) (bound : Nat) (h : Heap F) (p : SourceValue F),
      Ingress.RawConvExpr c.refs.toList recurAddrs univs c.sharing.toList blobs h bound d.value p →
    ∀ (x_a x_v res : SourceValue F) (h' : Heap F) (cs : List (Call F)),
      (⟨"KernelSubst::subst_const", [p, x_a, x_v], h⟩ : Call F) ∈ calls →
      ObsFn W "KernelSubst::subst_const" [p, x_a, x_v] h res h' cs →
      Bytes.RepAddressRef addrTy h b x_a →
    ∀ x : Bytes.Address, ProjIn h' p x → x ≠ b

set_option maxHeartbeats 6400000 in
/-- **One certificate, from the check `validate_op_equations` makes at its index**: at a
well-founded operation, the entry at index `k` of the evidence checks the `k`-th certificate
statement (`OpRefine.CertObs`) with a proof term closed, with no `let` and no level parameter,
at the keying of the closure's environment `env`. Besides the premises of `certStmt_open`: the
certificate's used references stored (`CertRefsStoredAt`) and the substitution into its proof
meeting no projection at the operation's address (`CertProjFreeAt`). -/
theorem certObs_of_seg {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ()) {r : Role}
    (hmem : (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natDivModNames)
    (hp1 : RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_evidence_is_proof.body)
      (roleNum r) = some 1)
    {calls : List (Call F)} {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {Ec : Ixon.Env} {env : Ix.Kernel.Env .anon} {lim : Nat} {val : KExpr}
    {x_rc x_tbl x_a x_val : SourceValue F} {b : Bytes.Address} {h₀ : Heap F}
    (hrc : RCRep t (some lim) h₀ x_rc) (htbl : TableRep t h₀ x_tbl)
    (hb : Bytes.RepAddressRef addrTy h₀ b x_a) (hkb : keyOf t (ixAddr b) = .role r)
    (hv : Decl.TmCExact (keyOf t) h₀ val x_val)
    (hvcells : ∀ h₂, Heap.Extends h₀ h₂ → ∀ x, AddrIn h₂ x_val x →
      ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci)
    (hnamed : ∀ x : Bytes.Address, certNamedOk r (keyOf t (ixAddr x)) = true → x ≠ b →
      ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci)
    {ev0 : Ix.Kernel.Evidence _root_.Address}
    (hcert : ∀ thm : _root_.Address, ev0 = .proof thm → CertRefsStoredAt calls t env b thm)
    (hnoproj : ∀ thm : _root_.Address, ev0 = .proof thm → CertProjFreeAt calls b thm)
    {e rest x_ev : SourceValue F} {k : Nat} {h : Heap F} {res : SourceValue F} {h' : Heap F}
    {cs : List (Call F)} (ext0 : Heap.Extends h₀ h) (he : EvRep h ev0 e)
    (sg : Obs.«KernelRoles::validate_op_equations».Seg1 e rest x_rc x_tbl (.field (roleNum r))
      x_a x_val x_ev (.field ((k : Nat) : F)) h res h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) (hgood : Good ⟨Ec, env, t, none⟩ cs) :
    ∀ st, (Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey))[k]? = some st →
      ∃ P : KExpr, P.looseBVarsBounded 0 = true ∧ P.hasFvar = false ∧
        Decl.noLetExpr P = true ∧ P.allLevelParamsDefined [] = true ∧
        OpRefine.CertObs Ec t lim env (.role r) val st P := by
  intro st hget
  have htwf : t.wf = true := wf_of_check ht
  let cx : Ctx := ⟨Ec, env, t, some lim⟩
  have hinj : ∀ b', keyOf t (ixAddr b') = keyOf t (ixAddr b) → b' = b :=
    fun b' hk => Decl.ixAddr_injective (Decl.keyOf_injective htwf hk)
  match sg with
  | .n0_Defeq (ev56 := ev56) .. =>
    exact (zero_ne_one (Value.field.inj (op_evidence_is_proof_val hp1 ev56).1)).elim
  | .n0_Proof (ev56 := ev56) .. =>
    exact (zero_ne_one (Value.field.inj (op_evidence_is_proof_val hp1 ev56).1)).elim
  | .other_Defeq (heq431 := hbad) .. => exact (zero_ne_one (Value.field.inj hbad)).elim
  | .other_Proof_Defn_other (heq1257 := hbad) .. =>
    exact (zero_ne_one (Value.field.inj hbad)).elim
  | .other_Proof_other (heq1904 := hbad) .. => exact (zero_ne_one (Value.field.inj hbad)).elim
  | .other_Proof_Defn_Theorem (x_thm := xthm) (w496 := w496) (x_nlvls := xnl) (w646 := w646)
      (x_pval := xpval) (m615 := m615) (v689 := v689) (m690 := m690) (v808 := v808)
      (m831 := m831)
      (v876 := v876) (m877 := m877) (x_eqn := xeqn)
      (x_types := xtypes) (v1123 := v1123) (m1124 := m1124) (v1152 := v1152) (m1163 := m1163)
      (v1175 := v1175) (cs629 := cs629) (cs460 := cs460) (cs887 := cs887) (cs1148 := cs1148)
      (ev56 := ev56) (hv442 := hv442) (ev462 := ev462) (ev631 := ev631) (ld625 := ld625)
      (ev702 := ev702) (ev740 := ev740) (ev821 := ev821) (ev843 := ev843) (ev889 := ev889)
      (ev960 := ev960) (ev980 := ev980) (ev934 := ev934) (ev1058 := ev1058)
      (ev1043 := ev1043) (hm1106 := hm1106) (ev1029 := ev1029) (ev1136 := ev1136)
      (ev1194 := ev1194) (ev1173 := ev1173) (ev1150 := ev1150) (hc1225 := hc) .. =>
    obtain ⟨-, hm43⟩ := op_evidence_is_proof_val hp1 ev56
    have hm43' := hm43.symm
    subst hm43'
    -- the certificate's address
    obtain ⟨thmB, hev0, hthB⟩ : ∃ thm : Bytes.Address, ev0 = .proof (ixAddr thm) ∧
        Bytes.RepAddressRef addrTy h thm xthm := by
      rcases he with ⟨_, hvd⟩ | ⟨a', p, hprf, hvp, hap⟩
      · rw [hv442] at hvd
        injection hvd with _ hc' _
        exact absurd hc' (by decide)
      · rw [hv442] at hvp
        injection hvp with _ _ hps
        injection hps with hps
        subst hps
        exact ⟨a', hprf, hap⟩
    have e462 := ev462.heap_extends
    have e631 := ev631.heap_extends
    have e702 := ev702.heap_extends
    have e740 := ev740.heap_extends
    have e821 := ev821.heap_extends
    have e843 := ev843.heap_extends
    have e889 := ev889.heap_extends
    have e960 := ev960.heap_extends
    have e980 := ev980.heap_extends
    have e934 := ev934.heap_extends
    have hsub460 : ∀ cl ∈ cs460, cl ∈ calls := fun cl hm => hsub cl (by rw [hc]; simp [hm])
    have hsub629 : ∀ cl ∈ cs629, cl ∈ calls := fun cl hm => hsub cl (by rw [hc]; simp [hm])
    have hsub887 : ∀ cl ∈ cs887, cl ∈ calls := fun cl hm => hsub cl (by rw [hc]; simp [hm])
    have hcallS : (⟨"KernelSubst::subst_const", [xpval, x_a, x_val], m615⟩ : Call F) ∈ calls :=
      hsub _ (by rw [hc]; simp)
    -- the loaded record: hashed bytes at the certificate's address, a definition
    obtain ⟨-, rawBytes', c', hsz', hh', hbl', -, hdeE', hrep', -⟩ :=
      Claim.load_verified_constant_de ⟨thmB, hthB, rfl⟩ ev462
    have hrep0 := hrep'
    obtain ⟨infoVal, _, refsVal, _, _, hv_c, hinfo, _, hr_list, _, _⟩ := hrep'
    injection hv_c with _ _ hargs_c
    simp only [List.cons.injEq] at hargs_c
    rw [← hargs_c.1] at hinfo
    rw [← hargs_c.2.2.1] at hr_list
    obtain ⟨d, hinfo'⟩ := claimInfo_defn' hinfo
    obtain ⟨rawBytes, c, hh, haddr, hex, hres⟩ :=
      Ingress.get_ci_trace_spec (Bytes.repAddressRef_heapMono₂ addrTy e462 hthB) ev631
    have hraw : rawBytes = rawBytes' := hS.hashed_inj (Claim.hashed_mono hsub629 hh)
      (Claim.hashed_mono hsub460 hh') (haddr.trans hbl'.symm)
    subst hraw
    have hcc : c = c' := Except.ok.inj (hex.symm.trans hdeE')
    subst hcc
    -- the proof's conversion
    unfold Ingress.GetCITraceResult at hres
    rw [hinfo'] at hres
    obtain ⟨blobs, tree, v, hhp, built, hld, htr⟩ := hres
    obtain ⟨hnlvls, tyPtr, valPtr, hint, planT, planV, hvv, rty, rval, hpT, hpV, hlT, hlV⟩ := htr
    subst hvv
    have hshape : Ingress.defnValShape d tyPtr valPtr hint =
        .construct "KernelTypes::KConstantInfo" "Thm" [xnl, w646, xpval] :=
      Except.ok.inj (hld.symm.trans ld625)
    have hkind : d.kind = .thm := by
      cases hk : d.kind with
      | thm => rfl
      | defn => simp [Ingress.defnValShape, hk, Core.kciEnum] at hshape
      | opaq => simp [Ingress.defnValShape, hk, Core.kciEnum] at hshape
    have hxp : valPtr = xpval := by
      simp only [Ingress.defnValShape, hkind] at hshape
      injection hshape with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      exact hargs.2.2
    have hrecur : Ingress.defnRecurAddrs d (ixAddr thmB) = [] := by
      simp [Ingress.defnRecurAddrs, Ingress.defnIsUnsafeCI, hkind]
    rw [hrecur, hxp] at rval
    -- the proof term, read, replaced and scope-checked
    obtain ⟨X, hX⟩ := rawConv_tmR (κ := keyOf t) rval
    have ext615 := ext0.trans (e462.trans e631)
    have hvR : TmR (keyOf t) _ val x_val :=
      tmExact_toTmR ((hv 0 (fun _ => .sort .zero)).mono ext615)
    have hvc : val.looseBVarsBounded 0 = true :=
      Tm.looseBVarsBounded ((hv 0 (fun _ => .sort .zero)).toTm)
    obtain ⟨hPR, -, hcells⟩ :=
      subst_const_raw hinj hvc (Bytes.repAddressRef_heapMono₂ addrTy ext615 hb) hvR hX ev702
    rw [hkb] at hPR
    obtain ⟨hPC, hPlv⟩ := hPR.closed_of_scope (Heap.Extends.refl _) ev740
    -- the references the proof uses: no block, stored
    have hrefs : RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem _
        c.refs.toList w496 :=
      repList_heapMono₂ _ Claim.repAddrElem_heapMono₂
        (e631.trans (e702.trans (e740.trans (e821.trans e843)))) hr_list
    obtain ⟨-, hidxs⟩ := Claim.const_idxs_of_spec
      (hrep0.mono (e631.trans (e702.trans e740))) ev821
    have hbound : 0 + c.refs.toList.length < 8589934592 := by
      rw [Nat.zero_add, Array.length_toList]
      exact refs_size_lt_bound_cert hsz' hdeE'
    have ev889' : ObsFn W "KernelRoles::walk_refs_except"
        [x_rc, w496, v808, .field ((0 : Nat) : F), x_a] m831 v876 m877 cs887 := by
      simpa using ev889
    have ext831 :=
      ext0.trans (e462.trans (e631.trans (e702.trans (e740.trans (e821.trans e843)))))
    obtain ⟨-, hwalk⟩ := walk_refs_except_notBlock c.refs.toList hbound (hrc.mono ext831)
      hrefs (hidxs.mono e843)
      ⟨b, Bytes.repAddressRef_heapMono₂ addrTy ext831 hb, rfl⟩ ev889'
    have hused : ∀ i, i ∈ IxVM.Consistency.usedRefIdxs c → ∀ x : Bytes.Address,
        c.refs.toList[i]? = some (ixAddr x) → x ≠ b →
        ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci := by
      intro i hu x hx hne
      have hlt : i < c.refs.toList.length := (List.getElem?_eq_some_iff.mp hx).1
      have hxe : c.refs.toList[i] = ixAddr x := (List.getElem?_eq_some_iff.mp hx).2
      have hnb := hwalk i hlt (by rw [Nat.zero_add, Assembly.usedRefIdxs_eq]; exact hu)
        (by rw [hxe]; intro e'; exact hne (Decl.ixAddr_injective e'))
      rw [hxe] at hnb
      exact hcert (ixAddr thmB) hev0 rawBytes c (Claim.hashed_mono hsub629 hh) hsz' haddr hex i
        hu x hx hne (hnb.mono hsub887)
    have huse_of : ∀ x : Bytes.Address,
        (∃ i, (i ∈ IxVM.Consistency.exprRefIdxs d.value ∨
          ∃ s ∈ c.sharing.toList, i ∈ IxVM.Consistency.exprRefIdxs s) ∧
          c.refs.toList[i]? = some (ixAddr x)) → x ≠ b →
        ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci := by
      rintro x ⟨i, hi, hr⟩ hne
      have hu : i ∈ IxVM.Consistency.usedRefIdxs c := by
        unfold IxVM.Consistency.usedRefIdxs
        rw [hinfo']
        rcases hi with hi | ⟨s, hs, his⟩
        · exact List.mem_append_right _ (List.mem_append_right _ hi)
        · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
      exact hused i hu x hr hne
    have rval690 := rval.mono e702 (fun _ hm => hm)
    have stored : ∀ x, AddrIn m690 v689 x → ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci := by
      intro x hin
      rcases hcells m690 (Heap.Extends.refl _) x hin with h1 | ⟨h1, hne⟩ | h1
      · exact hvcells m690 (ext615.trans e702) x h1
      · rcases Ingress.RawConvExpr.addrIn_used rval690 x h1 with hr | hr
        · exact huse_of x hr hne
        · cases hr
      · -- a projection the substitution meets: read off its own call
        have hne : x ≠ b := hnoproj (ixAddr thmB) hev0 rawBytes c (Claim.hashed_mono hsub629 hh)
          hsz' haddr hex d hinfo' _ _ _ _ _ _ rval _ _ _ _ _ hcallS ev702
          (Bytes.repAddressRef_heapMono₂ addrTy ext615 hb) x h1
        exact huse_of x (Ingress.RawConvExpr.projIn_used rval690 x h1) hne
    -- the proof term at the closure's keying
    have hPs : TmC cx.stored.κ m690 (Expr.substConstAll (.role r) val X) v689 :=
      hPC.rekey
        (fun x hin => by
          obtain ⟨ci, hci⟩ := stored x hin
          exact Ctx.stored_key_of_find (c := cx) hci)
        (fun x hp _ => by
          obtain ⟨ci, hci⟩ := stored x hp.addrIn
          exact Ctx.stored_projPermitted_of_find (c := cx) hci)
    obtain ⟨hPnl, hPfv, hPcl, -⟩ := OpRefine.tmC_props hPs
    -- the statement
    have ext764 := ext831.trans (e889.trans (e960.trans (e980.trans e934)))
    obtain ⟨ext1124, hv1123, Γ, htypes, hghost, heqn, hΓ0, hΓ1, hΓh, hlen⟩ :=
      certStmt_open (Ec := Ec) (env := env) (lim := lim) htwf hmem hget htbl hb hkb hv.toTmC
        hvcells hnamed ext764 ev1058 ev1043 hm1106 ev1029 ev1136
    -- the proof applied to the statement's variables
    rw [hv1123] at ev1194
    have hnlen : st.1.length ≤ 2 := by simp only [List.length_map] at hlen; omega
    have htop : ZMod.val (((2 + st.1.length : Nat)) : F) = 2 + st.1.length :=
      ZMod.val_natCast_of_lt (by change _ < 18446744069414584321; omega)
    have ext690 : Heap.Extends m690 m1124 :=
      (e740.trans (e821.trans (e843.trans (e889.trans (e960.trans (e980.trans e934)))))).trans
        ((ev1058.heap_extends.trans ev1043.heap_extends).trans
          ((show Heap.Extends _ _ by rw [hm1106]; exact Heap.Extends.snoc _ _).trans
            (ev1029.heap_extends.trans ev1136.heap_extends)))
    obtain ⟨happ, ext1163⟩ := OpOpen.apply_bvars_desc_spec htop (by omega)
      ((hPs.mono ext690) (2 + st.1.length) Γ) ev1194 ev1173
    have hmk := OpOpen.mkAppN_fvars_divModCertApplied
      (P := Expr.substConstAll (.role r) val X) hΓ0 hΓ1 hΓh hlen
    rw [List.length_map] at hmk
    rw [hmk] at happ
    refine ⟨Expr.substConstAll (.role r) val X, hPcl, hPfv, hPnl, hPlv, Γ, x_rc, xtypes, v1152,
      xeqn, res, m1163, h', cs1148, hrc.mono ((ext764.trans ext1124).trans ext1163),
      htypes.mono ext1163, hghost, ev1150, hgood.sub (fun cl hm => by rw [hc]; simp [hm]), happ,
      heqn.mono ext1163⟩

/-- **Every certificate, from the walk of the evidence list** (`validate_op_equations` from
index `k`): at a well-founded operation, each entry of the evidence list checks the
certificate statement at its index. -/
theorem certObs_of_evidence {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ()) {r : Role}
    (hmem : (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natDivModNames)
    (hp1 : RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_evidence_is_proof.body)
      (roleNum r) = some 1)
    {calls : List (Call F)} {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {Ec : Ixon.Env} {env : Ix.Kernel.Env .anon} {lim : Nat} {val : KExpr}
    {x_rc x_tbl x_a x_val : SourceValue F} {b : Bytes.Address} {h₀ : Heap F}
    (hrc : RCRep t (some lim) h₀ x_rc) (htbl : TableRep t h₀ x_tbl)
    (hb : Bytes.RepAddressRef addrTy h₀ b x_a) (hkb : keyOf t (ixAddr b) = .role r)
    (hv : Decl.TmCExact (keyOf t) h₀ val x_val)
    (hvcells : ∀ h₂, Heap.Extends h₀ h₂ → ∀ x, AddrIn h₂ x_val x →
      ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci)
    (hnamed : ∀ x : Bytes.Address, certNamedOk r (keyOf t (ixAddr x)) = true → x ≠ b →
      ∃ ci, env.find? (keyOf t (ixAddr x)) = some ci) :
    ∀ {es : List (Ix.Kernel.Evidence _root_.Address)} (k : Nat) {x_ev res : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      Heap.Extends h₀ h → RepList evListEnum EvRep h es x_ev →
      (∀ thm, Ix.Kernel.Evidence.proof thm ∈ es → CertRefsStoredAt calls t env b thm) →
      (∀ thm, Ix.Kernel.Evidence.proof thm ∈ es → CertProjFreeAt calls b thm) →
      ObsFn W "KernelRoles::validate_op_equations"
        [x_rc, x_tbl, .field (roleNum r), x_a, x_val, x_ev, .field ((k : Nat) : F)] h res h' cs →
      (∀ cl ∈ cs, cl ∈ calls) → Good ⟨Ec, env, t, none⟩ cs →
      ∀ i, i < es.length → ∀ st,
        (Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey))[k + i]? = some st →
        ∃ P : KExpr, P.looseBVarsBounded 0 = true ∧ P.hasFvar = false ∧
          Decl.noLetExpr P = true ∧ P.allLevelParamsDefined [] = true ∧
          OpRefine.CertObs Ec t lim env (.role r) val st P
  | es, k, x_ev, res, h, h', cs, ext0, hlist, hcert, hnoproj, ev, hsub, hgood => by
    cases Obs.«KernelRoles::validate_op_equations».obs ev with
    | Nil ld12 _ he23 _ =>
      rw [← evListEnum] at ld12
      obtain rfl := Lib.rep_nil_of_load hlist ld12
      intro i hi
      cases hi
    | Cons x_e x_rest v2523 m2524 cs2526 cs2535 v2544 ld12 sg2531 op2600 ev2537 hc2602 =>
      rw [← evListEnum] at ld12
      obtain ⟨e, rest, rfl, he_rep, hrest_rep⟩ := Lib.rep_cons_of_load hlist ld12
      have tailMember : (⟨"KernelRoles::validate_op_equations",
          [x_rc, x_tbl, .field (roleNum r), x_a, x_val, x_rest, v2544], m2524⟩ : Call F) ∈
          cs := by
        rw [hc2602]; simp
      have ext1 : Heap.Extends h m2524 := (ev.call_heap_bounds tailMember).1
      obtain rfl := Decl.evalBinOp_add_one k op2600
      have hhead := certObs_of_seg ht hmem hp1 hS hrc htbl hb hkb hv hvcells hnamed
        (ev0 := e)
        (fun thm he' => hcert thm (by rw [← he']; exact List.mem_cons_self))
        (fun thm he' => hnoproj thm (by rw [← he']; exact List.mem_cons_self))
        ext0 he_rep sg2531
        (fun cl hm => hsub cl (by rw [hc2602]; simp [hm]))
        (hgood.sub (fun cl hm => by rw [hc2602]; simp [hm]))
      have htail := certObs_of_evidence ht hmem hp1 hS hrc htbl hb hkb hv hvcells hnamed (k + 1)
        (ext0.trans ext1) (repList_heapMono₂ evListEnum evRep_heapMono₂ ext1 hrest_rep)
        (fun thm hm => hcert thm (List.mem_cons_of_mem _ hm))
        (fun thm hm => hnoproj thm (List.mem_cons_of_mem _ hm)) ev2537
        (fun cl hm => hsub cl (by rw [hc2602]; simp [hm]))
        (hgood.sub (fun cl hm => by rw [hc2602]; simp [hm]))
      intro i hi st hget
      cases i with
      | zero => exact hhead st (by simpa using hget)
      | succ i =>
        exact htail i (by simp at hi; omega) st
          (by rwa [show k + (i + 1) = k + 1 + i by omega] at hget)

/-! ## `OpCertFacts` from the one premise left -/

/-- **No certificate of a well-founded operation projects the operation where the operation is
substituted into its proof**: for an operation `r` bound at `a` and a certificate `thm` in its
evidence whose record in the run's store is a standalone definition, a call of
`KernelSubst::subst_const` in the run on a conversion `p` of the certificate's value, with `a`
as its second argument, reaches no projection whose structure is at `a`: every projection
reached from `p` through applications, binders, `let`s and projection arguments at the call's
output heap (`ProjIn`, the cells the substitution visits) has its structure elsewhere. A shared
expression of the record that the value does not reach is not constrained. Producer:
`KernelSubst::subst_const`'s projection arm refusing a projection whose structure address is
the address of the operation it replaces (`certProjFree_of_subst`). -/
def CertProjFree (calls : List (Call F)) : Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (ρ : BRun) (Rs : Nat → Ixon.Env), BindingRun calls t ρ Rs →
    ∀ (r : Role) (a : _root_.Address), r ∈ RoleOps.opRoles → t.addressOf? r = some a →
    ∀ (arr : Array (Ix.Kernel.Evidence _root_.Address)) (thm : _root_.Address),
      (r, arr) ∈ t.evidence.toList → Ix.Kernel.Evidence.proof thm ∈ arr.toList →
    ∀ (c : Ixon.Constant) (d : Ixon.Definition), IxVM.Consistency.recordOf ρ.E₀ thm = some c →
      c.info = .defn d →
    ∀ (recurAddrs : List _root_.Address) (univs : List Ixon.Univ)
      (blobs : List (_root_.Address × ByteArray)) (bound : Nat) (h : Heap F) (p : SourceValue F),
      Ingress.RawConvExpr c.refs.toList recurAddrs univs c.sharing.toList blobs h bound d.value p →
    ∀ (x_a x_v res : SourceValue F) (h' : Heap F) (cs : List (Call F)),
      (⟨"KernelSubst::subst_const", [p, x_a, x_v], h⟩ : Call F) ∈ calls →
      ObsFn W "KernelSubst::subst_const" [p, x_a, x_v] h res h' cs →
    ∀ b : Bytes.Address, ixAddr b = a → Bytes.RepAddressRef addrTy h b x_a →
    ∀ x : Bytes.Address, ProjIn h' p x → x ≠ b

/-- **`CertProjFree` from the substitution's own refusal**: if every successful
`KernelSubst::subst_const(e, a, v)` reaches, at its output heap, no projection whose structure
is at the address `a` holds, then `CertProjFree` holds of every call list. The premise is what
the projection arm's refusal of a projection at the substituted address gives, read off the
substitution's observation. -/
theorem certProjFree_of_subst
    (hsub : ∀ (e a v r : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (b x : Bytes.Address), ObsFn W "KernelSubst::subst_const" [e, a, v] h r h' cs →
      Bytes.RepAddressRef addrTy h b a → ProjIn h' e x → x ≠ b) :
    ∀ calls : List (Call F), CertProjFree calls := by
  intro calls t ρ Rs hrun r a hr ha arr thm harr hthm c d hc hd recurAddrs univs blobs bound h p
    rp x_a x_v res h' cs _ ev b _ hb x hx
  exact hsub p x_a x_v res h h' cs b x ev hb hx

/-- **`CertProjFree` is implied by the inequality at every projection index of the record**: a
projection a conversion of the value reaches has its structure at a projection's structure
index of the value or of a shared expression (`RawConvExpr.projIn_prj`). The converse fails at
a shared expression the value does not reach. -/
theorem certProjFree_of_inventory {calls : List (Call F)}
    (hinv : ∀ (t : Ix.Kernel.RoleTable) (ρ : BRun) (Rs : Nat → Ixon.Env),
      BindingRun calls t ρ Rs →
      ∀ (r : Role) (a : _root_.Address), r ∈ RoleOps.opRoles → t.addressOf? r = some a →
      ∀ (arr : Array (Ix.Kernel.Evidence _root_.Address)) (thm : _root_.Address),
        (r, arr) ∈ t.evidence.toList → Ix.Kernel.Evidence.proof thm ∈ arr.toList →
      ∀ (c : Ixon.Constant) (d : Ixon.Definition),
        IxVM.Consistency.recordOf ρ.E₀ thm = some c → c.info = .defn d →
      ∀ x : _root_.Address, Ingress.PrjUsed c.refs.toList c.sharing.toList d.value x → x ≠ a) :
    CertProjFree calls := by
  intro t ρ Rs hrun r a hr ha arr thm harr hthm c d hc hd recurAddrs univs blobs bound h p rp
    x_a x_v res h' cs _ ev b hb _ x hx hxb
  exact hinv t ρ Rs hrun r a hr ha arr thm harr hthm c d hc hd (ixAddr x)
    (Ingress.RawConvExpr.projIn_prj (rp.mono ev.heap_extends (fun _ hm => hm)) x hx)
    (by rw [hxb]; exact hb)

private theorem evList_length'' {es : List (Ix.Kernel.Evidence _root_.Address)}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<KernelRoles::RoleEvidence>» [l] h r h' cs)
    (hl : RepList evListEnum EvRep h es l) :
    r = .field (es.length : F) ∧ h' = h := by
  have ev' : ObsFn W (Instance.mk "Lists::length" [.named "KernelRoles::RoleEvidence" []]).symbol
      [l] h r h' cs := by
    rw [Obs.Names.«Lists::length<KernelRoles::RoleEvidence>».symbol]; exact ev
  have hl' : RepList (Instance.mk "Lists::Node" [.named "KernelRoles::RoleEvidence" []]).symbol
      EvRep h es l := by
    rw [Obs.Names.«Lists::Node<KernelRoles::RoleEvidence>».symbol]; exact hl
  exact Lib.Lists.length_spec ev' hl'

private theorem le_length_of_cast' {n m : Nat} (hn : n < 4294967296)
    (e : ((m : Nat) : F) = ((n : Nat) : F)) : n ≤ m := by
  have hv := congrArg ZMod.val e
  rw [ZMod.val_natCast, Claim.val_of_lt_u32 hn] at hv
  exact hv ▸ Nat.mod_le _ _

set_option maxRecDepth 100000 in
/-- Every operation has fewer than 64 certificate statements (decided). -/
theorem certCount_small : Role.all.all (fun r =>
    decide ((Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey)).length < 64)) = true := by
  decide +kernel

/-- A list whose every index carries a related element is related to some list. -/
theorem exists_forall₂_of_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ (l : List α), (∀ (i : Nat) (a : α), l[i]? = some a → ∃ b, R a b) →
      ∃ bs, List.Forall₂ R l bs
  | [], _ => ⟨[], .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h 0 a rfl
    obtain ⟨bs, hbs⟩ := exists_forall₂_of_getElem? l (fun i x hx => h (i + 1) x (by simpa using hx))
    exact ⟨b :: bs, .cons hb hbs⟩

set_option maxHeartbeats 6400000 in
/-- **`OpCertFacts` from `CertProjFree`**: at a well-founded operation, from the observed
`validate_role`, one checked certificate per statement (`OpRefine.CertObs`) at the closure's
environment. The value `validate_op_equations` substitutes is the pointer of `validate_role`'s own
load (`LoadedReads.get_ci_defn_value_exact`); the constants a statement names are stored by the
closure's coverage (`WalkedStored`) and by the prefix (`Eq`, `Bool` and its constructors); the
references a certificate's proof uses are stored by the coverage, from the operation's walk of
them (`RoleVal.ValidateRoleIn.op_certificate_walks`, its records no block, in Lean's logic and
held by the group's store, `Admits.evidenceRefs`). -/
theorem opCertFacts_of_projFree {calls : List (Call F)} (hpf : CertProjFree calls) :
    OpCertFacts.{u} calls := by
  intro t ρ Rs hrun ht g r a R R₁ R' Ec env₁ c d val₀ val h6 h77 hgrp hop ha hadm hrd hadds hws
    hEc hst hinv hcE hinfo hlv0 hlogic hvl h3 h4 hcV hstored hpre hmem
  have htwf : t.wf = true := wf_of_check ht
  have hrg : r ∈ IxVM.Consistency.roleGroup g := by rw [hgrp]; exact List.mem_singleton.mpr rfl
  have hgr : Ix.SpecDigest.groupOf r = g := OpInstall.groupOf_of_mem_roleGroup hrg
  obtain ⟨hp1, hcount⟩ := opTables_wf hmem
  have h64 : (Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey)).length < 64 := by
    have := List.all_eq_true.mp certCount_small r (Role.mem_all r)
    simpa using this
  obtain ⟨bAddr, tb, -, -, hρ⟩ := hrun.observed
  have hval : RoleVal.ValidateRoleIn calls bAddr t g r := by
    have e : ρ.validated = (observedRun calls bAddr t ρ.E₀ ρ.rank).validated :=
      congrArg BRun.validated hρ
    have h1 := hadm.validated r hrg
    rw [e] at h1
    exact h1
  have hcR' : IxVM.Consistency.recordOf R' a = some c := by
    obtain ⟨c₁, hc₁⟩ := Option.isSome_iff_exists.mp
      (hadm.kept r hrg (Or.inl (OpInstall.op_kept hop).1) a ha)
    have h1 := recordOf_sub hadm.loaded a c₁ hc₁
    rw [hcE] at h1
    rw [hc₁, Option.some.inj h1]
  have hcEc : IxVM.Consistency.recordOf Ec a = some c :=
    (Typing.recordOf_eq_recordAt_of_decoded hEc.1 a).trans (hEc.2.1 a c hcR')
  have hblobEc : ∀ x b, ρ.E₀.blobs.get? x = some b → Ec.blobs.get? x = some b :=
    fun x b hx => hEc.2.2.1 x b (hrd.blobs x b hx)
  have hgood : Good ⟨Ec, env₁, t, none⟩ calls := hst.good env₁ none
  have hk2 : RoleVal.roleSpecKindNat r = 2 := (specKind_two_iff r).mpr hop
  have hval0 := hval
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsubV⟩ := hval
  have htblR : TableRep t h x_tbl := htbl.toTableRep
  cases Obs.«KernelRoles::validate_role».obs ev with
  | n2 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs236
      ev14 ev47 ld41 ev80 ev100 heq109 ev124 ev238 hc279 =>
    have hsub45 : ∀ cl ∈ cs45, cl ∈ calls := fun cl hm => hsubV cl (by rw [hc279]; simp [hm])
    have hsub236 : ∀ cl ∈ cs236, cl ∈ calls := fun cl hm => hsubV cl (by rw [hc279]; simp [hm])
    obtain ⟨ext_ba, a', ha_m2, had⟩ := RoleVal.role_bound_addr_uncond htblR ev14
    have ea : a' = a := Option.some.inj (had.symm.trans ha)
    subst ea
    obtain ⟨b, hbr, hba⟩ := ha_m2
    subst hba
    have hkb : keyOf t (ixAddr b) = .role r := keyOf_of_addressOf htwf had
    have ext32_111 : Heap.Extends m32 m111 :=
      ev80.heap_extends.trans (ev100.heap_extends.trans ev124.heap_extends)
    have exth_111 : Heap.Extends h m111 := ext_ba.trans (ev47.heap_extends.trans ext32_111)
    -- the value pointer of the role's own load
    have hvlEc := ReaderReads.exprReader_mono hblobEc hvl
    have h4' : val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true := by
      rw [hlv0]; exact h4
    obtain ⟨tyPtr, valPtr, hintV, blobs, val', hcV', hldv, htmV, rval⟩ :=
      LoadedReads.get_ci_defn_value_exact ht (hgood.sub hsub45).1 hbr ev47 hcEc hinfo hlogic
        hvlEc h3 h4'
    have hvv : val' = val := by
      rw [hlv0] at hcV'
      exact Option.some.inj (hcV'.symm.trans hcV)
    rw [hvv, hlv0, Decl.posOf_range] at htmV
    have hv31 : v31 = Ingress.defnValShape d tyPtr valPtr hintV :=
      Except.ok.inj (ld41.symm.trans hldv)
    match Obs.«KernelRoles::validate_op».obs ev238 with
    | .other (heq575 := hbad) .. => exact (zero_ne_one (Value.field.inj hbad)).elim
    | .Defn (m391 := m391) (m400 := m400) (m443 := m443) (m463 := m463) (v399 := v399)
        (v440 := v440) (v441 := v441) (x_val := x_val) (cs486 := cs486) (hv114 := hci)
        (ev412 := ev412) (ev453 := ev453) (ev473 := ev473) (heq482 := heq482) (ev488 := ev488)
        (hc544 := hca) .. =>
      have memE : (⟨"KernelRoles::validate_op_equations",
          [x_rc, x_tbl, .field (roleNum r), v1, x_val, v399, .field 0], m463⟩ : Call F) ∈
          cs236 := by
        rw [hca]; simp
      have memR : (⟨"KernelRoles::role_evidence", [x_tbl, .field (roleNum r)], m391⟩ :
          Call F) ∈ cs236 := by
        rw [hca]; simp
      have ext111_463 : Heap.Extends m111 m463 := (ev238.call_heap_bounds memE).1
      have ext111_391 : Heap.Extends m111 m391 := (ev238.call_heap_bounds memR).1
      have hsub486 : ∀ cl ∈ cs486, cl ∈ calls :=
        fun cl hm => hsub236 cl (by rw [hca]; simp [hm])
      -- the value pointer is the role's own load's
      rw [hv31] at hci
      have hkind : d.kind = .defn := by
        cases hk : d.kind with
        | defn => rfl
        | opaq => simp [Ingress.defnValShape, hk, Core.kciEnum] at hci
        | thm => simp [Ingress.defnValShape, hk, Core.kciEnum] at hci
      have hsh : Ingress.defnValShape d tyPtr valPtr hintV = .construct Core.kciEnum "Defn"
          [.field (d.lvls.toNat : F), tyPtr, valPtr, Ingress.repDefSafetyVal d.safety, hintV] := by
        simp [Ingress.defnValShape, hkind]
      rw [hsh] at hci
      have hfl := (Value.construct.inj hci).2.2
      simp only [List.cons.injEq] at hfl
      obtain ⟨-, -, hxval, -, -⟩ := hfl
      -- the evidence list, its length, and the table's evidence
      let c₀ : Ctx := { E := default, env := default, t := t, lim := none }
      obtain ⟨es, hlist, hes⟩ := role_evidence_step (ScopedCtx.unrestricted c₀) ev412 x_tbl r rfl
        (htblR.mono (exth_111.trans ext111_391))
      obtain ⟨hlen, hm443⟩ := evList_length'' ev453 hlist
      obtain ⟨hcnt, hm463⟩ := op_equation_count_val hcount ev473
      have hlist463 : RepList evListEnum EvRep m463 es v399 := by
        rw [hm463, hm443]; exact hlist
      have hge : (Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey)).length ≤
          es.length :=
        le_length_of_cast' (by omega) (Value.field.inj (hlen.symm.trans (heq482.trans hcnt)))
      have hesT : ∀ thm, Ix.Kernel.Evidence.proof thm ∈ es →
          ∃ arr, (r, arr) ∈ t.evidence.toList ∧ Ix.Kernel.Evidence.proof thm ∈ arr.toList := by
        intro thm hthm
        rcases hes with hnil | ⟨arr, harr, hae⟩
        · rw [hnil] at hthm; cases hthm
        · exact ⟨arr, harr, by rw [hae]; exact hthm⟩
      -- the premises of the walk, at the walk's heap
      have ext32_463 : Heap.Extends m32 m463 := ext32_111.trans ext111_463
      have hvcells : ∀ h₂, Heap.Extends m463 h₂ → ∀ x, AddrIn h₂ valPtr x →
          ∃ ci, env₁.find? (keyOf t (ixAddr x)) = some ci := by
        intro h₂ e₂ x hin
        have hin32 := TmExact.addrIn_back (htmV 0 (fun _ => .sort .zero)) (ext32_463.trans e₂)
          x hin
        rcases Ingress.RawConvExpr.addrIn_used rval x hin32 with ⟨i, hi, hr⟩ | hr
        · have hu : i ∈ IxVM.Consistency.usedRefIdxs c := by
            unfold IxVM.Consistency.usedRefIdxs
            rw [hinfo]
            rcases hi with hi | ⟨s, hs, his⟩
            · exact List.mem_append_right _ (List.mem_append_right _ hi)
            · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
          exact hstored i hu (ixAddr x) hr
        · cases hr
      have hnamed : ∀ x : Bytes.Address, certNamedOk r (keyOf t (ixAddr x)) = true → x ≠ b →
          ∃ ci, env₁.find? (keyOf t (ixAddr x)) = some ci := by
        intro x hn hne
        cases hk : keyOf t (ixAddr x) with
        | role r' =>
          rw [hk] at hn
          simp only [certNamedOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hn
          rcases hn with ((((hrr | ⟨hw, hlt⟩) | hq) | hbo) | htr') | hfa
          · exfalso
            subst hrr
            exact hne (Decl.ixAddr_injective (Decl.keyOf_injective htwf (hk.trans hkb.symm)))
          · have hs := hws.2 r' (ixAddr x) hw (by rw [← hgr]; exact hlt)
              (addressOf_of_keyOf htwf hk)
            rw [show IxVM.Consistency.keyOf t (ixAddr x) = .role r' from hk] at hs
            exact Option.isSome_iff_exists.mp hs
          · subst hq
            exact ⟨_, hpre.eq⟩
          · subst hbo
            exact Option.isSome_iff_exists.mp
              (RoleOps.boolStored_of_ctorsTyped hinv.store.store hpre.boolCtorsTyped)
          · subst htr'
            obtain ⟨⟨ci₁, hci₁, -⟩, -⟩ := hpre.op.boolCtors (Or.inr (Or.inr hmem))
            exact ⟨ci₁, hci₁⟩
          · subst hfa
            obtain ⟨-, ⟨ci₂, hci₂, -⟩⟩ := hpre.op.boolCtors (Or.inr (Or.inr hmem))
            exact ⟨ci₂, hci₂⟩
        | _ => simp [hk, certNamedOk] at hn
      -- the certificates' references
      have hcertD : ∀ thm, Ix.Kernel.Evidence.proof thm ∈ es →
          CertRefsStoredAt calls t env₁ b thm := by
        intro thm hthm rawBytes c₁ hh hsz hbl hde i hu x hx hne hnb
        obtain ⟨arr, harr, hthmA⟩ := hesT thm hthm
        obtain ⟨raw', c', -, hh', hbl', hde', hg, hw⟩ :=
          RoleVal.ValidateRoleIn.op_certificate_walks hval0 hk2 had harr hthmA
        have hraw : rawBytes = raw' := hrun.runStore.hashed_inj hh hh' (hbl.trans hbl'.symm)
        subst hraw
        have hcc : c₁ = c' := Except.ok.inj (hde.symm.trans hde')
        subst hcc
        have hxa : ixAddr x ≠ ixAddr b := fun e' => hne (Decl.ixAddr_injective e')
        have hlt : i < c₁.refs.toList.length := (List.getElem?_eq_some_iff.mp hx).1
        have hxe : c₁.refs.toList[i] = ixAddr x := (List.getElem?_eq_some_iff.mp hx).2
        have hu' : i ∈ BaseSeams.usedRefIdxs c₁ := by rw [Assembly.usedRefIdxs_eq]; exact hu
        obtain ⟨-, hcov⟩ := hw i hlt hu' (by rw [hxe]; exact hxa)
        rw [hxe] at hcov
        -- the certificate's record and the record at `x`
        have hrecThm : IxVM.Consistency.recordOf ρ.E₀ thm = some c₁ := by
          rw [← hbl]
          exact Claim.recordOf_hashed hrun.runStore hrun.hashedStored hh hsz
            (Ingress.deConstant_of_deConstantExact hde) hde
        have hU : Typing.UsedRef ρ.E₀ thm (ixAddr x) :=
          ⟨c₁, i, hrecThm, hu, by rw [← Array.getElem?_toList]; exact hx⟩
        have hR' := hadm.evidenceRefs r hrg arr thm (ixAddr x) harr hthmA hU
          (by rw [had]; intro e'; exact hxa (Option.some.inj e').symm)
        obtain ⟨cx, hcx⟩ := Option.isSome_iff_exists.mp hR'
        have hcx₁ : IxVM.Consistency.recordOf R₁ (ixAddr x) = some cx :=
          (OpInstall.recordOf_ne hadds hxa).symm.trans hcx
        by_cases hcovP : Claim.CoveredAt t (some (valLimit g)) (ixAddr x)
        · obtain ⟨r', hr', ⟨hw', hlt'⟩ | ⟨hnone, -⟩⟩ := hcovP
          · have hs := hws.2 r' (ixAddr x) hw' (Nat.lt_of_lt_of_le (hlt' _ rfl) (valLimit_le g)) hr'
            exact Option.isSome_iff_exists.mp hs
          · cases hnone
        · obtain ⟨recs, hcl, hmem'⟩ := hcov.resolve_left hcovP
          obtain ⟨r', hr', hr'x⟩ := List.mem_map.mp hmem'
          have hxE : IxVM.Consistency.recordOf ρ.E₀ (ixAddr x) = some r'.c := by
            rw [← hr'x]
            exact topRec_recordOf hrun.hashedStored r'
          have hcxE : IxVM.Consistency.recordOf ρ.E₀ (ixAddr x) = some cx :=
            recordOf_sub hadm.loaded _ cx hcx
          have ecx : cx = r'.c := Option.some.inj (hcxE.symm.trans hxE)
          -- no block
          have hnm : ∀ ms, cx.info ≠ .muts ms := by
            obtain ⟨raw, c'', hhr, hbr, hdr, hnm⟩ := hnb
            have eraw : raw = r'.rawBytes :=
              hrun.runStore.hashed_inj hhr r'.hhashed (hbr.trans (hr'x.symm.trans r'.hblake.symm))
            rw [eraw, r'.hde] at hdr
            have e₄ : r'.c = c'' := Except.ok.inj hdr
            rw [ecx, e₄]
            exact hnm
          -- in Lean's logic, with its block
          obtain ⟨hh₁, hh₁', x_rc₁, x_refs, x_used, x_a₁, r₁, cs₁, hrc₁, hrefs₁, hidx₁, ha₁, ev₁,
            hs₁⟩ := hg
          have hbnd : c₁.refs.toList.length < 8589934592 := by
            rw [Array.length_toList]
            exact refs_size_lt_bound_cert hsz hde
          have hsafe := Claim.assert_safe_refs_except_spec (lim := some (valLimit g))
            hrun.runStore hbnd hrc₁ hrefs₁ hidx₁ ha₁ ev₁ hs₁ i hlt hu' (by rw [hxe]; exact hxa)
            (by rw [hxe]; exact hcovP)
          rw [hxe] at hsafe
          obtain ⟨hlx, hox⟩ := hsafe cx hcxE
          -- checked at the limit
          have hchk : ρ.checked (ixAddr x) (valLimit g) := by
            have e₅ : ρ.checked = (observedRun calls bAddr t ρ.E₀ ρ.rank).checked :=
              congrArg BRun.checked hρ
            rw [e₅]
            show UnitCheckedAt calls bAddr t ρ.E₀ (ixAddr x) (some (valLimit g))
            rcases r'.hchecked with ⟨ms, hms, -⟩ | hc
            · exact (hnm ms (by rw [ecx]; exact hms)).elim
            · left
              rw [← hr'x]
              exact hc
          have hown₁ : ∀ cb, IxVM.Consistency.recordOf R₁ (Ix.Cert.ownerOf (ixAddr x) cx) =
              some cb → IxVM.Consistency.InLogic cb :=
            fun cb hcb => hox cb (recordOf_sub hadm.loaded _ cb (OpInstall.recordOf_up hadds hcb))
          exact Option.isSome_iff_exists.mp (hws.1 (ixAddr x) cx (valLimit g) hcx₁ hnm hlx hown₁ hchk)
      have hnoprojD : ∀ thm, Ix.Kernel.Evidence.proof thm ∈ es → CertProjFreeAt calls b thm := by
        intro thm hthm rawBytes c₁ hh hsz hbl hde d₁ hinfo₁ rA uA bA nA hS pS rS xA xV rV hS' csS
          hmS evS hbS x hpj
        obtain ⟨arr, harr, hthmA⟩ := hesT thm hthm
        have hrecThm : IxVM.Consistency.recordOf ρ.E₀ thm = some c₁ := by
          rw [← hbl]
          exact Claim.recordOf_hashed hrun.runStore hrun.hashedStored hh hsz
            (Ingress.deConstant_of_deConstantExact hde) hde
        exact hpf t ρ Rs hrun r (ixAddr b) hop had arr thm harr hthmA c₁ d₁ hrecThm hinfo₁
          rA uA bA nA hS pS rS xA xV rV hS' csS hmS evS b rfl hbS x hpj
      have hall := certObs_of_evidence (Ec := Ec) (env := env₁) (lim := valLimit g) (val := val)
        ht hmem hp1 hrun.runStore
        (Claim.RCFullRep.toRCRep (hrc.mono (exth_111.trans ext111_463)))
        (htblR.mono (exth_111.trans ext111_463))
        (Bytes.repAddressRef_heapMono₂ addrTy (ev47.heap_extends.trans ext32_463) hbr)
        hkb (htmV.mono ext32_463) hvcells hnamed (es := es) 0 (Heap.Extends.refl _) hlist463
        hcertD hnoprojD
        (by rw [← hxval] at ev488; simpa using ev488) hsub486 (hgood.sub hsub486)
      refine exists_forall₂_of_getElem? _ (fun i st hgi => ?_)
      have hi : i < (Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey)).length :=
        (List.getElem?_eq_some_iff.mp hgi).1
      exact hall i (by omega) st (by simpa using hgi)
  | n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hk2] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hk2] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hk2] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hk2] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hk2] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)

/-- **The operations' role unit in the family form, from `CertProjFree`.** -/
theorem operationRoleUnitW_of_projFree
    (hpf : ∀ calls : List (Call F), CertProjFree calls) :
    ∀ calls : List (Call F), AtGroups (BindingRun calls)
      (RoleUnitStepOverW.{u} (· ∈ RoleOps.opRoles) Typing.FormerOpenTraceAt) :=
  operationRoleUnitW_of_certs (fun calls => opCertFacts_of_projFree (hpf calls))

end IxVM.Refinement.Binding
