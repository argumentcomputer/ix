import IxVMRefinement.Binding.FamilyReconMember
import IxVMRefinement.Binding.FamilyReconType
import IxVMRefinement.Binding.FamilyReconMinors
import IxVMRefinement.Binding.FamilyReconRules
import IxVMRefinement.Binding.FamilyFlatBuild
import IxVMRefinement.Binding.FamilyFlatDerive
import IxVMRefinement.Binding.FamilyOfCall

/-! # The reconstruction form of a family record, from a family check under a group's validation

An accepted `KernelModeled::check_family` under a group's validation (a limit `n < 77`, where
`KernelRoles::rc_validates_group` answers `1`) compares every recursor of the family record with
the block's reconstruction at the recursor's position: `KernelModeled::check_recs` runs
`KernelCheck::check_recursor_canonical_at` on each, and the arm of `canonical_rules_at_pos` that
accepts a full consumption of the reconstruction is refused. This module assembles the
record-level form `FamilyRecon.RFormS` from the member-level specifications.

* `storedRules_of_trace`, `rulesTrace_shape`: the rule list a load of a recursor converts
  represents, rule by rule, the canonical readings of the record's rules (`StoredRuleRep`).
* `resolved_keyOf`, `indDataAt_block`, `indInfoAt_of_indDataAt`, `flatOwnParams_mem`,
  `primaryAt_of_major`, `recordFlatAt_fallback`: readings of the store; the list
  `build_flat_block` reads off a non-empty record does not depend on the fallback block, so the
  list each member check rebuilds (with its parent's block as the fallback) is the record's.
* `canonical_of_call`: an observed member check on represented arguments, at entry `k` of the
  flattened family, with the callee specifications of `check_recursor_canonical_at_spec`
  instantiated by the proved ones.
* `memberRecon_of_cons`: one iteration of `check_recs` gives `MemberRecon` at its position.
* `defnAnswers_of_sub`, `indAnswers_of_sub`, `ctorOfAnswers_of_sub`: the store's answers among
  the calls of the family check.
* **`rFormS_of_call`**: `RFormS` from the family check; the record has one recursor per entry
  (`CheckFamilyFlatChain.length_eq`).

Taken as hypotheses, each a definition here or in the modules it comes from: `PeerRecsSpec` (the
peer search), `MinorsListSmall` (the minor premises' list is bounded: `build_all_minors_spec`
asks the bound of its result before the member check measures it), `ElimOffsetOf` (the offset
`block_elim` hands the members), `RuleLevelsDefined` (the scoping of the rules' right-hand
sides), `ReconSide` (the bounds and fits of the entries: `ParamsFit`, `CtorFits`,
`CtorTeleSmall`, counts below `2^32`), `FlatDistinct`, `AllInd`, the load answers `CtorAnswers`,
`CtorAddrAnswers`, `CprjAnswers`, `ModeledAnswers`, and `LoadedLevelsDefined` at the check's
calls. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option autoImplicit false

namespace IxVM.Refinement.Binding.FamilyCallRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Binding.FamilyOf
open IxVM.Refinement.Binding.FamilyFlatRecord
open IxVM.Refinement.Binding.FamilyFlatBuild
open IxVM.Refinement.Binding.FamilyRecon
open IxVM.Refinement.Typing
open IxVM.Refinement.Core (W KExpr KLevel KKey kexprEnum kexprListEnum addrTy addrListEnum ixAddr
  krrEnum krrListEnum Resolved ExprLvEq)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM (F)

/-! ## The stored rules of a loaded recursor -/

section Rules

variable {t : Ix.Kernel.RoleTable}

/-- **The rules a load converts are the canonical readings of the record's rules**
(`L1.RulesTraceRep`, the rule list of a `Rec` loaded by `Ingress::get_ci`): the list represents,
rule by rule (`StoredRuleRep`), the rule's position, its field count and the canonical reading of
its right-hand side at the rule's root (`loadedAt`), where each right-hand side's reading mentions
only the level parameters below `n`. -/
theorem storedRules_of_trace (ht : t.check = .ok ())
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {n : Nat}
    {blobs : List (_root_.Address × ByteArray)} {tree : L1.BinderTreeData}
    (hn : n < 4294967296)
    (hselfk : ∀ i x m k, recurAddrs[i]? = some x → self i = some m → m = .ok k →
      k = keyOf t x)
    (hselfok : ∀ i x, recurAddrs[i]? = some x → ∃ m k, self i = some m ∧ m = .ok k)
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData src.binders.toList) tree) {h : Heap F} :
    ∀ (rus : List Ixon.RecursorRule) (j : Nat) (root : F) {p : SourceValue F},
      L1.RulesTraceRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs tree
        h j root rus p →
      j + rus.length < 18446744069414584321 →
      (∀ ru ∈ rus, ∀ v, (exprReader t blob src id self).read ru.rhs = .ok v →
        v.allLevelParamsDefined (List.range n) = true) →
      ∃ stored : List (Nat × Nat × KExpr),
        RepList krrListEnum (StoredRuleRep (keyOf t)) h stored p ∧
        ∀ (i : Nat) (ru : Ixon.RecursorRule), rus[i]? = some ru →
          ∃ rhs, loadedAt t blob src self n (root + ((i : Nat) : F)) ru.rhs = some rhs ∧
            stored[i]? = some (j + i, ru.fields.toNat, rhs) := by
  intro rus j root p tr
  induction tr with
  | nil cell =>
    intro _ _
    exact ⟨[], .nil cell, fun i ru hi => by simp at hi⟩
  | @cons j root addr rhsPtr rest ru rus plan cell hf raw planned levels _ ih =>
    intro hlen hdef
    obtain ⟨stored, hst, hall⟩ := ih (by simp only [List.length_cons] at hlen; omega)
      (fun ru' hru' => hdef ru' (List.mem_cons_of_mem _ hru'))
    obtain ⟨rhs, hld, htm⟩ := loadedAt_tmOExact (t := t) (blob := blob) (self := self)
      (recurAddrs := recurAddrs) ht hn hselfk hselfok hblob raw built planned levels
      (hdef ru List.mem_cons_self)
    refine ⟨(j, ru.fields.toNat, rhs) :: stored,
      .cons cell ⟨rhsPtr, rfl, by simp only [List.length_cons] at hlen; omega, hf, htm⟩ hst, ?_⟩
    intro i ru' hi
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      refine ⟨rhs, ?_, by simp⟩
      simpa using hld
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨rhs', hld', hs'⟩ := hall i ru' hi
      refine ⟨rhs', ?_, ?_⟩
      · have he : root + ((i + 1 : Nat) : F) = root + 1 + ((i : Nat) : F) := by
          push_cast; ring
        rw [he]; exact hld'
      · simp only [List.getElem?_cons_succ]
        rw [hs']
        congr 2
        omega

end Rules

/-! ## Readings of the store -/

section Store

variable {t : Ix.Kernel.RoleTable} {E : Ixon.Env}

/-- Every key of the role table's keying resolves. -/
theorem resolved_keyOf (t : Ix.Kernel.RoleTable) (a : _root_.Address) : Resolved (keyOf t a) :=
  (inferInstance : Resolved (IxVM.Refinement.Core.keyOf t a))

/-- The block of an inductive type the store reads is a block record of the store with the
inductive at its position. -/
theorem indDataAt_block {a : _root_.Address} {d : IndData}
    (h : indDataAt t E a = some (some d)) :
    ∃ cb ms ind, recordOf E d.blk = some cb ∧ cb.info = .muts ms ∧
      ms[d.idx]? = some (Ixon.MutConst.indc ind) := by
  unfold indDataAt at h
  repeat' split at h
  all_goals first
    | (cases h; exact ⟨_, _, _, ‹_›, ‹_›, ‹_›⟩)
    | cases h

/-- An inductive type the reconstruction reads is one the flattening reads, with the same
counts, block and position. -/
theorem indInfoAt_of_indDataAt {a : _root_.Address} {d : IndData}
    (h : indDataAt t E a = some (some d)) :
    indInfoAt E a = some (some ⟨d.nl, d.np, d.nctors, d.blk, d.idx⟩) := by
  unfold indDataAt at h
  unfold indInfoAt
  repeat' split at h
  all_goals first
    | (cases h; simp [*])
    | cases h

/-- Each count `flatOwnParams` lists is the parameter count of an entry's inductive type. -/
theorem flatOwnParams_mem {V : ReconView} :
    ∀ {es : List FlatEntry} {fop : List Nat}, flatOwnParams V es = some fop →
      ∀ n ∈ fop, ∃ e ∈ es, ∃ d, V.ind e.addr = some (some d) ∧ d.np = n
  | [], fop, h, n, hn => by
    simp only [flatOwnParams, Option.some.injEq] at h
    subst h
    cases hn
  | e₀ :: es, fop, h, n, hn => by
    simp only [flatOwnParams] at h
    cases hi : V.ind e₀.addr with
    | none => rw [hi] at h; cases h
    | some o =>
      cases o with
      | none => rw [hi] at h; cases h
      | some d =>
        cases hr : flatOwnParams V es with
        | none => rw [hi, hr] at h; cases h
        | some ns =>
          rw [hi, hr] at h
          simp only [Option.some.injEq] at h
          subst h
          rcases List.mem_cons.mp hn with rfl | hn'
          · exact ⟨e₀, List.mem_cons_self, d, hi, rfl⟩
          · obtain ⟨e, he, d', hd', hnp⟩ := flatOwnParams_mem hr n hn'
            exact ⟨e, List.mem_cons_of_mem _ he, d', hd', hnp⟩

/-- **The primary block of a non-empty record whose first recursor is over an inductive type is
that type's block**, whatever the fallback block. -/
theorem primaryAt_of_major (htwf : t.wf = true) {rb : _root_.Address} {crb : Ixon.Constant}
    {rs : Array Ixon.MutConst} {r0 : Ixon.Recursor} (h0 : rs[0]? = some (Ixon.MutConst.recr r0))
    {ty d : KExpr} {a : _root_.Address} {ls : List KLevel} {i : IndInfo}
    (hty : loadedAt t (fun x => E.blobs.get? x) crb (blockSelf t rb rs) r0.lvls.toNat
      (mutsRoot rs 0) r0.typ = some ty)
    (hd : binderDomAfter (r0.params.toNat + r0.motives.toNat + r0.minors.toNat +
      r0.indices.toNat) ty = some d)
    (hfn : Ix.Kernel.Expr.getAppFn d = .const (keyOf t a) ls)
    (hi : indInfoAt E a = some (some i)) (B : _root_.Address) :
    primaryAt t E rb crb rs B = some i.blk := by
  have hmaj : majorAt t E rb crb rs 0 =
      some (d, r0.motives.toNat + r0.minors.toNat + r0.indices.toNat) := by
    simp only [majorAt, h0, hty, hd]
  simp only [primaryAt, h0, hmaj, hfn, constOf, keyAddr_keyOf htwf, hi]

/-- **The flattened family a non-empty record reads does not depend on the fallback block**,
where the first recursor's major premise is over the first entry, an inductive type. -/
theorem recordFlatAt_fallback (htwf : t.wf = true) {rb : _root_.Address} {crb : Ixon.Constant}
    {rs : Array Ixon.MutConst} {es : List FlatEntry} (hflat : RecordFlat t E rb crb rs es)
    (hind : AllInd (ReconView.ofStore t E) es) {r0 : Ixon.Recursor} {e0 : FlatEntry}
    (h0 : rs[0]? = some (Ixon.MutConst.recr r0)) (he0 : es[0]? = some e0) (off : Nat)
    (B B' : _root_.Address) :
    recordFlatAt t E rb crb rs B' off = recordFlatAt t E rb crb rs B off := by
  obtain ⟨ty, d, hty, hd, hfn, -⟩ := hflat 0 r0 e0 h0 he0
  obtain ⟨dd, hdd⟩ := hind e0 (List.mem_of_getElem? he0)
  have hi := indInfoAt_of_indDataAt (t := t) hdd
  unfold recordFlatAt
  rw [primaryAt_of_major htwf h0 hty hd hfn hi B, primaryAt_of_major htwf h0 hty hd hfn hi B']

end Store

/-! ## What the member check takes of the call -/

/-- **The peer search of a member check lists the record's own recursors**
(`KernelCheck::build_peer_recs` on the flattened family `es`, the record's block address and a
recursor's projection address): the addresses returned are `recAddrs rb rs`, for a call whose own
calls are among `root`. -/
def PeerRecsSpec (root : List (Call F)) (t : Ix.Kernel.RoleTable) (es : List FlatEntry)
    (rb : _root_.Address) (rs : Array Ixon.MutConst) : Prop :=
  ∀ {x_flat x_rb x_addr v : SourceValue F} {m m' : Heap F} {cs : List (Call F)}
    {bR aRec : Bytes.Address} {k : Nat},
    ObsFn W "KernelCheck::build_peer_recs" [x_flat, x_rb, x_addr] m v m' cs →
    IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
    RepList flatListEnum (FlatEntryRepExact (keyOf t)) m es x_flat →
    Bytes.RepAddressRef addrTy m bR x_rb → ixAddr bR = rb →
    Bytes.RepAddressRef addrTy m aRec x_addr → ixAddr aRec = IxVM.Refinement.Core.rprjAddr rb k →
    k < rs.size →
    ∃ as : List Bytes.Address,
      RepList addrListEnum (Bytes.RepAddressRef addrTy) m' as v ∧
        as.map ixAddr = recAddrs rb rs

/-- **The minor premises a member check builds are fewer than `2^39`**: the list
`KernelCheck::build_all_minors` returns, for a call whose own calls are among `root`. (In
`canonical_rules_at_pos` the list is the argument of a later `Lists::length`, which bounds it in
a bounded run.) -/
def MinorsListSmall (root : List (Call F)) : Prop :=
  ∀ {args : List (SourceValue F)} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
    ObsFn W "KernelCheck::build_all_minors" args h r h' cs → (∀ c ∈ cs, c ∈ root) →
    ∀ ms : List Unit, RepList kexprListEnum (fun _ _ _ => True) h' ms r → ms.length < 2 ^ 39

/-! ## One member check, at its position -/

section Member

variable {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}

/-- **An observed `KernelCheck::check_recursor_canonical_at` under a group's validation, on
recursor `k` of a family record**, gives what `memberRecon_of_canonical` asks of the recursor:
its declared type is the reconstructed type at `k`, and every stored rule follows the
reconstructed body, with the record's own recursors as the peers. The callee specifications of
`check_recursor_canonical_at_spec` are the proved ones (`build_flat_block_spec`,
`build_flat_own_params_spec`, the two readers of an auxiliary's parameters and levels,
`build_rec_type_spec`, `build_all_minors_spec`, `rules_at_pos_spec`), at the store's readings
answered among `root`.

The arguments are represented: the recursor's type exactly, as its canonical reading, whose major
premise's head cell is the parent address (`MajorConst`, at the heap of the parent's load); the
record's block address; the recursor's projection address; the stored rules; and the parent's
payload is the load of the parent address. -/
theorem canonical_of_call (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlvR : RecLevelsDefined t E₀ rb crb rs)
    {root : List (Call F)} (hrc : ∀ c ∈ root, c ∈ calls)
    (hD : DefnAnswers root (keyOf t) (ReconView.ofStore t E₀))
    (hI : IndAnswers root (keyOf t) (ReconView.ofStore t E₀))
    (hC : CtorOfAnswers root (ReconView.ofStore t E₀))
    (hM : ModeledAnswers root (ReconView.ofStore t E₀))
    (hCt : CtorAnswers root (keyOf t) (ReconView.ofStore t E₀))
    (hCa : CtorAddrAnswers root (keyOf t) (ReconView.ofStore t E₀))
    {NF : _root_.Address → Nat → Nat → Nat → Prop}
    (hP : CprjAnswers root (keyOf t) (ReconView.ofStore t E₀) NF)
    {es : List FlatEntry} {off : Nat} (hoff : off ≤ 1) (hdist : FlatDistinct es)
    (hind : AllInd (ReconView.ofStore t E₀) es) (hcov : es.length = rs.size)
    (hesS : es.length < 8589934592)
    (hmodel : ∀ P, recordFlatAt t E₀ rb crb rs P off = some es)
    (hlvlFit : ∀ (B' P : _root_.Address) (cP : Ixon.Constant) (mP : Array Ixon.MutConst)
      (j : Nat) (ind : Ixon.Inductive), primaryAt t E₀ rb crb rs B' = some P →
      recordOf E₀ P = some cP → cP.info = .muts mP → mP[j]? = some (Ixon.MutConst.indc ind) →
      off + ind.lvls.toNat < 4294967296)
    (peer : PeerRecsSpec root t es rb rs) (hminors : MinorsListSmall root)
    (hindSmall : ∀ e ∈ es, ∀ d, (ReconView.ofStore t E₀).ind e.addr = some (some d) →
      d.np < 4294967296 ∧ d.ni < 4294967296)
    (hauxNp : ∀ e ∈ es, e.aux = true → ∀ d,
      (ReconView.ofStore t E₀).ind e.addr = some (some d) → e.params.length = d.np)
    {k : Nat} {rc : Ixon.Recursor} {e : FlatEntry}
    (hrk : rs[k]? = some (Ixon.MutConst.recr rc)) (hek : es[k]? = some e)
    (hnl : rc.lvls.toNat < 4294967296) (hnP : rc.params.toNat < 4294967296)
    (hnMot : rc.motives.toNat < 4294967296) (hnMin : rc.minors.toNat < 4294967296)
    (hnI : rc.indices.toNat < 72057594037927936)
    (hfitP : ∀ e ∈ es, ParamsFit (ReconView.ofStore t E₀) rc.params.toNat e)
    (hfitC : ∀ e ∈ es, ∀ d, (ReconView.ofStore t E₀).ind e.addr = some (some d) → ∀ c cty np,
      (ReconView.ofStore t E₀).ctor d.blk d.idx c = some (cty, np) →
      CtorFits (ReconView.ofStore t E₀) rc.params.toNat e.aux e.params e.levels cty np)
    (hteleS : ∀ d, (ReconView.ofStore t E₀).ind e.addr = some (some d) → ∀ c cty np,
      c < d.nctors → (ReconView.ofStore t E₀).ctor d.blk d.idx c = some (cty, np) →
      CtorTeleSmall (ReconView.ofStore t E₀) cty np e.levels e.aux e.params)
    {ty d0 : KExpr}
    (hdom : binderDomAfter (rc.params.toNat + rc.motives.toNat + rc.minors.toNat +
      rc.indices.toNat) ty = some d0)
    (hfn : Ix.Kernel.Expr.getAppFn d0 = .const (keyOf t e.addr) e.levels)
    (hpar : e.aux = true →
      ((Ix.Kernel.Expr.getAppArgs d0).take e.params.length).map
        (Ix.Kernel.Expr.lowerBVars (rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) 0) =
        e.params)
    {x_rc x_ty x_rules x_k x_uns x_rb x_idx x_addr x_par x_bnl x_form parCi r xm xls pp :
      SourceValue F} {hp h h' : Heap F} {cs csp : List (Call F)}
    (ev : ObsFn W "KernelCheck::check_recursor_canonical_at"
      [x_rc,
        .construct "KernelTypes::KConstantInfo" "Rec"
          [.field (rc.lvls.toNat : F), x_ty, .field (rc.params.toNat : F),
            .field (rc.indices.toNat : F), .field (rc.motives.toNat : F),
            .field (rc.minors.toNat : F), x_rules, x_k, x_uns, x_rb, x_idx],
        x_addr, parCi, x_par, .field (off : F), x_bnl, x_form] h r h' cs)
    (hcs : ∀ c ∈ cs, c ∈ root)
    (htyP : TmOExact (keyOf t) hp ty x_ty)
    (hMajP : MajorConst hp x_ty (rc.params.toNat + rc.motives.toNat + rc.minors.toNat +
      rc.indices.toNat) xm x_par xls)
    {bR aRec : Bytes.Address}
    (hrb : Bytes.RepAddressRef addrTy h bR x_rb) (hbR : ixAddr bR = rb)
    (haddr : Bytes.RepAddressRef addrTy h aRec x_addr)
    (haRec : ixAddr aRec = IxVM.Refinement.Core.rprjAddr rb k)
    (evPar : ObsFn W "Ingress::get_ci" [x_par] hp pp h csp)
    (hmemPar : (⟨"Ingress::get_ci", [x_par], hp⟩ : Call F) ∈ root)
    (hsubPar : ∀ c ∈ csp, c ∈ root) (ldPar : loadValue h pp = .ok parCi)
    {stored : List (Nat × Nat × KExpr)}
    (hstored : RepList krrListEnum (StoredRuleRep (keyOf t)) h stored x_rules)
    (hval : ∀ {m m' : Heap F} {v : SourceValue F} {cs' : List (Call F)},
      ObsFn W "KernelRoles::rc_validates_group" [x_rc] m v m' cs' → Heap.Extends h m →
      v = .field 1) :
    ∃ (cbk : Nat) (bodies : List KExpr),
      (Eventually fun f =>
        recTypeAt (ReconView.ofStore t E₀) f es off rc.params.toNat k = some ty) ∧
      ctorsBefore (ReconView.ofStore t E₀) es k = some cbk ∧
      (Eventually fun f =>
        ruleBodiesAt (ReconView.ofStore t E₀) f es off rc.params.toNat rc.motives.toNat
          rc.minors.toNat rc.lvls.toNat k (recAddrs rb rs) = some bodies) ∧
      ∀ (c : Nat) (ru : Nat × Nat × KExpr), stored[c]? = some ru →
        ∃ cb, bodies[c]? = some cb ∧
          RuleFollows ty rc.params.toNat rc.motives.toNat rc.minors.toNat (cbk + c) ru.2.1
            (elimLevel off) ru.2.2 cb := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hinj : Function.Injective (keyOf t) := keyOf_injective' htwf
  have hA := addrOf_ofStore htwf E₀
  have hK : ∀ a, (ReconView.ofStore t E₀).key a = keyOf t a := fun _ => rfl
  have extP : Heap.Extends hp h := evPar.heap_extends
  have hklt : k < es.length := (List.getElem?_eq_some_iff.mp hek).1
  have hemem : e ∈ es := List.mem_of_getElem? hek
  have hN : rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat <
      288230376151711744 := by omega
  -- the major premise names the entry
  obtain ⟨d1, apar, ls1, As, hdom1, hd1, -, rapar, rls⟩ := hMajP.sem htyP
  have hdd : d1 = d0 := Option.some.inj (hdom1.symm.trans hdom)
  subst hdd
  have hfn1 : Ix.Kernel.Expr.getAppFn d1 = .const (keyOf t (ixAddr apar)) ls1 := by
    rw [hd1]; exact getAppFn_const_mkAppN _ _ _
  have hce := hfn1.symm.trans hfn
  injection hce with hkk hll
  have hpar_eq : ixAddr apar = e.addr := IxVM.Refinement.Core.keyOf_inj htwf hkk
  -- the parent is the entry's inductive type
  obtain ⟨dI, hdI⟩ := hind e hemem
  have hans := hI rapar evPar hmemPar hsubPar ldPar
  have hparCi : ∃ xnl xty xnp xni xnc xrec xblk xidx, parCi =
      .construct "KernelTypes::KConstantInfo" "Induct"
        [xnl, xty, xnp, xni, xnc, xrec, xblk, xidx] := by
    by_contra hne
    have hnone := hans.2 (fun vs hvs heq => hne (by
      match vs, hvs with
      | [a1, a2, a3, a4, a5, a6, a7, a8], _ => exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, heq⟩))
    rw [hpar_eq, hdI] at hnone
    cases hnone
  obtain ⟨x_pnl, x_pty, x_pnp, x_pni, x_nc, x_w, x_pblk, x_pidx, rfl⟩ := hparCi
  obtain ⟨self, ba, hself, hnl', hnp', hni', hnc', hidx', rfl, hpty, rfl, rfl, rfl, hba, rba,
    rfl⟩ := hans.1 _ _ _ _ _ _ _ _ rfl
  rw [hpar_eq] at hself
  obtain ⟨hselfNp, hselfNi⟩ := hindSmall e hemem self hself
  obtain ⟨cB, mB, indB, hcB, hmB, hindB⟩ := indDataAt_block (t := t) (E := E₀) hself
  have hne_blk : bR ≠ ba := by
    intro heq
    subst heq
    rw [← hba, hbR] at hcB
    have e1 : cB = crb := Option.some.inj (hcB.symm.trans hR.record)
    subst e1
    have e2 : mB = rs := Ixon.ConstantInfo.muts.inj (hmB.symm.trans hR.muts)
    subst e2
    obtain ⟨r', hr'⟩ := hR.recrs _
      (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hindB))
    cases hr'
  have hfopS : ∀ {fop : List Nat}, flatOwnParams (ReconView.ofStore t E₀) es = some fop →
      ∀ n ∈ fop, n < 4294967296 := by
    intro fop hfop n hn
    obtain ⟨e', he', d', hd', rfl⟩ := flatOwnParams_mem hfop n hn
    exact (hindSmall e' he' d' hd').1
  have hminorsRes : ∀ {args : List (SourceValue F)} {v : SourceValue F} {m m' : Heap F}
      {cs' : List (Call F)},
      ObsFn W "KernelCheck::build_all_minors" args m v m' cs' → (∀ c ∈ cs', c ∈ root) →
      ∀ ms : List Unit, RepList kexprListEnum (fun _ _ _ => True) m' ms v →
        rc.params.toNat + es.length + ms.length < 1099511627776 := by
    intro args v m m' cs' evm sub ms hms
    have := hminors evm sub ms hms
    omega
  obtain ⟨-, fop, Ms, cbk, bodies, hfop, hMot, hMin, hMsE, hRec, hcbk, hbod, -, hfol⟩ :=
    check_recursor_canonical_at_spec (κ := keyOf t) hinj (V := ReconView.ofStore t E₀) hdist
      (off := off) (nP := rc.params.toNat) (nI := rc.indices.toNat)
      (nMot := rc.motives.toNat) (nMin := rc.minors.toNat) (nl := rc.lvls.toNat) (k := k) hek
      (ty := ty) (peers := recAddrs rb rs) (stored := stored) (self := self) (ba := ba)
      (NF := NF) (arb := bR) (apb := ba) (apar := apar) (root := root) ev
      (RomBound.bounded_mono hbd (fun c hc => hrc c (hcs c hc))) hcs hoff hnl hnMot hnMin
      (htyP.mono extP) (Bytes.repAddressRef_heapMono₂ addrTy extP rapar) hpar_eq hrb rba
      (fun _ => hne_blk) hval
      (fun _ {m m' x v cs'} hx evm ext sub => by
        rcases hx with rfl | rfl
        · exact is_muts_block_of_muts hS (Bytes.repAddressRef_heapMono₂ addrTy ext hrb)
            (by rw [hbR]; exact hR.record) hR.muts evm (fun c hc => hrc c (sub c hc))
        · exact is_muts_block_of_muts hS (Bytes.repAddressRef_heapMono₂ addrTy ext rba)
            (by rw [hba]; exact hcB) hmB evm (fun c hc => hrc c (sub c hc)))
      (fun {m m' v cs'} evf ext b sub => by
        obtain ⟨-, P, as, os, es', xs, -, -, -, -, hmod, -, -, hrep⟩ :=
          build_flat_block_spec ht hbd hS hH hR hlvR hbR (by rw [hba]; exact hcB) hmB
            (fun P cP mP j ind hP => hlvlFit _ P cP mP j ind hP)
            (Bytes.repAddressRef_heapMono₂ addrTy ext hrb)
            (Bytes.repAddressRef_heapMono₂ addrTy ext rba) evf (fun c hc => hrc c (sub c hc))
        have hes : es' = es := Option.some.inj (hmod.symm.trans (hmodel _))
        subst hes
        exact hrep)
      (fun {m m' v x_flat cs'} evp ext b sub hfl =>
        peer evp b sub hfl (Bytes.repAddressRef_heapMono₂ addrTy ext hrb) hbR
          (Bytes.repAddressRef_heapMono₂ addrTy ext haddr) haRec
          (by rw [← hcov]; exact hklt))
      (fun {m m' v x_flat cs'} evo ext b sub hfl =>
        build_flat_own_params_spec hI es hind evo b sub hfl)
      (fun {m m' v cs'} evs ext b sub => by
        obtain ⟨-, d2, ys, hd2, hys, hrep⟩ :=
          extract_aux_spec_params_from_rec_spec (κ := keyOf t) (root := root) hN (by omega)
            (hMajP.mono (extP.trans ext)) (htyP.mono (extP.trans ext)) evs b sub
        refine ⟨ys, hrep, fun haux => ?_⟩
        have hdd : d2 = d1 := Option.some.inj (hd2.symm.trans hdom1)
        subst hdd
        rw [occParamsLower_eq _ _ _ hys, ← hauxNp e hemem haux self hself]
        exact hpar haux)
      (fun {m m' v cs'} evu ext b sub => by
        obtain ⟨rfl, ext'⟩ := extract_aux_occ_us_spec hN (hMajP.mono (extP.trans ext)) evu
        exact ⟨ls1, rls.mono ((extP.trans ext).trans ext'), fun _ => hll⟩)
      (fun {m m' v x_flat x_peers x_fop x_lvls x_elim cs' fop} evt a b sub =>
        build_rec_type_spec hA hD hI hC hM hK hnP hselfNi hoff hklt
          (fun e' _ => resolved_keyOf t e'.addr) hind hfitP
          (fun ek d hek' hd' => by
            have e1 : ek = e := Option.some.inj (hek'.symm.trans hek)
            subst e1
            have e2 : d = self := Option.some.inj (Option.some.inj (hd'.symm.trans hself))
            rw [e2])
          a.fopEq
          (fun {xrc xflat xfop xelim r' m₁ m₁' cs₁} evm b' sub' hfl hfo hel =>
            (build_all_minors_spec hinj hA hD hI hC hM hCt hCa (Nat.le_refl _)
              (hfopS a.fopEq) hind hfitC evm b' sub' hfl hfo hel
              (hminorsRes evm sub')).2)
          evt b sub a.flat a.fop a.elim)
      (fun {m m' v x_flat x_peers x_fop x_lvls x_elim cs' fop} evm a b sub =>
        build_all_minors_spec hinj hA hD hI hC hM hCt hCa (Nat.le_refl _)
          (hfopS a.fopEq) hind hfitC evm b sub a.flat a.fop a.elim (hminorsRes evm sub))
      (fun {h₀ h₁ h₂ h₃ vcb vcanon v w x_aux x_sp x_ou x_flat x_peers x_fop x_lvls x_elim cs₁
          cs₂ cs₃ fop} Ms evcb evpop evcmp ext0 a b2 b3 s1 s2 s3 hrepE hMotE hMinE hMsEv => by
        obtain ⟨_, rfl, _, _, hsp, hus⟩ := FlatEntryRepExact.tuple_inv hrepE
        obtain ⟨as, has, hmap⟩ := a.peers
        obtain ⟨f0, hf0⟩ := hMsEv
        have hm := rules_minors_of_allMinors (hf0 f0 (Nat.le_refl _)) hek hself
        have ext02 : Heap.Extends h₀ h₂ := evcb.heap_extends.trans evpop.heap_extends
        have hpeers : as.length = es.length := by
          have hl := congrArg List.length hmap
          simp only [List.length_map, recAddrs, List.length_zipIdx, Array.length_toList] at hl
          omega
        have hres := rules_at_pos_spec hinj hA hD hI hC hM hK (resolved_keyOf t) hP hek
          hself hba.symm a.fopEq (by omega) (by omega) hnc' hidx' hpeers
          (fun n hn => by have := hfopS a.fopEq n hn; omega)
          (fun cbk hc => by rw [hMinE]; exact hm.2 cbk hc)
          (fun c hc => by rw [hba]; exact hm.1 c hc)
          (fun c cty np hc hct => hteleS self hself c cty np hc (by rw [← hba]; exact hct))
          (stored := stored) (off := off) (nl := rc.lvls.toNat) (ty := ty)
          evcb evpop evcmp b2 b3 s1 s2 s3 a.flat
          (Bytes.repAddressRef_heapMono₂ addrTy ext0 rba) hus a.lvls has a.fop hsp a.elim
          (repList_heapMono₂ _ storedRuleRep_heapMono₂ (ext0.trans ext02) hstored)
          ((htyP.mono extP).mono (ext0.trans ext02))
        rw [hmap] at hres
        exact hres)
  exact ⟨cbk, bodies, hRec, hcbk, hbod, fun c ru hru => (hfol c ru hru).2.2.2⟩

/-- **The right-hand sides of a family record's rules mention only their recursor's level
parameters**: the reading of rule `c` of recursor `k` over the store's blobs mentions no level
parameter at or above the recursor's level count (`KernelModeled::check_rules` validates each
right-hand side's scoping). -/
def RuleLevelsDefined (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (rb : _root_.Address)
    (crb : Ixon.Constant) (rs : Array Ixon.MutConst) : Prop :=
  ∀ (k : Nat) (rc : Ixon.Recursor) (ru : Ixon.RecursorRule) (v : KExpr),
    rs[k]? = some (Ixon.MutConst.recr rc) → ru ∈ rc.rules.toList →
    (exprReader t (fun x => E.blobs.get? x) crb id (blockSelf t rb rs)).read ru.rhs = .ok v →
    v.allLevelParamsDefined (List.range rc.lvls.toNat) = true

/-- **What the reconstruction takes of the entries and of the record's counts**, at the store's
readings: the counts the circuit compares in the field are below `2^32` (`counts`, `indSmall`);
an auxiliary entry is taken at all its type's parameters (`auxNp`); every entry's parameters and
every constructor fit a recursor over the record's parameter count (`paramsFit`, `ctorFits`); the
constructors' telescopes are short (`teleSmall`); and the levels of the primary block's types fit
at the offset (`lvlFit`). -/
structure ReconSide (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (rb : _root_.Address)
    (crb : Ixon.Constant) (rs : Array Ixon.MutConst) (es : List FlatEntry) (off : Nat) :
    Prop where
  counts : ∀ (k : Nat) (rc : Ixon.Recursor), rs[k]? = some (Ixon.MutConst.recr rc) →
    rc.params.toNat < 4294967296 ∧ rc.motives.toNat < 4294967296 ∧
      rc.minors.toNat < 4294967296
  indSmall : ∀ e ∈ es, ∀ d, (ReconView.ofStore t E).ind e.addr = some (some d) →
    d.np < 4294967296 ∧ d.ni < 4294967296
  auxNp : ∀ e ∈ es, e.aux = true → ∀ d,
    (ReconView.ofStore t E).ind e.addr = some (some d) → e.params.length = d.np
  paramsFit : ∀ (k : Nat) (rc : Ixon.Recursor), rs[k]? = some (Ixon.MutConst.recr rc) →
    ∀ e ∈ es, ParamsFit (ReconView.ofStore t E) rc.params.toNat e
  ctorFits : ∀ (k : Nat) (rc : Ixon.Recursor), rs[k]? = some (Ixon.MutConst.recr rc) →
    ∀ e ∈ es, ∀ d, (ReconView.ofStore t E).ind e.addr = some (some d) → ∀ c cty np,
      (ReconView.ofStore t E).ctor d.blk d.idx c = some (cty, np) →
      CtorFits (ReconView.ofStore t E) rc.params.toNat e.aux e.params e.levels cty np
  teleSmall : ∀ e ∈ es, ∀ d, (ReconView.ofStore t E).ind e.addr = some (some d) → ∀ c cty np,
    c < d.nctors → (ReconView.ofStore t E).ctor d.blk d.idx c = some (cty, np) →
    CtorTeleSmall (ReconView.ofStore t E) cty np e.levels e.aux e.params
  lvlFit : ∀ (B' P : _root_.Address) (cP : Ixon.Constant) (mP : Array Ixon.MutConst)
    (j : Nat) (ind : Ixon.Inductive), primaryAt t E rb crb rs B' = some P →
    recordOf E P = some cP → cP.info = .muts mP → mP[j]? = some (Ixon.MutConst.indc ind) →
    off + ind.lvls.toNat < 4294967296

/-- The spine of a converted rule list. -/
theorem rulesTrace_shape {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {tree : L1.BinderTreeData} {h : Heap F} {j : Nat} {root : F}
    {rus : List Ixon.RecursorRule} {p : SourceValue F}
    (tr : L1.RulesTraceRep refs recurAddrs univs sharing blobs tree h j root rus p) :
    RepList krrListEnum
      (fun (_ : Heap F) (_ : Ixon.RecursorRule) (_ : SourceValue F) => True) h rus p := by
  induction tr with
  | nil cell => exact .nil cell
  | cons cell _ _ _ _ _ ih => exact .cons cell trivial ih

/-- **One iteration of `KernelModeled::check_recs` under a group's validation, on recursor `k`
of the family record, gives `MemberRecon` at `k`**: the iteration's load of the recursor
represents its type and its rules as their canonical readings, its `rec_to_parent_addr` reaches
the constant cell heading the major premise, which `RecordFlat` reads as entry `k`'s, and its
`check_recursor_canonical_at` is then the member check at `k` (`canonical_of_call`,
`memberRecon_of_canonical`). -/
theorem memberRecon_of_cons (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlvR : RecLevelsDefined t E₀ rb crb rs)
    (hrlv : RuleLevelsDefined t E₀ rb crb rs)
    {root : List (Call F)} (hrc : ∀ c ∈ root, c ∈ calls)
    (hD : DefnAnswers root (keyOf t) (ReconView.ofStore t E₀))
    (hI : IndAnswers root (keyOf t) (ReconView.ofStore t E₀))
    (hC : CtorOfAnswers root (ReconView.ofStore t E₀))
    (hM : ModeledAnswers root (ReconView.ofStore t E₀))
    (hCt : CtorAnswers root (keyOf t) (ReconView.ofStore t E₀))
    (hCa : CtorAddrAnswers root (keyOf t) (ReconView.ofStore t E₀))
    {NF : _root_.Address → Nat → Nat → Nat → Prop}
    (hP : CprjAnswers root (keyOf t) (ReconView.ofStore t E₀) NF)
    {es : List FlatEntry} {off : Nat} (hoff : off ≤ 1) (hdist : FlatDistinct es)
    (hind : AllInd (ReconView.ofStore t E₀) es) (hcov : es.length = rs.size)
    (hesS : es.length < 8589934592)
    (hflat : RecordFlat t E₀ rb crb rs es)
    (hmodel : ∀ P, recordFlatAt t E₀ rb crb rs P off = some es)
    (peer : PeerRecsSpec root t es rb rs) (hminors : MinorsListSmall root)
    (side : ReconSide t E₀ rb crb rs es off)
    {rcV tys recs models src dst aset s n kV np bnl fam form r : SourceValue F}
    {h h' : Heap F} {cs_rec : List (Call F)} (hsub : ∀ c ∈ cs_rec, c ∈ root)
    (C : FamilyAlias.CheckRecsCons rcV tys recs models src dst aset s n kV np (.field (off : F))
      bnl fam form r h h' cs_rec)
    {k : Nat} {rc : Ixon.Recursor} {aRec : Bytes.Address}
    (hk_u64 : k < UInt64.size) (hrk : rs[k]? = some (Ixon.MutConst.recr rc))
    (haRec_eq : ixAddr aRec = IxVM.Refinement.Core.rprjAddr rb k)
    (haRec_rep : Bytes.RepAddressRef addrTy h aRec C.x)
    (hval : ∀ {m m' : Heap F} {v : SourceValue F} {cs' : List (Call F)},
      ObsFn W "KernelRoles::rc_validates_group" [rcV] m v m' cs' → Heap.Extends h m →
      v = .field 1) :
    ∃ fuel, MemberRecon ExprLvEq t E₀ rb crb rs es off fuel k rc := by
  have hsubC : FamilyAlias.CallSub cs_rec calls := fun c hc => hrc c (hsub c hc)
  have hklt : k < rs.size := (Array.getElem?_eq_some_iff.mp hrk).1
  obtain ⟨e, hek⟩ : ∃ e, es[k]? = some e :=
    ⟨es[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  have hsub_getRec : FamilyAlias.CallSub C.evGetRec.cs calls :=
    fun cl hcl => hsubC cl (C.evGetRec.sub cl hcl)
  obtain ⟨_, cRec, hhRec, hbaRec, hexRec, -, htrRec⟩ :=
    L1.get_ci_block_trace_spec (RomBound.bounded_mono hbd hsub_getRec) haRec_rep C.evGetRec.obs
  have hrecAtRec : Ix.Cert.recordAt E₀ (ixAddr aRec) =
      some (memberProjection rb k (.recr rc)) := by
    rw [← hS.recordOf_eq_recordAt, haRec_eq, ← LoadedReads.memberAddr_recr]
    exact hR.members k (.recr rc) hrk
  have hcRec_eq : cRec = memberProjection rb k (.recr rc) :=
    hS.record_eq hrecAtRec (IxVM.Refinement.Core.hashed_mono hsub_getRec hhRec) hbaRec hexRec
  subst hcRec_eq
  unfold L1.GetCIBlockTraceResult at htrRec
  simp only [memberProjection] at htrRec
  obtain ⟨_, _, crb', rs', rc', blobs, tree, vRec, hhBlk, hbaBlk, hexBlk, hmuts', hrk', hhp,
      built, hldv, hrepRec⟩ := htrRec
  have hcrb_eq : crb' = crb :=
    hS.record_eq ((hS.recordOf_eq_recordAt rb).symm.trans hR.record)
      (IxVM.Refinement.Core.hashed_mono hsub_getRec hhBlk) hbaBlk hexBlk
  subst crb'
  have hrs_eq : rs' = rs := Ixon.ConstantInfo.muts.inj (hmuts'.symm.trans hR.muts)
  subst rs'
  have hk_toNat : k.toUInt64.toNat = k := toUInt64_toNat_of_lt hk_u64
  rw [hk_toNat, Array.getElem?_toList, hrk] at hrk'
  have hrc_eq : rc' = rc := Ixon.MutConst.recr.inj (Option.some.inj hrk').symm
  subst rc'
  rw [hk_toNat] at hrepRec
  obtain ⟨hlvls_lt, hnp_lt, hni_lt, hnmot_lt, hnmin_lt, hk_lt, tyPtr, rulesPtr, blkPtr, bBlk,
      planT, hbBlk_eq, hbBlk_ref, hvRec_eq, rty, hpT, hlT, hrlsTrace⟩ := hrepRec
  have hvRec_ld := Except.ok.inj (C.ldRec.symm.trans hldv)
  rw [hvRec_eq] at hvRec_ld
  injection hvRec_ld with _ _ hargs_r
  injection hargs_r with hnl_eq hargs_r
  injection hargs_r with hty_eq hargs_r
  injection hargs_r with hnp_eq hargs_r
  injection hargs_r with hni_eq hargs_r
  injection hargs_r with hn_eq hargs_r
  injection hargs_r with hnmin_eq hargs_r
  injection hargs_r with hrules_eq hargs_r
  injection hargs_r with hkf_eq hargs_r
  injection hargs_r with huns_eq hargs_r
  injection hargs_r with hblk_eq hargs_r
  subst hnp_eq hn_eq
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hrun := hS.blobs bs (IxVM.Refinement.Core.hashed_mono hsub_getRec hhx)
    rwa [hxa] at hrun
  -- the type, as its canonical reading
  obtain ⟨tyA, hloaded, htm⟩ := loadedAt_tmOExact (t := t) (blob := fun x => E₀.blobs.get? x)
    (self := blockSelf t rb rs) (recurAddrs := []) ht hlvls_lt
    (fun _ _ _ _ hx => by simp at hx) (fun _ _ hx => by simp at hx) hblob rty built hpT hlT
    (fun v hv => hlvR k rc v hrk hv)
  rw [← hty_eq] at htm
  -- the heaps of the iteration
  have ext_67_669 : Heap.Extends C.m67 C.m669 := by
    have e1 : Heap.Extends C.m561 C.mNil1 := by rw [C.hNil1]; exact Heap.Extends.snoc _ _
    have e2 : Heap.Extends C.mRen C.mNil2 := by rw [C.hNil2]; exact Heap.Extends.snoc _ _
    have e3 : Heap.Extends C.mLP C.mNilSort := by rw [C.hNilSort]; exact Heap.Extends.snoc _ _
    exact C.ext391.trans (C.evCarriers.extends.trans (C.evScope.extends.trans
      (C.evNoMent.extends.trans (e1.trans (C.evPeel1.extends.trans (C.evRen.extends.trans
        (e2.trans (C.evPeel2.extends.trans (C.evParamEq.extends.trans (C.evPins.extends.trans
          (C.evLowerPins.extends.trans (e3.trans (C.evSort.extends.trans C.ext669)))))))))))))
  have ext_67_698 : Heap.Extends C.m67 C.m698 := ext_67_669.trans C.evParent.extends
  have ext_67_par : Heap.Extends C.m67 C.mPar := ext_67_698.trans C.evGetParent.extends
  have ext_par_838 : Heap.Extends C.mPar C.m838 :=
    C.evCanon.extends.trans C.evHeaderLets.extends
  -- the stored rules, as their canonical readings
  have hrlsTrace' : L1.RulesTraceRep crb.refs.toList (L1.blockRecurAddrs rb rs.toList)
      crb.univs.toList crb.sharing.toList blobs tree C.m67 0 (mutsRoot rs k + 1)
      rc.rules.toList C.rules := by
    rw [← hrules_eq] at hrlsTrace; exact hrlsTrace
  have hrulesLen : rc.rules.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbd (hsubC _ C.evRules.mem) (by simp)
      (rulesTrace_shape (hrlsTrace'.mono (ext_67_par.trans ext_par_838) (fun _ hq => hq)))
  obtain ⟨stored, hst, hall⟩ := storedRules_of_trace (t := t) ht
    (blob := fun x => E₀.blobs.get? x) (src := crb) (self := blockSelf t rb rs)
    (recurAddrs := L1.blockRecurAddrs rb rs.toList) (n := rc.lvls.toNat) hlvls_lt
    (LoadedReads.blockSelf_key t rb rs) (LoadedReads.blockSelf_ok t rb rs) hblob built
    rc.rules.toList 0 (mutsRoot rs k + 1) hrlsTrace' (by omega)
    (fun ru hru v hv => hrlv k rc ru v hrk hru hv)
  -- the major premise
  obtain ⟨ty', d0, hty', hdom, hfn, hpar⟩ := hflat k rc e hrk hek
  have hte : ty' = tyA := Option.some.inj (hty'.symm.trans hloaded)
  subst hte
  have evPar' : ObsFn W "KernelCheck::rec_to_parent_addr"
      [C.ty, .field (rc.params.toNat : F), .field (rc.motives.toNat : F),
        .field (rc.minors.toNat : F), .field (rc.indices.toNat : F)]
      C.m669 C.parAddr C.m698 C.evParent.cs := by
    rw [← hnmin_eq, ← hni_eq]; exact C.evParent.obs
  obtain ⟨-, xm, xls, hMaj⟩ := rec_to_parent_addr_major (by omega) evPar'
  -- the member check
  have evCan : ObsFn W "KernelCheck::check_recursor_canonical_at"
      [rcV,
        .construct "KernelTypes::KConstantInfo" "Rec"
          [.field (rc.lvls.toNat : F), C.ty, .field (rc.params.toNat : F),
            .field (rc.indices.toNat : F), .field (rc.motives.toNat : F),
            .field (rc.minors.toNat : F), C.rules, .field 0, .field 0, C.blk, C.idx],
        C.x, C.parCi, C.parAddr, .field (off : F), bnl, form] C.mPar C.form' C.mCan
      C.evCanon.cs := by
    rw [← hnl_eq, ← hni_eq, ← hnmin_eq]; exact C.evCanon.obs
  obtain ⟨hcnP, hcnMot, hcnMin⟩ := side.counts k rc hrk
  have hcanon := canonical_of_call ht hbd hS hH hR hlvR hrc hD hI hC hM hCt hCa hP hoff hdist
    hind hcov hesS hmodel side.lvlFit peer hminors side.indSmall side.auxNp hrk hek hlvls_lt
    hcnP hcnMot hcnMin hni_lt (side.paramsFit k rc hrk) (side.ctorFits k rc hrk)
    (side.teleSmall e (List.mem_of_getElem? hek)) hdom hfn hpar evCan
    (fun c hc => hsub c (C.evCanon.sub c hc)) (htm.mono ext_67_698) hMaj
    (by rw [hblk_eq]; exact Bytes.repAddressRef_heapMono₂ addrTy ext_67_par hbBlk_ref)
    hbBlk_eq
    (Bytes.repAddressRef_heapMono₂ addrTy (C.evGetRec.extends.trans ext_67_par) haRec_rep)
    haRec_eq C.evGetParent.obs (hsub _ C.evGetParent.mem)
    (fun c hc => hsub c (C.evGetParent.sub c hc)) C.ldParent
    (repList_heapMono₂ _ storedRuleRep_heapMono₂ ext_67_par hst)
    (fun ev' ext => hval ev' ((C.evGetRec.extends.trans ext_67_par).trans ext))
  refine memberRecon_of_canonical hloaded (stored := stored) (fun c ru hru => ?_) hcanon
  obtain ⟨rhs, hld, hs⟩ := hall c ru (by rw [Array.getElem?_toList]; exact hru)
  exact ⟨rhs, 0 + c, hld, hs⟩

/-! ## The store's answers among the calls of a family check -/

/-- **`DefnAnswers` among part of a run's calls**: for a bounded run with its store, the loads
among calls `cs` of the run answer the store's definitions, where the readings at the addresses
`cs` loads mention only their level parameters. -/
theorem defnAnswers_of_sub (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) (hbd : Bounded calls)
    {cs : List (Call F)} (hsub : ∀ c ∈ cs, c ∈ calls) (hlv : LoadedLevelsDefined t E₀ cs) :
    DefnAnswers cs (keyOf t) (ReconView.ofStore t E₀) := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  intro xa p ci h m cs' a ha ev hself hsub' hld
  obtain ⟨X, hX, hsome, hnone⟩ := defnAt_of_load ht hS hH hbd (hlv hself ha) ha ev
    (fun c hc => hsub c (hsub' c hc)) hld
  exact defn_clause_of_defnAt htwf hX hsome hnone

/-- **`IndAnswers` among part of a run's calls** (`indDataAt_of_load`). -/
theorem indAnswers_of_sub (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) (hbd : Bounded calls)
    {cs : List (Call F)} (hsub : ∀ c ∈ cs, c ∈ calls) (hlv : LoadedLevelsDefined t E₀ cs) :
    IndAnswers cs (keyOf t) (ReconView.ofStore t E₀) := by
  intro xa p ci h m cs' a ha ev hself hsub' hld
  exact indDataAt_of_load ht hS hH hbd (hlv hself ha) ha ev (fun c hc => hsub c (hsub' c hc)) hld

/-- **`CtorOfAnswers` among part of a run's calls.** -/
theorem ctorOfAnswers_of_sub (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) (hbd : Bounded calls)
    {cs : List (Call F)} (hsub : ∀ c ∈ cs, c ∈ calls) :
    CtorOfAnswers cs (ReconView.ofStore t E₀) := by
  intro xa p ci h m cs' a ha ev hsub' hld
  exact ctorOfAnswers_of_run (t := t) hS hH hbd ha ev (fun c hc => hsub c (hsub' c hc)) hld

/-! ## The record -/

/-- **The elimination offset a family check hands its members is `off`**: the offset every
`KernelModeled::block_elim` among the calls `cs` returns (`block_elim_blockElim_at` reads it as
the block's `BlockElim` offset, which `BlockDerivedFlat` pins). -/
def ElimOffsetOf (cs : List (Call F)) (off : Nat) : Prop :=
  ∀ {rc xt bnl uo : SourceValue F} {h h' : Heap F} {cs' : List (Call F)},
    ObsFn W "KernelModeled::block_elim" [rc, xt] h (.tuple [bnl, uo]) h' cs' →
    (⟨"KernelModeled::block_elim", [rc, xt], h⟩ : Call F) ∈ cs → uo = .field (off : F)

/-- **The reconstruction form of a family record, from its family check under a group's
validation.** An accepted `KernelModeled::check_family` of the block `B` with the non-empty
family record `r`, at a group limit `n < 77`, leaves the record in the form `RFormS`: over the
flattened family `es` of the record (`RecordFlat`, the list `build_flat_block` reads,
`hmodel`), derived from the block at the offset `off` (`BlockDerivedFlat`), every recursor's
declared type is the reconstructed type at its position and its rules follow the reconstructed
bodies. Every recursor of the record has its iteration of `check_recs`
(`FamilyOfCall.checkRecs_member`), whose member check is read by `memberRecon_of_cons`; the
members' fuels are joined by `recordReconWith_of_members`.

Taken: the record-level conjuncts over `es` and `off` (`hflat`, `hder`, `hmodel`, `hcov`); the
entries differ (`hdist`) and are inductive types of the store (`hind`); the offset the check
hands its members (`huo`); the peer search (`peer`); the store's answers among the check's calls
(`hlv`, `hM`, `hCt`, `hCa`, `hP`); the scoping of the rules' right-hand sides (`hrlv`); the bound
on the minor premises' list (`hminors`); and the fits and bounds of `ReconSide`. -/
theorem rFormS_of_call (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {bAddr B r : _root_.Address} {cb cr : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    {n : Nat} {cs : List (Call F)}
    (hB : FamBlockRecord E₀ B cb ms) (hR : FamRecRecord E₀ r cr rs) (hrs : rs.size ≠ 0)
    (hn : n < 77) (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B r (some n) cs)
    (hlv : LoadedLevelsDefined t E₀ cs)
    (hM : ModeledAnswers cs (ReconView.ofStore t E₀))
    (hCt : CtorAnswers cs (keyOf t) (ReconView.ofStore t E₀))
    (hCa : CtorAddrAnswers cs (keyOf t) (ReconView.ofStore t E₀))
    {NF : _root_.Address → Nat → Nat → Nat → Prop}
    (hP : CprjAnswers cs (keyOf t) (ReconView.ofStore t E₀) NF)
    {es : List FlatEntry} {off : Nat}
    (hflat : RecordFlat t E₀ r cr rs es) (hder : BlockDerivedFlat t E₀ B off es)
    (hmodel : recordFlatAt t E₀ r cr rs B off = some es)
    (hdist : FlatDistinct es) (hind : AllInd (ReconView.ofStore t E₀) es)
    (huo : ElimOffsetOf cs off) (peer : PeerRecsSpec cs t es r rs)
    (hminors : MinorsListSmall cs) (hrlv : RuleLevelsDefined t E₀ r cr rs)
    (side : ReconSide t E₀ r cr rs es off) :
    RFormS t E₀ B r := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hlvR := recLevelsDefined_of_call ht hbd hS hH hfc hR
  have hrsz := familyCall_recs_bound hS hH hfc hR
  have hoff : off ≤ 1 := by
    obtain ⟨⟨_, _, _, _, _, _, lvl, _, _, _, ho⟩, _⟩ := hder
    rw [ho]
    split <;> omega
  obtain ⟨h, h', rcV, xb, xrb, res, hrcRep, ⟨bB, hbB, rfl⟩, ⟨bR, hbR, rfl⟩, ev, -, hsub⟩ := hfc
  have hD : DefnAnswers cs (keyOf t) (ReconView.ofStore t E₀) :=
    defnAnswers_of_sub ht hS hH hbd hsub hlv
  have hI : IndAnswers cs (keyOf t) (ReconView.ofStore t E₀) :=
    indAnswers_of_sub ht hS hH hbd hsub hlv
  have hC : CtorOfAnswers cs (ReconView.ofStore t E₀) := ctorOfAnswers_of_sub hS hH hbd hsub
  obtain ⟨C, ⟨X⟩⟩ := FamilyAlias.checkFamily_flatChain ev
  have ext_0_453 : Heap.Extends h C.m453 :=
    (check_family_seg1_extends C.sg112).trans C.ext_m105_m453
  have ext_501_652 : Heap.Extends C.m501 C.m652 :=
    C.evLenMem.extends.trans (C.evIndcCnt.extends.trans C.evNParams.extends)
  have ext_674_784 : Heap.Extends C.m674 C.m784 :=
    C.evTypeMods.extends.trans (C.evCtors.extends.trans
      (C.evLenCtors.extends.trans C.evCtorMods.extends))
  have ext_0_784 : Heap.Extends h C.m784 :=
    ext_0_453.trans (C.evLoadBlk.extends.trans (ext_501_652.trans
      (C.evTypes.extends.trans ext_674_784)))
  have hbR784 : Bytes.RepAddressRef addrTy C.m784 bR xrb :=
    Bytes.repAddressRef_heapMono₂ addrTy ext_0_784 hbR
  have hsubRecs : ∀ cl ∈ C.evRecs.cs, cl ∈ calls :=
    fun cl hcl => hsub cl (C.evRecs.sub cl hcl)
  obtain ⟨as_rc, has_rc, hmap_rc⟩ :=
    FamilyAlias.family_recs_list hH hbR784 C.evRecs.obs hsubRecs hR
  have ext_840_978 : Heap.Extends C.m840 C.m978 :=
    C.evNoRole.extends.trans (C.evNoTypeRole.extends.trans (C.evLenRecs.extends.trans
      (C.evRecMods.extends.trans (C.evSrcTail.extends.trans (C.evSrc.extends.trans
        (C.evDstTail.extends.trans C.evDst.extends))))))
  have ext_840_1293 : Heap.Extends C.m840 C.m1293 := ext_840_978.trans C.ext_m978_m1293
  have ext_0_1293 : Heap.Extends h C.m1293 :=
    ext_0_784.trans (C.evRecs.extends.trans ext_840_1293)
  have has_rc1293 := repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy)
    ext_840_1293 has_rc
  have huoC : C.uo = .field (off : F) := huo C.evBlockElim.obs C.evBlockElim.mem
  have evCR : ObsFn W "KernelModeled::check_recs"
      [rcV, C.tys, C.recs, C.recM, C.src, C.dst, C.aset, C.s8, C.nRecs, .field 0, C.np,
        .field (off : F), C.bnl, C.recs, .field 0] C.m1293 C.s9 h' C.evCheckRecs.cs := by
    rw [← huoC]; exact C.evCheckRecs.obs
  -- under the group's validation the record has one recursor per entry
  have hcov : es.length = rs.size := by
    have evFlat : ObsFn W "KernelCheck::build_flat_block" [xrb, xb, .field (off : F)] C.m1191
        X.flat X.mFlat X.evFlat.cs := by
      rw [← huoC]; exact X.evFlat.obs
    obtain ⟨-, P, as, os, es', xs, -, -, -, -, hmod, -, -, hrepF⟩ :=
      build_flat_block_spec ht hbd hS hH hR hlvR rfl hB.record hB.muts
        (fun P cP mP j ind hP => side.lvlFit _ P cP mP j ind hP)
        (Bytes.repAddressRef_heapMono₂ addrTy C.ext_in_m1191 hbR)
        (Bytes.repAddressRef_heapMono₂ addrTy C.ext_in_m1191 hbB) evFlat
        (fun c hc => hsub c (X.evFlat.sub c hc))
    have hes : es' = es := Option.some.inj (hmod.symm.trans hmodel)
    subst hes
    have hrepN := flatList_mono X.evNested.extends hrepF
    have hlenF : es'.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbd (hsub _ X.evLenFlat.mem) (by simp) hrepN
    obtain ⟨hnRecs, -⟩ := Decl.addrList_length_spec
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
        (C.evNoRole.extends.trans C.evNoTypeRole.extends) has_rc) C.evLenRecs.obs
    have hrlen : as_rc.length = rs.size := by
      have e := congrArg List.length hmap_rc
      simpa only [List.length_map, List.length_mapIdx, Array.length_toList] using e
    rw [← hrlen]
    exact X.length_eq (X.validates_one hn hrcRep) hnRecs (by omega) hrepN (by omega)
  -- the list the record reads, at every fallback block
  have hpos : 0 < rs.size := Nat.pos_of_ne_zero hrs
  have hm0 : rs[0]? = some rs[0] := Array.getElem?_eq_getElem hpos
  obtain ⟨r0, hr0⟩ := hR.recrs _
    (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hm0))
  rw [hr0] at hm0
  have he0 : es[0]? = some (es[0]'(by omega)) := List.getElem?_eq_getElem (by omega)
  have hmodelAll : ∀ P, recordFlatAt t E₀ (ixAddr bR) cr rs P off = some es := fun P =>
    (recordFlatAt_fallback htwf hflat hind hm0 he0 off (ixAddr bB) P).trans hmodel
  show RecordReconWith ExprLvEq t E₀ (ixAddr bB) (ixAddr bR)
  refine recordReconWith_of_members hR.record hR.muts hflat hder (fun k rc hrk => ?_)
  have hklt : k < rs.size := (Array.getElem?_eq_some_iff.mp hrk).1
  have hkL : rs.toList[k]? = some (.recr rc) := by rw [Array.getElem?_toList]; exact hrk
  have h1 : (as_rc.map ixAddr)[k]? = some (IxVM.Refinement.Core.rprjAddr (ixAddr bR) k) := by
    rw [hmap_rc, List.getElem?_mapIdx, hkL]
    rfl
  rw [List.getElem?_map] at h1
  obtain ⟨a_k, ha_k, ha_k_eq⟩ := Option.map_eq_some_iff.mp h1
  obtain ⟨recs', models', s', kV', form', r', h1, h1', cs1, C', ext1, hsub1, ha_rep⟩ :=
    FamilyOfCall.checkRecs_member as_rc has_rc1293 evCR k a_k ha_k
  exact memberRecon_of_cons ht hbd hS hH hR hlvR hrlv hsub hD hI hC hM hCt hCa hP hoff hdist
    hind hcov (by omega) hflat hmodelAll peer hminors side
    (fun c hc => C.evCheckRecs.sub c (hsub1 c hc)) C'
    (Nat.lt_trans hklt (Nat.lt_trans hrsz (by decide))) hrk ha_k_eq ha_rep
    (fun ev' ext => (rc_validates_group_spec hn
      (hrcRep.mono ((ext_0_1293.trans ext1).trans ext)) ev').1)

end Member

end IxVM.Refinement.Binding.FamilyCallRecon
