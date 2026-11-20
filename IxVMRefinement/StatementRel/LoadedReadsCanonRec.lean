import IxVMRefinement.StatementRel.LoadedReadsCanonInd

/-! # The canonical annotated constant of a recursor, and its reloads

A recursor record declares a recursor (`RecReads`): its level parameters `ps` (the family
inductive's, behind one more for a large eliminator), the reading `ty₀` of its type under `ps`,
the argument counts of the record, and one rule per rule of the record, whose right-hand side
reads as `rl₀.rhs` under `ps`. The circuit converts the type at root `base` (with no `recur`
address in scope) and rule `j`'s right-hand side at root `base + 1 + j`
(`Convert::convert_recursor`); a standalone record at base `0`, a member of a block at its root
offset. The stored constant is therefore a function of the record and its reading:

* `canonRules src ps kFlag cParams root rus rules₀`: each read rule with its right-hand side
  replaced by its canonical annotation at its root, and its K flag and parameter count set to
  the record's (the loaded rule list carries them: `Core.CIRep.recr`, `hk`). The rule's
  constructor key and field count are the reading's (`RuleStored` compares them).
* `canonRec key src base rc ps ty₀ rules₀`: the recursor under `key` with the canonical
  annotation of `ty₀` at root `base`, the record's argument counts, and `canonRules` from root
  `base + 1`.

The level parameters `ps` are part of the reading. What the representation needs of them is
what `recrPayload_rep` takes: as many as the record counts (`F3` gives it for `recPs`), in some
order of the positions, and a recursor that declares K has one rule (`F5`).

* `rules_canon`, `recr_value_canon`: the pure steps from a traced conversion.
* `get_ci_recr_canon`, `get_ci_rprj_canon`: every load of a standalone recursor record or a
  recursor-projection record, in calls with no hashed collision with the store, represents the
  canonical constant.
* `reloadsAs_recr`, `reloadsAs_recr_cons`, `reloadsAs_rprj`, `reloadsAs_rprj_cons`.
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxVM.Refinement.LoadedReads

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency

private theorem toUInt64_toNat_r {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

private theorem forall₂_imp_r {α β : Type} {R S : α → β → Prop} (H : ∀ a b, R a b → S a b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons hr hs => .cons (H _ _ hr) (forall₂_imp_r H hs)

/-! ## The canonical rules and recursor -/

/-- **The canonical rules**: rule `ru` with reading `rl₀`, from root `root`, is `rl₀` with
right-hand side the canonical annotation of `rl₀.rhs` at `root`, K flag `kFlag` and parameter
count `cParams`; the next rule is at `root + 1`. `none` if the lists differ in length or an
annotation is undefined. -/
noncomputable def canonRules (src : Ixon.Constant) (ps : List Ix.Kernel.LevelParam)
    (kFlag : Bool) (cParams : Nat) :
    F → List Ixon.RecursorRule → List (Ix.Kernel.RecRule .anon) →
      Option (List (Ix.Kernel.RecRule .anon))
  | _, [], [] => some []
  | root, ru :: rus, rl :: rls =>
    (canonAnn src ps root ru.rhs rl.rhs).bind fun rhs' =>
      (canonRules src ps kFlag cParams (root + 1) rus rls).map fun rest =>
        { rl with rhs := rhs', k := kFlag, ctorParams := cParams } :: rest
  | _, [], _ :: _ => none
  | _, _ :: _, [] => none

/-- **The canonical annotated constant of a recursor payload**: the recursor under the key
`key` with level parameters `ps`, the canonical annotation of its read type `ty₀` at root
`base` in the record `src`, the record's argument counts, and the canonical rules of its read
rules `rules₀` from root `base + 1`, with the record's K flag and parameter count. -/
noncomputable def canonRec (key : Ix.Kernel.Key .anon) (src : Ixon.Constant) (base : F)
    (rc : Ixon.Recursor) (ps : List Ix.Kernel.LevelParam) (ty₀ : Ix.Kernel.Expr .anon)
    (rules₀ : List (Ix.Kernel.RecRule .anon)) : Option (Ix.Kernel.ConstantInfo .anon) :=
  (canonAnn src ps base rc.typ ty₀).bind fun ty' =>
    (canonRules src ps rc.k rc.params.toNat (base + 1) rc.rules.toList rules₀).map fun rules' =>
      .recInfo ⟨key, ps, ty'⟩
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules'

theorem canonRec_eq {key : Ix.Kernel.Key .anon} {src : Ixon.Constant} {base : F}
    {rc : Ixon.Recursor} {ps : List Ix.Kernel.LevelParam} {ty₀ ty' : Ix.Kernel.Expr .anon}
    {rules₀ rls : List (Ix.Kernel.RecRule .anon)}
    (hT : canonAnn src ps base rc.typ ty₀ = some ty')
    (hR : canonRules src ps rc.k rc.params.toNat (base + 1) rc.rules.toList rules₀ = some rls) :
    canonRec key src base rc ps ty₀ rules₀ =
      some (.recInfo ⟨key, ps, ty'⟩
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rls) := by
  unfold canonRec
  rw [hT, hR]
  rfl

theorem canonRec_inv {key : Ix.Kernel.Key .anon} {src : Ixon.Constant} {base : F}
    {rc : Ixon.Recursor} {ps : List Ix.Kernel.LevelParam} {ty₀ : Ix.Kernel.Expr .anon}
    {rules₀ : List (Ix.Kernel.RecRule .anon)} {cn : Ix.Kernel.ConstantInfo .anon}
    (h : canonRec key src base rc ps ty₀ rules₀ = some cn) :
    ∃ (ty' : Ix.Kernel.Expr .anon) (rls : List (Ix.Kernel.RecRule .anon)),
      canonAnn src ps base rc.typ ty₀ = some ty' ∧
      canonRules src ps rc.k rc.params.toNat (base + 1) rc.rules.toList rules₀ = some rls ∧
      cn = .recInfo ⟨key, ps, ty'⟩
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rls := by
  unfold canonRec at h
  cases hT : canonAnn src ps base rc.typ ty₀ with
  | none =>
    rw [hT] at h
    have h' : (none : Option (Ix.Kernel.ConstantInfo .anon)) = some cn := h
    cases h'
  | some ty' =>
    rw [hT] at h
    cases hR : canonRules src ps rc.k rc.params.toNat (base + 1) rc.rules.toList rules₀ with
    | none =>
      rw [hR] at h
      have h' : (none : Option (Ix.Kernel.ConstantInfo .anon)) = some cn := h
      cases h'
    | some rls =>
      rw [hR] at h
      have h' : some (Ix.Kernel.ConstantInfo.recInfo ⟨key, ps, ty'⟩
          (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
          (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rls) = some cn := h
      exact ⟨ty', rls, rfl, rfl, (Option.some.inj h').symm⟩

section Rec

variable {t : Ix.Kernel.RoleTable}

/-- **Traced rules represent their canonical rules**, under a keying `κ` to which the table's
keying of each converted right-hand side transfers. -/
theorem rules_canon (ht : t.check = .ok ()) {blob : _root_.Address → Option ByteArray}
    {src : Ixon.Constant} {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (hps : ps.length < 4294967296)
    (hselfk : ∀ i x m k, recurAddrs[i]? = some x → self i = some m → m = .ok k →
      k = Core.keyOf t x)
    {blobs : List (_root_.Address × ByteArray)}
    (hagree : Ingress.BlobReadAgreement (readCtx t blob).blob blobs)
    {tree : Ingress.BinderTreeData}
    (built : Ingress.BinderTreeBuilt (Ingress.binderLeavesData src.binders.toList) tree)
    {h : Heap F} (κ : _root_.Address → Core.KKey) (kFlag : Bool) (cParams : Nat) :
    ∀ {j : Nat} {root : F} {rus : List Ixon.RecursorRule} {p : SourceValue F}
      {rules₀ : List (Ix.Kernel.RecRule .anon)},
      Ingress.RulesTraceRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs tree
        h j root rus p →
      (∀ ru ∈ rus, ∀ (q : SourceValue F) (X : Core.KExpr),
        Ingress.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs h
          4294967295 ru.rhs q → Core.TmC (Core.keyOf t) h X q → Core.TmC κ h X q) →
      List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
        (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self).read ru.rhs = .ok rl₀.rhs ∧
        rl₀.rhs.looseBVarsBounded 0 = true ∧ rl₀.rhs.allLevelParamsDefined ps = true)
        rus rules₀ →
      ∃ rls : List (Ix.Kernel.RecRule .anon),
        canonRules src ps kFlag cParams root rus rules₀ = some rls ∧
        List.Forall₂ RuleStored rls rules₀ ∧
        Core.RulesRep κ h ps j p rls ∧
        (∀ rl ∈ rls, rl.k = kFlag ∧ rl.ctorParams = cParams) := by
  intro j root rus p rules₀ hrep
  induction hrep generalizing rules₀ with
  | nil cell =>
    intro _ hfa
    cases hfa with
    | nil => exact ⟨[], by simp [canonRules], .nil, .nil cell, fun _ hm => nomatch hm⟩
  | @cons j root addr rhsPtr rest ru rus plan cell hf raw planned levels rs ih =>
    intro hre hfa
    cases hfa with
    | @cons _ rl₀ _ rest₀ hhd htl =>
      obtain ⟨hnf, hrd, hlbb, hdef⟩ := hhd
      obtain ⟨rhs', hcR, hannR, htmR⟩ :=
        annotation_canon_gen ht hperm hps hselfk hagree raw built planned levels hrd hlbb hdef
      obtain ⟨rls, hcrs, hst, hrr, hprops⟩ :=
        ih (fun ru' hm => hre ru' (List.mem_cons.mpr (Or.inr hm))) htl
      have htmK : Core.TmC κ h (Core.posOf ps rhs') rhsPtr :=
        hre ru (List.mem_cons.mpr (Or.inl rfl)) _ _ raw htmR
      refine ⟨{ rl₀ with rhs := rhs', k := kFlag, ctorParams := cParams } :: rls, ?_,
        .cons ⟨rfl, rfl, hannR⟩ hst, .cons cell ⟨rhsPtr, ?_, ?_, htmK⟩ hrr, ?_⟩
      · simp [canonRules, hcR, hcrs]
      · show _ = Value.construct Core.krrEnum "Mk"
          [.field (j : F), .field (rl₀.nfields : F), rhsPtr]
        rw [hnf]
      · show rl₀.nfields < 72057594037927936
        rw [hnf]
        exact hf
      · intro rl hm
        rcases List.mem_cons.mp hm with rfl | hm'
        · exact ⟨rfl, rfl⟩
        · exact hprops rl hm'

/-- **A traced conversion of a recursor payload represents its canonical constant**, under a
keying `κ` to which the table's keying of the converted type and right-hand sides transfers,
and under which the name is the key of the recursor's own address or of the member's projection
record (the two forms the loaded value names). The level parameters are as many as the record
counts, in some order of the positions; the readings are well scoped; a recursor that declares
K has one rule. -/
theorem recr_value_canon (ht : t.check = .ok ()) {blob : _root_.Address → Option ByteArray}
    {src : Ixon.Constant} {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {rc : Ixon.Recursor} {ps : List Ix.Kernel.LevelParam}
    (hlen : ps.length = rc.lvls.toNat) (hperm : ps.Perm (List.range ps.length))
    (hselfk : ∀ i x m k, recurAddrs[i]? = some x → self i = some m → m = .ok k →
      k = Core.keyOf t x)
    {blobs : List (_root_.Address × ByteArray)}
    (hagree : Ingress.BlobReadAgreement (readCtx t blob).blob blobs)
    {tree : Ingress.BinderTreeData}
    (built : Ingress.BinderTreeBuilt (Ingress.binderLeavesData src.binders.toList) tree)
    {root : F} {h : Heap F} {v : SourceValue F} {blkAddr : _root_.Address} {recIdx : Nat}
    (rep : Ingress.RecrTraceRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      tree root h rc blkAddr recIdx v)
    {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self).read rc.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true)
    {rules₀ : List (Ix.Kernel.RecRule .anon)}
    (hrules : List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
      (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self).read ru.rhs = .ok rl₀.rhs ∧
      rl₀.rhs.looseBVarsBounded 0 = true ∧ rl₀.rhs.allLevelParamsDefined ps = true)
      rc.rules.toList rules₀)
    (hk : rc.k = true → rc.rules.size = 1)
    (κ : _root_.Address → Core.KKey) (name : Ix.Kernel.Key .anon)
    (hname : name = κ blkAddr ∨ name = κ (Core.rprjAddr blkAddr recIdx))
    (hreT : ∀ (q : SourceValue F) (X : Core.KExpr),
      Ingress.RawConvExpr src.refs.toList [] src.univs.toList src.sharing.toList blobs h 4294967295
        rc.typ q → Core.TmC (Core.keyOf t) h X q → Core.TmC κ h X q)
    (hreR : ∀ ru ∈ rc.rules.toList, ∀ (q : SourceValue F) (X : Core.KExpr),
      Ingress.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs h
        4294967295 ru.rhs q → Core.TmC (Core.keyOf t) h X q → Core.TmC κ h X q) :
    ∃ (ty' : Ix.Kernel.Expr .anon) (rls : List (Ix.Kernel.RecRule .anon)),
      canonAnn src ps root rc.typ ty₀ = some ty' ∧
      canonRules src ps rc.k rc.params.toNat (root + 1) rc.rules.toList rules₀ = some rls ∧
      Annotates ty' ty₀ ∧ List.Forall₂ RuleStored rls rules₀ ∧
      Core.CIRep κ h v (.recInfo ⟨name, ps, ty'⟩
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rls) := by
  obtain ⟨hlvls, hp56, hi56, hm56, hmi56, hidx56, tyPtr, rulesPtr, blkPtr, b, planT, hb_eq,
    hb_rep, hv, rty, hpT, hlT, hrls⟩ := rep
  subst hv
  have hps : ps.length < 4294967296 := by rw [hlen]; exact hlvls
  have hself_nil : ∀ i x m k, ([] : List _root_.Address)[i]? = some x → self i = some m →
      m = .ok k → k = Core.keyOf t x := fun _ _ _ _ hx => by simp at hx
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    annotation_canon_gen ht hperm hps hself_nil hagree rty built hpT hlT hty hty_lbb hty_def
  obtain ⟨rls, hcR, hst, hrr, hprops⟩ :=
    rules_canon ht hperm hps hselfk hagree built κ rc.k rc.params.toNat hrls hreR hrules
  refine ⟨ty', rls, hcT, hcR, hannT, hst, ?_⟩
  refine .recr ⟨by rw [hlen], hps, hperm, hreT _ _ rty htmT⟩ rfl rfl rfl rfl
    (by simp only [Nat.cast_add]) (by simp only [Nat.cast_add]) ⟨by omega, by omega⟩ hrr ?_
    ⟨b, ((recIdx : Nat) : F), hb_rep, rfl, ?_⟩
  · intro hk1
    have hrck : rc.k = true := by
      cases hkc : rc.k <;> simp [Ingress.repBoolField, hkc] at hk1
      rfl
    have hlen1 : rls.length = 1 := by
      have hl1 := hst.length_eq
      have hl2 := hrules.length_eq
      rw [hl1, ← hl2, Array.length_toList, hk hrck]
    rcases rls with _ | ⟨rl, _ | _⟩
    · simp at hlen1
    · obtain ⟨hrlk, hrlp⟩ := hprops rl (List.mem_singleton.mpr rfl)
      rw [hrck] at hrlk
      rw [← Ingress.val_cast_u56_ing hp56] at hrlp
      exact ⟨rl, rfl, hrlk, hrlp⟩
    · simp at hlen1
  · rw [hb_eq, Ingress.val_cast_u56_ing hidx56]
    exact hname

/-- The references a recursor record's type uses are references the record uses. -/
private theorem recr_typ_used {c : Ixon.Constant} {rc : Ixon.Recursor} (hinfo : c.info = .recr rc) :
    ∀ i, i ∈ exprRefIdxs rc.typ → i ∈ usedRefIdxs c := by
  intro i hi
  unfold usedRefIdxs
  rw [hinfo]
  exact List.mem_append_right _ (List.mem_append_left _ hi)

private theorem recr_rule_used {c : Ixon.Constant} {rc : Ixon.Recursor}
    (hinfo : c.info = .recr rc) {ru : Ixon.RecursorRule} (hru : ru ∈ rc.rules.toList) :
    ∀ i, i ∈ exprRefIdxs ru.rhs → i ∈ usedRefIdxs c := by
  intro i hi
  unfold usedRefIdxs
  rw [hinfo]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨ru, hru, hi⟩))

private theorem rmember_typ_used {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {k : Nat}
    {rc : Ixon.Recursor} (hmuts : cb.info = .muts ms) (hmem : ms[k]? = some (.recr rc)) :
    ∀ i, i ∈ exprRefIdxs rc.typ → i ∈ usedRefIdxs cb := by
  have hmem' : Ixon.MutConst.recr rc ∈ ms.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hmem)
  intro i hi
  unfold usedRefIdxs
  rw [hmuts]
  exact List.mem_append_right _
    (List.mem_flatMap.mpr ⟨.recr rc, hmem', by unfold mutRefIdxs; exact List.mem_append_left _ hi⟩)

private theorem rmember_rule_used {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {k : Nat}
    {rc : Ixon.Recursor} (hmuts : cb.info = .muts ms) (hmem : ms[k]? = some (.recr rc))
    {ru : Ixon.RecursorRule} (hru : ru ∈ rc.rules.toList) :
    ∀ i, i ∈ exprRefIdxs ru.rhs → i ∈ usedRefIdxs cb := by
  have hmem' : Ixon.MutConst.recr rc ∈ ms.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hmem)
  intro i hi
  unfold usedRefIdxs
  rw [hmuts]
  exact List.mem_append_right _
    (List.mem_flatMap.mpr ⟨.recr rc, hmem', by
      unfold mutRefIdxs
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨ru, hru, hi⟩)⟩)

/-! ## A standalone recursor record -/

/-- **Every load of a held standalone recursor record represents its canonical constant.**
The store `E` holds the record `c` at the address (exact decoding); `ps`, `ty₀`, `rules₀` are
the reading's level parameters, type and rules over `E`'s blobs (as `RecReads` gives them),
with `ps` as many as the record counts and in some order of the positions, the readings well
scoped, and one rule if the record declares K. Then for a `get_ci` at the address in bounded
calls that hash no collision with `E`, the canonical annotations (type at root `0`, rule `j` at
root `1 + j`) are defined and the returned pointer represents the canonical constant: under the
table's keying, and under the keying of any prefix that stores the references the record uses
and the record's own key. -/
theorem get_ci_recr_canon (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbound : Bounded cs)
    {a : Aiur.Library.Bytes.Address} {addr ptr : SourceValue F} {h h' : Heap F}
    (ha : Aiur.Library.Bytes.RepAddressRef Core.addrTy h a addr)
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) {c : Ixon.Constant}
    {rc : Ixon.Recursor} (hrec : recordOf E (Core.ixAddr a) = some c) (hinfo : c.info = .recr rc)
    {ps : List Ix.Kernel.LevelParam} (hlen : ps.length = rc.lvls.toNat)
    (hperm : ps.Perm (List.range ps.length)) {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) c (Ix.Kernel.Reader.recParam ps)
      (soloSelf t (Core.ixAddr a))).read rc.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true)
    {rules₀ : List (Ix.Kernel.RecRule .anon)}
    (hrules : List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
      (exprReader t (fun x => E.blobs.get? x) c (Ix.Kernel.Reader.recParam ps)
        (soloSelf t (Core.ixAddr a))).read ru.rhs = .ok rl₀.rhs ∧
      rl₀.rhs.looseBVarsBounded 0 = true ∧ rl₀.rhs.allLevelParamsDefined ps = true)
      rc.rules.toList rules₀)
    (hk : rc.k = true → rc.rules.size = 1) :
    ∃ (ty' : Ix.Kernel.Expr .anon) (rls : List (Ix.Kernel.RecRule .anon)),
      canonAnn c ps 0 rc.typ ty₀ = some ty' ∧
      canonRules c ps rc.k rc.params.toNat (0 + 1) rc.rules.toList rules₀ = some rls ∧
      Annotates ty' ty₀ ∧ List.Forall₂ RuleStored rls rules₀ ∧
      Core.CIPtrRep (Core.keyOf t) h' ptr (.recInfo ⟨keyOf t (Core.ixAddr a), ps, ty'⟩
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rls) ∧
      (∀ (env : Ix.Kernel.Env .anon) (lim : Option Nat), Decl.UsedRefsStored t env c →
        (∃ ci, env.find? (Core.keyOf t (Core.ixAddr a)) = some ci) →
          Core.CIPtrRep (Core.Ctx.stored ⟨E, env, t, lim⟩).κ h' ptr
            (.recInfo ⟨keyOf t (Core.ixAddr a), ps, ty'⟩
              (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
              (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rls)) := by
  obtain ⟨rawBytes, c', hh, haddr, hex, htv, hres⟩ := Ingress.get_ci_block_trace_spec hbound ha ev
  obtain ⟨lc, hget, hdec⟩ := recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hnc rawBytes hh haddr
  have hc : c = c' := by
    rw [hb, hdec] at hex
    exact Except.ok.inj hex
  subst hc
  unfold Ingress.GetCIBlockTraceResult at hres
  rw [hinfo] at hres
  obtain ⟨blobs, tree, v, hhp, built, hld, htr⟩ := hres
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨ty', rls, hcT, hcR, hannT, hst, hrepT⟩ :=
    recr_value_canon ht hlen hperm (soloSelf_key t (Core.ixAddr a)) hagree built htr hty hty_lbb
      hty_def hrules hk (Core.keyOf t) (keyOf t (Core.ixAddr a)) (Or.inl rfl)
      (fun _ _ _ r => r) (fun _ _ _ _ _ r => r)
  refine ⟨ty', rls, hcT, hcR, hannT, hst, ⟨_, hld, hrepT⟩, fun env lim hstored hself => ?_⟩
  obtain ⟨ci, hci⟩ := hself
  have hκ := Core.Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hci
  obtain ⟨ty'', rls', hcT', hcR', -, -, hrepS⟩ :=
    recr_value_canon ht hlen hperm (soloSelf_key t (Core.ixAddr a)) hagree built htr hty hty_lbb
      hty_def hrules hk (Core.Ctx.stored ⟨E, env, t, lim⟩).κ (keyOf t (Core.ixAddr a))
      (Or.inl hκ.symm)
      (fun q X raw rep => tmC_stored_of_used raw (recr_typ_used hinfo) hstored
        (fun x hx => by simp at hx) rep)
      (fun ru hru q X raw rep => tmC_stored_of_used raw (recr_rule_used hinfo hru) hstored
        (fun x hx => by
          rw [List.mem_singleton] at hx
          rw [hx]
          exact ⟨ci, hci⟩) rep)
  have e1 : ty'' = ty' := Option.some.inj (hcT'.symm.trans hcT)
  have e2 : rls' = rls := Option.some.inj (hcR'.symm.trans hcR)
  subst e1
  subst e2
  exact ⟨_, hld, hrepS⟩

/-- **The canonical constant of a standalone recursor record reloads** at every store `E'`
that holds the record `c` at `a` (exact decoding) and over whose blobs the record's type and
rules read as `ty₀`, `rules₀` under `ps`, under the keying of any prefix `env` that stores the
references the record uses and the record's own key. -/
theorem reloadsAs_recr (ht : t.check = .ok ()) {E' : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {a : _root_.Address} {c : Ixon.Constant} {rc : Ixon.Recursor}
    (hrec : recordOf E' a = some c) (hinfo : c.info = .recr rc)
    {ps : List Ix.Kernel.LevelParam} (hlen : ps.length = rc.lvls.toNat)
    (hperm : ps.Perm (List.range ps.length)) {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E'.blobs.get? x) c (Ix.Kernel.Reader.recParam ps)
      (soloSelf t a)).read rc.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true)
    {rules₀ : List (Ix.Kernel.RecRule .anon)}
    (hrules : List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
      (exprReader t (fun x => E'.blobs.get? x) c (Ix.Kernel.Reader.recParam ps)
        (soloSelf t a)).read ru.rhs = .ok rl₀.rhs ∧
      rl₀.rhs.looseBVarsBounded 0 = true ∧ rl₀.rhs.allLevelParamsDefined ps = true)
      rc.rules.toList rules₀)
    (hk : rc.k = true → rc.rules.size = 1)
    (hstored : Decl.UsedRefsStored t env c)
    (hself : ∃ ci, env.find? (Core.keyOf t a) = some ci)
    {cn : Ix.Kernel.ConstantInfo .anon}
    (hcn : canonRec (keyOf t a) c 0 rc ps ty₀ rules₀ = some cn) :
    Decl.ReloadsAs E' t env cn := by
  obtain ⟨ty', rls, hcT, hcR, hcn'⟩ := canonRec_inv hcn
  subst hcn'
  intro addr ptr h h' cs a' ev hgood ha hkey
  have hk' : Core.keyOf t (Core.ixAddr a') = Core.keyOf t a := hkey
  have haddr : Core.ixAddr a' = a := Assembly.keyOf_injective ht hk'
  subst haddr
  obtain ⟨ty'', rls', hcT', hcR', -, -, -, hrep⟩ :=
    get_ci_recr_canon ht hgood.1 hgood.2 ha ev hrec hinfo hlen hperm hty hty_lbb hty_def hrules hk
  have e1 : ty'' = ty' := Option.some.inj (hcT'.symm.trans hcT)
  have e2 : rls' = rls := Option.some.inj (hcR'.symm.trans hcR)
  subst e1
  subst e2
  exact hrep env none hstored hself

/-- **The reload a step needs, for a standalone recursor record**: the canonical constant
reloads under the keying of the prefix that stores it, where the prefix before it stores the
references the record uses, at every store `E'` that holds the record and at least the blobs of
a store `E` over which the record's type and rules read as `ty₀`, `rules₀`. -/
theorem reloadsAs_recr_cons (ht : t.check = .ok ()) {E E' : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {a : _root_.Address} {c : Ixon.Constant} {rc : Ixon.Recursor}
    (hrec : recordOf E' a = some c) (hinfo : c.info = .recr rc)
    (hblobs : ∀ x b, E.blobs.get? x = some b → E'.blobs.get? x = some b)
    {ps : List Ix.Kernel.LevelParam} (hlen : ps.length = rc.lvls.toNat)
    (hperm : ps.Perm (List.range ps.length)) {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) c (Ix.Kernel.Reader.recParam ps)
      (soloSelf t a)).read rc.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true)
    {rules₀ : List (Ix.Kernel.RecRule .anon)}
    (hrules : List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
      (exprReader t (fun x => E.blobs.get? x) c (Ix.Kernel.Reader.recParam ps)
        (soloSelf t a)).read ru.rhs = .ok rl₀.rhs ∧
      rl₀.rhs.looseBVarsBounded 0 = true ∧ rl₀.rhs.allLevelParamsDefined ps = true)
      rc.rules.toList rules₀)
    (hk : rc.k = true → rc.rules.size = 1)
    (hstored : Decl.UsedRefsStored t env c)
    {cn : Ix.Kernel.ConstantInfo .anon}
    (hcn : canonRec (keyOf t a) c 0 rc ps ty₀ rules₀ = some cn) :
    Decl.ReloadsAs E' t ⟨cn :: env.consts⟩ cn := by
  have hname : cn.name = Core.keyOf t a := by
    obtain ⟨ty', rls, -, -, hcneq⟩ := canonRec_inv hcn
    subst hcneq
    rfl
  exact reloadsAs_recr ht hrec hinfo hlen hperm
    (ReaderReads.exprReader_mono (blob := fun x => E.blobs.get? x)
      (blob' := fun x => E'.blobs.get? x) hblobs hty)
    hty_lbb hty_def
    (forall₂_imp_r (fun ru rl₀ hr => ⟨hr.1,
      ReaderReads.exprReader_mono (blob := fun x => E.blobs.get? x)
        (blob' := fun x => E'.blobs.get? x) hblobs hr.2.1, hr.2.2⟩) hrules)
    hk (usedRefsStored_cons cn hstored)
    ⟨cn, by rw [Ix.Kernel.Env.find?_cons, ite_eq_left hname]⟩ hcn

/-! ## A recursor member of a block -/

/-- **Every load of a held recursor-projection record represents its canonical constant.**
The store `E` holds the record `c` at the address and the block `cb` at the block address it
names (exact decodings); the member is the recursor `rc`; `ps`, `ty₀`, `rules₀` are the
reading's level parameters, type and rules in the block over `E`'s blobs, with the facts of
`get_ci_recr_canon`. Then for a `get_ci` at the address in bounded calls that hash no collision
with `E`, the address is the member's constant address, the canonical annotations (at the
member's root offset) are defined and the returned pointer represents the canonical constant:
under the table's keying, and under the keying of any prefix that stores the references the
block uses and the block's members. -/
theorem get_ci_rprj_canon (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbound : Bounded cs)
    {a : Aiur.Library.Bytes.Address} {addr ptr : SourceValue F} {h h' : Heap F}
    (ha : Aiur.Library.Bytes.RepAddressRef Core.addrTy h a addr)
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) {c cb : Ixon.Constant}
    {p : Ixon.RecursorProj} {ms : Array Ixon.MutConst} {rc : Ixon.Recursor}
    (hrec : recordOf E (Core.ixAddr a) = some c) (hinfo : c.info = .rPrj p)
    (hblock : recordOf E p.block = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[p.idx.toNat]? = some (.recr rc))
    {ps : List Ix.Kernel.LevelParam} (hlen : ps.length = rc.lvls.toNat)
    (hperm : ps.Perm (List.range ps.length)) {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) cb (Ix.Kernel.Reader.recParam ps)
      (blockSelf t p.block ms)).read rc.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true)
    {rules₀ : List (Ix.Kernel.RecRule .anon)}
    (hrules : List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
      (exprReader t (fun x => E.blobs.get? x) cb (Ix.Kernel.Reader.recParam ps)
        (blockSelf t p.block ms)).read ru.rhs = .ok rl₀.rhs ∧
      rl₀.rhs.looseBVarsBounded 0 = true ∧ rl₀.rhs.allLevelParamsDefined ps = true)
      rc.rules.toList rules₀)
    (hk : rc.k = true → rc.rules.size = 1) :
    Core.ixAddr a = memberAddr p.block p.idx.toNat (.recr rc) ∧
    ∃ (ty' : Ix.Kernel.Expr .anon) (rls : List (Ix.Kernel.RecRule .anon)),
      canonAnn cb ps ((Ingress.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) rc.typ ty₀ =
        some ty' ∧
      canonRules cb ps rc.k rc.params.toNat
        (((Ingress.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) + 1) rc.rules.toList rules₀ =
        some rls ∧
      Annotates ty' ty₀ ∧ List.Forall₂ RuleStored rls rules₀ ∧
      Core.CIPtrRep (Core.keyOf t) h' ptr (.recInfo ⟨keyOf t (Core.ixAddr a), ps, ty'⟩
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rls) ∧
      (∀ (env : Ix.Kernel.Env .anon) (lim : Option Nat), Decl.UsedRefsStored t env cb →
        BlockStored t env p.block ms →
          Core.CIPtrRep (Core.Ctx.stored ⟨E, env, t, lim⟩).κ h' ptr
            (.recInfo ⟨keyOf t (Core.ixAddr a), ps, ty'⟩
              (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
              (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rls)) := by
  obtain ⟨rawBytes, c', hh, haddr, hex, htv, hres⟩ := Ingress.get_ci_block_trace_spec hbound ha ev
  obtain ⟨lc, hget, hdec⟩ := recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hnc rawBytes hh haddr
  have hc : c = c' := by
    rw [hb, hdec] at hex
    exact Except.ok.inj hex
  subst hc
  have haddr' : Core.ixAddr a = memberAddr p.block p.idx.toNat (.recr rc) :=
    haddr.symm.trans (rprj_canonical rc hex htv hinfo).2
  have hkey : keyOf t (Core.ixAddr a) = Core.keyOf t (Core.rprjAddr p.block p.idx.toNat) := by
    rw [haddr', memberAddr_recr, keyOf_eq]
  unfold Ingress.GetCIBlockTraceResult at hres
  rw [hinfo] at hres
  obtain ⟨hidx, blkBytes, cb', ms', rc', blobs, tree, v, hhB, haB, hexB, hcb, hms, hhp, built,
    hld, htr⟩ := hres
  obtain ⟨lcB, hgetB, hdecB⟩ := recordOf_inv hblock
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hnc blkBytes hhB haB
  have hcB : cb = cb' := by
    rw [hbB, hdecB] at hexB
    exact Except.ok.inj hexB
  subst hcB
  have hmsEq : ms = ms' := Ixon.ConstantInfo.muts.inj (hmuts.symm.trans hcb)
  subst hmsEq
  have hms' : ms[p.idx.toNat]? = some (.recr rc') := by
    rw [← Array.getElem?_toList]
    exact hms
  have hrEq : rc = rc' := Ixon.MutConst.recr.inj (Option.some.inj (hmem.symm.trans hms'))
  subst hrEq
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨ty', rls, hcT, hcR, hannT, hst, hrepT⟩ :=
    recr_value_canon ht hlen hperm (blockSelf_key t p.block ms) hagree built htr hty hty_lbb
      hty_def hrules hk (Core.keyOf t) (Core.keyOf t (Core.rprjAddr p.block p.idx.toNat))
      (Or.inr rfl) (fun _ _ _ r => r) (fun _ _ _ _ _ r => r)
  rw [hkey]
  refine ⟨haddr', ty', rls, hcT, hcR, hannT, hst, ⟨_, hld, hrepT⟩, fun env lim hstored hblk => ?_⟩
  have hin := memberAddr_mem_blockRecurAddrs (B := p.block) hmem
  rw [memberAddr_recr] at hin
  obtain ⟨ci, hci⟩ := hblk _ hin
  have hκ := Core.Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hci
  obtain ⟨ty'', rls', hcT', hcR', -, -, hrepS⟩ :=
    recr_value_canon ht hlen hperm (blockSelf_key t p.block ms) hagree built htr hty hty_lbb
      hty_def hrules hk (Core.Ctx.stored ⟨E, env, t, lim⟩).κ
      (Core.keyOf t (Core.rprjAddr p.block p.idx.toNat)) (Or.inr hκ.symm)
      (fun q X raw rep => tmC_stored_of_used raw (rmember_typ_used hmuts hmem) hstored
        (fun x hx => by simp at hx) rep)
      (fun ru hru q X raw rep => tmC_stored_of_used raw (rmember_rule_used hmuts hmem hru)
        hstored hblk rep)
  have e1 : ty'' = ty' := Option.some.inj (hcT'.symm.trans hcT)
  have e2 : rls' = rls := Option.some.inj (hcR'.symm.trans hcR)
  subst e1
  subst e2
  exact ⟨_, hld, hrepS⟩

/-- **The canonical constant of a recursor member reloads** at every store `E'` that holds the
member's projection record `c` at `a` and the block `cb` at the block address it names (exact
decodings), and over whose blobs the member's type and rules read as `ty₀`, `rules₀` under
`ps`, under the keying of any prefix `env` that stores the references the block uses and the
block's members. -/
theorem reloadsAs_rprj (ht : t.check = .ok ()) {E' : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {a : _root_.Address} {c cb : Ixon.Constant} {p : Ixon.RecursorProj}
    {ms : Array Ixon.MutConst} {rc : Ixon.Recursor}
    (hrec : recordOf E' a = some c) (hinfo : c.info = .rPrj p)
    (hblock : recordOf E' p.block = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[p.idx.toNat]? = some (.recr rc))
    {ps : List Ix.Kernel.LevelParam} (hlen : ps.length = rc.lvls.toNat)
    (hperm : ps.Perm (List.range ps.length)) {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E'.blobs.get? x) cb (Ix.Kernel.Reader.recParam ps)
      (blockSelf t p.block ms)).read rc.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true)
    {rules₀ : List (Ix.Kernel.RecRule .anon)}
    (hrules : List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
      (exprReader t (fun x => E'.blobs.get? x) cb (Ix.Kernel.Reader.recParam ps)
        (blockSelf t p.block ms)).read ru.rhs = .ok rl₀.rhs ∧
      rl₀.rhs.looseBVarsBounded 0 = true ∧ rl₀.rhs.allLevelParamsDefined ps = true)
      rc.rules.toList rules₀)
    (hk : rc.k = true → rc.rules.size = 1)
    (hstored : Decl.UsedRefsStored t env cb) (hblk : BlockStored t env p.block ms)
    {cn : Ix.Kernel.ConstantInfo .anon}
    (hcn : canonRec (keyOf t a) cb ((Ingress.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) rc ps
      ty₀ rules₀ = some cn) :
    Decl.ReloadsAs E' t env cn := by
  obtain ⟨ty', rls, hcT, hcR, hcn'⟩ := canonRec_inv hcn
  subst hcn'
  intro addr ptr h h' cs a' ev hgood ha hkey
  have hk' : Core.keyOf t (Core.ixAddr a') = Core.keyOf t a := hkey
  have haddr : Core.ixAddr a' = a := Assembly.keyOf_injective ht hk'
  subst haddr
  obtain ⟨-, ty'', rls', hcT', hcR', -, -, -, hrep⟩ :=
    get_ci_rprj_canon ht hgood.1 hgood.2 ha ev hrec hinfo hblock hmuts hmem hlen hperm hty
      hty_lbb hty_def hrules hk
  have e1 : ty'' = ty' := Option.some.inj (hcT'.symm.trans hcT)
  have e2 : rls' = rls := Option.some.inj (hcR'.symm.trans hcR)
  subst e1
  subst e2
  exact hrep env none hstored hblk

/-- **The reload a step needs, for recursor member `k` of the block at `B`**: the canonical
constant reloads under the keying of the prefix that stores it, where the prefix before it
stores the references the block uses and the prefix with it stores the block's members, at
every store `E'` that holds the member's projection record at its constant address, the block
at `B`, and at least the blobs of a store `E` over which the member's type and rules read as
`ty₀`, `rules₀`. -/
theorem reloadsAs_rprj_cons (ht : t.check = .ok ()) {E E' : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {k : Nat} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {rc : Ixon.Recursor} (hk64 : k < UInt64.size)
    (hproj : recordOf E' (memberAddr B k (.recr rc)) = some (memberProjection B k (.recr rc)))
    (hblock : recordOf E' B = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[k]? = some (.recr rc))
    (hblobs : ∀ x b, E.blobs.get? x = some b → E'.blobs.get? x = some b)
    {ps : List Ix.Kernel.LevelParam} (hlen : ps.length = rc.lvls.toNat)
    (hperm : ps.Perm (List.range ps.length)) {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) cb (Ix.Kernel.Reader.recParam ps)
      (blockSelf t B ms)).read rc.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true) (hty_def : ty₀.allLevelParamsDefined ps = true)
    {rules₀ : List (Ix.Kernel.RecRule .anon)}
    (hrules : List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
      (exprReader t (fun x => E.blobs.get? x) cb (Ix.Kernel.Reader.recParam ps)
        (blockSelf t B ms)).read ru.rhs = .ok rl₀.rhs ∧
      rl₀.rhs.looseBVarsBounded 0 = true ∧ rl₀.rhs.allLevelParamsDefined ps = true)
      rc.rules.toList rules₀)
    (hk : rc.k = true → rc.rules.size = 1)
    (hstored : Decl.UsedRefsStored t env cb)
    {cn : Ix.Kernel.ConstantInfo .anon}
    (hblk : BlockStored t ⟨cn :: env.consts⟩ B ms)
    (hcn : canonRec (keyOf t (memberAddr B k (.recr rc))) cb
      ((Ingress.mutsRootOffset ms.toList k : Nat) : F) rc ps ty₀ rules₀ = some cn) :
    Decl.ReloadsAs E' t ⟨cn :: env.consts⟩ cn := by
  have hkk : k.toUInt64.toNat = k := toUInt64_toNat_r hk64
  have hinfo : (memberProjection B k (.recr rc)).info = .rPrj ⟨k.toUInt64, B⟩ := rfl
  have hmem' : ms[(⟨k.toUInt64, B⟩ : Ixon.RecursorProj).idx.toNat]? = some (.recr rc) := by
    show ms[k.toUInt64.toNat]? = some (.recr rc)
    rw [hkk]
    exact hmem
  have hcn' : canonRec (keyOf t (memberAddr B k (.recr rc))) cb
      ((Ingress.mutsRootOffset ms.toList (⟨k.toUInt64, B⟩ : Ixon.RecursorProj).idx.toNat : Nat) : F)
      rc ps ty₀ rules₀ = some cn := by
    show canonRec (keyOf t (memberAddr B k (.recr rc))) cb
      ((Ingress.mutsRootOffset ms.toList k.toUInt64.toNat : Nat) : F) rc ps ty₀ rules₀ = some cn
    rw [hkk]
    exact hcn
  exact reloadsAs_rprj (p := ⟨k.toUInt64, B⟩) ht hproj hinfo hblock hmuts hmem' hlen hperm
    (ReaderReads.exprReader_mono (blob := fun x => E.blobs.get? x)
      (blob' := fun x => E'.blobs.get? x) hblobs hty)
    hty_lbb hty_def
    (forall₂_imp_r (fun ru rl₀ hr => ⟨hr.1,
      ReaderReads.exprReader_mono (blob := fun x => E.blobs.get? x)
        (blob' := fun x => E'.blobs.get? x) hblobs hr.2.1, hr.2.2⟩) hrules)
    hk (usedRefsStored_cons cn hstored) hblk hcn'

end Rec

end IxVM.Refinement.LoadedReads
