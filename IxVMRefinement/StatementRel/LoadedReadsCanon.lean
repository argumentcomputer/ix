import IxVMRefinement.StatementRel.LoadedReadsReload
import IxVMRefinement.StatementRel.LoadedReadsTrace
import IxVMRefinement.StatementRel.ReadsMono
import IxVMRefinement.L1.AnnotationCorrespondence
import IxVMRefinement.Assembly.RecordReadBare
import IxVMRefinement.Decl.PrefixInv

/-! # The canonical annotated constant of a definition record, and its reloads

A definition, theorem or opaque record declares a constant by its reading: the kernel reader's
conversion of its type and value (`Reads`). The circuit stores an annotated form of that
constant: each binder of the converted terms carries data the circuit computes from the record's
binder blocks. This module names that annotated form as a function of the record and its
reading, and shows that every load of the record represents it.

* `canonAnn src ps root e E_rd`: the annotation of the reading `E_rd` of the expression `e` of
  the record `src`, converted at root `root`. It applies the binder plan of the root
  (`L1.binderRootPlan`, in the tree built from `src`'s binder blocks) to the reading. Nothing
  outside the record and the reading enters.
* `canonDefn key src base d ty₀ val₀ hn`: the constant of the definition payload `d` under the
  key `key`, with the annotations of its read type (root `base`) and value (root `base + 1`).
  A standalone record converts at base `0`; a member of a block at its root offset.
* `get_ci_defn_canon`, `get_ci_dprj_canon`: a `get_ci` on the address of a record a store
  holds, in calls that hash no collision with the store, returns a pointer representing the
  canonical constant, under the table's keying and, where the references the record uses are
  stored, under the keying of a prefix.
* `reloadsAs_defn`, `reloadsAs_dprj`: hence the canonical constant reloads (`Decl.ReloadsAs`)
  at every store that holds the record (for a member, also its block) and over whose blobs the
  record reads as it did.
* `get_ci_axio_canon`, `reloadsAs_axio`: the same for an axiom record, whose type is converted
  at root `0`.
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.LoadedReads

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency

/-! ## The canonical annotation -/

open Classical in
/-- **The binder tree of a record's binder blocks**: the tree `Convert::binder_table` builds
from them (`L1.BinderTreeBuilt`, which determines it: `canonTree_eq`). -/
noncomputable def canonTree (blocks : List Ixon.BinderBlock) : L1.BinderTreeData :=
  if h : ∃ tree, L1.BinderTreeBuilt (L1.binderLeavesData blocks) tree then Classical.choose h
  else .empty

theorem canonTree_eq {blocks : List Ixon.BinderBlock} {tree : L1.BinderTreeData}
    (built : L1.BinderTreeBuilt (L1.binderLeavesData blocks) tree) : canonTree blocks = tree := by
  have h : ∃ tree, L1.BinderTreeBuilt (L1.binderLeavesData blocks) tree := ⟨tree, built⟩
  unfold canonTree
  rw [dite_eq_left h]
  exact (Classical.choose_spec h).unique built

/-- **The canonical annotation of a reading.** `E_rd` is the reading of the expression `e` of
the record `src`, under the level parameters `ps`; the annotation applies to it the binder plan
of root `root` in the tree of `src`'s binder blocks. It is `none` where the record has no plan
for the root or the plan does not fit the reading (neither happens for a record the circuit
converted: `annotation_canon`). -/
noncomputable def canonAnn (src : Ixon.Constant) (ps : List Ix.Kernel.LevelParam) (root : F)
    (e : Ixon.Expr) (E_rd : Ix.Kernel.Expr .anon) : Option (Ix.Kernel.Expr .anon) :=
  (L1.binderRootPlan (canonTree src.binders.toList) src.sharing.toList root e).bind fun plan =>
    (L1.applyBinderTrace (fun level => Core.bmeta (L1.invPosLevel ps level)) E_rd plan).map
      Prod.fst

/-- **A converted root represents the canonical annotation of its reading.** The root was
converted with no `recur` in scope, in the tree built from the record's binder blocks, with
the plan `plan` on the heap; its reading `E_rd` is well scoped; the literal bytes the
conversion hashed agree with the reading's blobs. Then the canonical annotation is defined,
annotates the reading, and the heap term represents it under the table's keying. -/
theorem annotation_canon {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))} {n : Nat}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {e : Ixon.Expr}
    {kp : SourceValue F} {E_rd : Ix.Kernel.Expr .anon} {root : F} {tree : L1.BinderTreeData}
    {plan : List Core.KLevel}
    (hn : n < 4294967296)
    (hagree : L1.BlobReadAgreement (readCtx t blob).blob blobs)
    (raw : L1.RawConvExpr src.refs.toList [] src.univs.toList src.sharing.toList blobs
      h 4294967295 e kp)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData src.binders.toList) tree)
    (planned : L1.binderRootPlan tree src.sharing.toList root e = some plan)
    (levels : L1.HeapBinderLevels h kp plan)
    (hread : (exprReader t blob src id self).read e = .ok E_rd)
    (hlbb : E_rd.looseBVarsBounded 0 = true)
    (hdef : E_rd.allLevelParamsDefined (List.range n) = true) :
    ∃ E' : Ix.Kernel.Expr .anon,
      canonAnn src (List.range n) root e E_rd = some E' ∧ Annotates E' E_rd ∧
      Core.TmC (Core.keyOf t) h (Core.posOf (List.range n) E') kp := by
  have hread' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) src
      (Ix.Kernel.Reader.recParam (List.range n)) self).read e = .ok E_rd := by
    rw [Assembly.recParam_range]
    exact hread
  obtain ⟨E', hann, htm, htrace⟩ :=
    raw.toTmCExactTrace_of_blobAgreement (recurAddrs := []) (κ := Core.keyOf t)
      (ps := List.range n) (by simp) (by simpa using hn) (readCtx_keyAt_inv ht blob)
      (fun _ _ _ _ hx => by simp at hx) hagree hread' hlbb hdef
  have hap := htrace plan levels []
  rw [List.append_nil] at hap
  refine ⟨E', ?_, hann, htm.toTmC⟩
  unfold canonAnn
  rw [canonTree_eq built, planned]
  show (L1.applyBinderTrace (fun level => Core.bmeta (L1.invPosLevel (List.range n) level))
    E_rd plan).map Prod.fst = some E'
  rw [hap]
  rfl

/-! ## The canonical constant -/

/-- **The canonical annotated constant of a definition payload**: the constant `d` declares
under the key `key` (`defnConst`), with the canonical annotations of its read type `ty₀`
(root `base`) and value `val₀` (root `base + 1`) in the record `src`. -/
noncomputable def canonDefn (key : Ix.Kernel.Key .anon) (src : Ixon.Constant) (base : F)
    (d : Ixon.Definition) (ty₀ val₀ : Ix.Kernel.Expr .anon) (hn : Ix.Kernel.ReducibilityHint) :
    Option (Ix.Kernel.ConstantInfo .anon) :=
  (canonAnn src (List.range d.lvls.toNat) base d.typ ty₀).bind fun ty' =>
    (canonAnn src (List.range d.lvls.toNat) (base + 1) d.value val₀).map fun val' =>
      defnConst d.kind ⟨key, List.range d.lvls.toNat, ty'⟩ val' hn

theorem canonDefn_eq {key : Ix.Kernel.Key .anon} {src : Ixon.Constant} {base : F}
    {d : Ixon.Definition} {ty₀ val₀ ty' val' : Ix.Kernel.Expr .anon}
    {hn : Ix.Kernel.ReducibilityHint}
    (hT : canonAnn src (List.range d.lvls.toNat) base d.typ ty₀ = some ty')
    (hV : canonAnn src (List.range d.lvls.toNat) (base + 1) d.value val₀ = some val') :
    canonDefn key src base d ty₀ val₀ hn =
      some (defnConst d.kind ⟨key, List.range d.lvls.toNat, ty'⟩ val' hn) := by
  unfold canonDefn
  rw [hT, hV]
  rfl

theorem canonDefn_inv {key : Ix.Kernel.Key .anon} {src : Ixon.Constant} {base : F}
    {d : Ixon.Definition} {ty₀ val₀ : Ix.Kernel.Expr .anon} {hn : Ix.Kernel.ReducibilityHint}
    {cn : Ix.Kernel.ConstantInfo .anon} (h : canonDefn key src base d ty₀ val₀ hn = some cn) :
    ∃ ty' val' : Ix.Kernel.Expr .anon,
      canonAnn src (List.range d.lvls.toNat) base d.typ ty₀ = some ty' ∧
      canonAnn src (List.range d.lvls.toNat) (base + 1) d.value val₀ = some val' ∧
      cn = defnConst d.kind ⟨key, List.range d.lvls.toNat, ty'⟩ val' hn := by
  unfold canonDefn at h
  cases hT : canonAnn src (List.range d.lvls.toNat) base d.typ ty₀ with
  | none =>
    rw [hT] at h
    have h' : (none : Option (Ix.Kernel.ConstantInfo .anon)) = some cn := h
    cases h'
  | some ty' =>
    rw [hT] at h
    cases hV : canonAnn src (List.range d.lvls.toNat) (base + 1) d.value val₀ with
    | none =>
      rw [hV] at h
      have h' : (none : Option (Ix.Kernel.ConstantInfo .anon)) = some cn := h
      cases h'
    | some val' =>
      rw [hV] at h
      have h' : some (defnConst d.kind ⟨key, List.range d.lvls.toNat, ty'⟩ val' hn) = some cn := h
      exact ⟨ty', val', rfl, rfl, (Option.some.inj h').symm⟩

theorem defnConst_name (kind : Ix.DefKind) (cv : Ix.Kernel.ConstantVal .anon)
    (value : Ix.Kernel.Expr .anon) (hn : Ix.Kernel.ReducibilityHint) :
    (defnConst kind cv value hn).name = cv.name := by
  cases kind <;> rfl

/-- **The declaration a definition record's constant is checked as**, by its kind: a
definition under the hint `hn`, a theorem, or an opaque. It installs `defnConst`. -/
def defnDecl (kind : Ix.DefKind) (cv : Ix.Kernel.ConstantVal .anon)
    (value : Ix.Kernel.Expr .anon) (hn : Ix.Kernel.ReducibilityHint) :
    Ix.Kernel.Declaration .anon :=
  match kind with
  | .defn => .defnDecl cv value hn
  | .thm => .thmDecl cv value
  | .opaq => .opaqueDecl cv value

theorem installs_defnDecl (kind : Ix.DefKind) (cv : Ix.Kernel.ConstantVal .anon)
    (value : Ix.Kernel.Expr .anon) (hn : Ix.Kernel.ReducibilityHint) :
    IxVM.Consistency.installs (defnDecl kind cv value hn) = [defnConst kind cv value hn] := by
  cases kind <;> rfl

/-- The declaration of a definition record is never an axiom declaration. -/
theorem defnDecl_ne_axiomDecl (kind : Ix.DefKind) (cv : Ix.Kernel.ConstantVal .anon)
    (value : Ix.Kernel.Expr .anon) (hn : Ix.Kernel.ReducibilityHint)
    (cv' : Ix.Kernel.ConstantVal .anon) : defnDecl kind cv value hn ≠ .axiomDecl cv' := by
  cases kind <;> simp [defnDecl]

/-! ## Helpers -/

private theorem toUInt64_toNat_c {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

/-- A store that holds a record at an address holds bytes there that decode exactly to it. -/
theorem recordOf_inv {E : Ixon.Env} {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf E a = some c) :
    ∃ lc, E.consts.get? a = some lc ∧ Ixon.deConstantExact lc.rawBytes = .ok c := by
  unfold recordOf at h
  cases hget : E.consts.get? a with
  | none =>
    rw [hget] at h
    have h' : (none : Option Ixon.Constant) = some c := h
    cases h'
  | some lc =>
    rw [hget] at h
    refine ⟨lc, rfl, ?_⟩
    have h' : (Ixon.deConstantExact lc.rawBytes).toOption = some c := h
    cases hd : Ixon.deConstantExact lc.rawBytes with
    | error err =>
      rw [hd] at h'
      have h'' : (none : Option Ixon.Constant) = some c := h'
      cases h''
    | ok c' =>
      rw [hd] at h'
      have h'' : some c' = some c := h'
      rw [Option.some.inj h'']

/-- A level count and a represented type are a represented constant value, under any key. -/
theorem valRep_range {κ : _root_.Address → Core.KKey} {h : Heap F} {n : Nat}
    {tyPtr : SourceValue F} {key : Ix.Kernel.Key .anon} {ty' : Ix.Kernel.Expr .anon}
    (hn : n < 4294967296) (hty : Core.TmC κ h (Core.posOf (List.range n) ty') tyPtr) :
    Core.ValRep κ h (.field (n : F)) tyPtr ⟨key, List.range n, ty'⟩ := by
  have hlen : n = (List.range n).length := by simp
  exact ⟨congrArg (fun m : Nat => Value.field (m : F)) hlen, by simpa using hn, by simp, hty⟩

/-- **A converted definition value represents a constant whose type and value its two heap
terms represent**, under any keying and every hint. -/
theorem ciRep_defnValShape {κ : _root_.Address → Core.KKey} {h : Heap F}
    {d : Ixon.Definition} {tyPtr valPtr hint : SourceValue F} {key : Ix.Kernel.Key .anon}
    {ty' val' : Ix.Kernel.Expr .anon} (hnlvls : d.lvls.toNat < 4294967296)
    (hty : Core.TmC κ h (Core.posOf (List.range d.lvls.toNat) ty') tyPtr)
    (hval : Core.TmC κ h (Core.posOf (List.range d.lvls.toNat) val') valPtr)
    (hn : Ix.Kernel.ReducibilityHint) :
    Core.CIRep κ h (L1.defnValShape d tyPtr valPtr hint)
      (defnConst d.kind ⟨key, List.range d.lvls.toNat, ty'⟩ val' hn) := by
  have hlen : d.lvls.toNat = (List.range d.lvls.toNat).length := by simp
  have hvr : Core.ValRep κ h (.field (d.lvls.toNat : F)) tyPtr
      ⟨key, List.range d.lvls.toNat, ty'⟩ :=
    ⟨congrArg (fun n : Nat => Value.field (n : F)) hlen,
      by simpa using hnlvls, by simp, hty⟩
  cases hk : d.kind with
  | defn =>
    simp only [L1.defnValShape, hk]
    exact .defn hvr hval
  | thm =>
    simp only [L1.defnValShape, hk]
    exact .thm hvr hval
  | opaq =>
    simp only [L1.defnValShape, hk]
    exact .opaq hvr

/-- The references a record uses stay stored when one more constant is stored. -/
theorem usedRefsStored_cons {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {c : Ixon.Constant} (cn : Ix.Kernel.ConstantInfo .anon)
    (h : Decl.UsedRefsStored t env c) : Decl.UsedRefsStored t ⟨cn :: env.consts⟩ c := by
  intro i hi x hx
  obtain ⟨ci, hci⟩ := h i hi x hx
  by_cases hk : cn.name = Core.keyOf t x
  · exact ⟨cn, by rw [Ix.Kernel.Env.find?_cons, ite_eq_left hk]⟩
  · exact ⟨ci, by rw [Ix.Kernel.Env.find?_cons, ite_eq_right hk]; exact hci⟩

/-! ## A standalone definition, theorem or opaque record -/

section Solo

variable {t : Ix.Kernel.RoleTable}

/-- **Every load of a held standalone definition, theorem or opaque record represents its
canonical constant.** The store `E` holds the record `c` at the address (exact decoding), in
Lean's logic; `ty₀`, `val₀` are the readings of its type and value over `E`'s blobs, well
scoped. Then for a `get_ci` at the address in calls that hash no collision with `E`, the
canonical annotations of the readings are defined and the returned pointer represents the
canonical constant, under every hint: under the table's keying, and under the keying of any
prefix that stores the references the record uses. -/
theorem get_ci_defn_canon (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) {a : Aiur.Library.Bytes.Address}
    {addr ptr : SourceValue F} {h h' : Heap F}
    (ha : Aiur.Library.Bytes.RepAddressRef Core.addrTy h a addr)
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) {c : Ixon.Constant}
    {d : Ixon.Definition} (hrec : recordOf E (Core.ixAddr a) = some c)
    (hinfo : c.info = .defn d) (hlogic : InLogic c) {ty₀ val₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) c id
      (soloSelf t (Core.ixAddr a))).read d.typ = .ok ty₀)
    (hval : (exprReader t (fun x => E.blobs.get? x) c id
      (soloSelf t (Core.ixAddr a))).read d.value = .ok val₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true)
    (hval_lbb : val₀.looseBVarsBounded 0 = true)
    (hval_def : val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true) :
    ∃ ty' val' : Ix.Kernel.Expr .anon,
      canonAnn c (List.range d.lvls.toNat) 0 d.typ ty₀ = some ty' ∧
      canonAnn c (List.range d.lvls.toNat) (0 + 1) d.value val₀ = some val' ∧
      Annotates ty' ty₀ ∧ Annotates val' val₀ ∧
      (∀ hn : Ix.Kernel.ReducibilityHint, Core.CIPtrRep (Core.keyOf t) h' ptr
        (defnConst d.kind ⟨keyOf t (Core.ixAddr a), List.range d.lvls.toNat, ty'⟩ val' hn)) ∧
      (∀ (env : Ix.Kernel.Env .anon) (lim : Option Nat), Decl.UsedRefsStored t env c →
        ∀ hn : Ix.Kernel.ReducibilityHint,
          Core.CIPtrRep (Core.Ctx.stored ⟨E, env, t, lim⟩).κ h' ptr
            (defnConst d.kind ⟨keyOf t (Core.ixAddr a), List.range d.lvls.toNat, ty'⟩ val'
              hn)) := by
  obtain ⟨rawBytes, c', hh, haddr, hex, hres⟩ := L1.get_ci_trace_spec ha ev
  obtain ⟨lc, hget, hdec⟩ := recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hnc rawBytes hh haddr
  have hc : c = c' := by
    rw [hb, hdec] at hex
    exact Except.ok.inj hex
  subst hc
  unfold L1.GetCITraceResult at hres
  rw [hinfo] at hres
  obtain ⟨blobs, tree, v, hhp, built, hld, htr⟩ := hres
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    have hl := hlogic
    unfold InLogic at hl
    rw [hinfo] at hl
    exact hl
  have hrecur : L1.defnRecurAddrs d (Core.ixAddr a) = [] := by
    have hf := (L1.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
    simp [L1.defnRecurAddrs, hf]
  rw [hrecur] at htr
  obtain ⟨hnlvls, tyPtr, valPtr, hint, planT, planV, hv, rty, rval, hpT, hpV, hlT, hlV⟩ := htr
  subst hv
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    annotation_canon ht hnlvls hagree rty built hpT hlT hty hty_lbb hty_def
  obtain ⟨val', hcV, hannV, htmV⟩ :=
    annotation_canon ht hnlvls hagree rval built hpV hlV hval hval_lbb hval_def
  refine ⟨ty', val', hcT, hcV, hannT, hannV,
    fun hn => ⟨_, hld, ciRep_defnValShape hnlvls htmT htmV hn⟩,
    fun env lim hstored hn => ⟨_, hld, ?_⟩⟩
  have heT : ∀ i, i ∈ exprRefIdxs d.typ → i ∈ usedRefIdxs c := by
    intro i hi
    unfold usedRefIdxs
    rw [hinfo]
    exact List.mem_append_right _ (List.mem_append_left _ hi)
  have heV : ∀ i, i ∈ exprRefIdxs d.value → i ∈ usedRefIdxs c := by
    intro i hi
    unfold usedRefIdxs
    rw [hinfo]
    exact List.mem_append_right _ (List.mem_append_right _ hi)
  exact ciRep_defnValShape hnlvls
    (Decl.tmC_stored_of_usedRefs (E₀ := E) (lim := lim) rty heT hstored htmT)
    (Decl.tmC_stored_of_usedRefs (E₀ := E) (lim := lim) rval heV hstored htmV) hn

/-- **The canonical constant of a standalone definition, theorem or opaque record reloads**
at every store `E'` that holds the record `c` at `a` (exact decoding) and over whose blobs
the record's type and value read as `ty₀`, `val₀`, under the keying of any prefix `env` that
stores the references the record uses. The run of a later load is only required to be good
for `E'` (`Decl.ReloadsAs`): no collision with `E'`, bounded. -/
theorem reloadsAs_defn (ht : t.check = .ok ()) {E' : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {a : _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hrec : recordOf E' a = some c) (hinfo : c.info = .defn d) (hlogic : InLogic c)
    {ty₀ val₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E'.blobs.get? x) c id (soloSelf t a)).read d.typ = .ok ty₀)
    (hval : (exprReader t (fun x => E'.blobs.get? x) c id (soloSelf t a)).read d.value =
      .ok val₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true)
    (hval_lbb : val₀.looseBVarsBounded 0 = true)
    (hval_def : val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true)
    (hstored : Decl.UsedRefsStored t env c)
    {hn : Ix.Kernel.ReducibilityHint} {cn : Ix.Kernel.ConstantInfo .anon}
    (hcn : canonDefn (keyOf t a) c 0 d ty₀ val₀ hn = some cn) :
    Decl.ReloadsAs E' t env cn := by
  obtain ⟨ty', val', hcT, hcV, hcn'⟩ := canonDefn_inv hcn
  subst hcn'
  intro addr ptr h h' cs a' ev hgood ha hkey
  have hk : Core.keyOf t (Core.ixAddr a') = Core.keyOf t a :=
    hkey.trans (defnConst_name _ _ _ _)
  have haddr : Core.ixAddr a' = a := Assembly.keyOf_injective ht hk
  subst haddr
  obtain ⟨ty'', val'', hcT', hcV', -, -, -, hrep⟩ :=
    get_ci_defn_canon ht hgood.1 ha ev hrec hinfo hlogic hty hval hty_lbb hty_def hval_lbb
      hval_def
  have e1 : ty'' = ty' := Option.some.inj (hcT'.symm.trans hcT)
  have e2 : val'' = val' := Option.some.inj (hcV'.symm.trans hcV)
  subst e1
  subst e2
  exact hrep env none hstored hn

/-- **The reload a step needs**: the canonical constant reloads under the keying of the
prefix that stores it, where the prefix before it stores the references the record uses, at
every store `E'` that holds the record and at least the blobs of a store `E` over which the
record reads as `ty₀`, `val₀`. -/
theorem reloadsAs_defn_cons (ht : t.check = .ok ()) {E E' : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {a : _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hrec : recordOf E' a = some c) (hinfo : c.info = .defn d) (hlogic : InLogic c)
    (hblobs : ∀ x b, E.blobs.get? x = some b → E'.blobs.get? x = some b)
    {ty₀ val₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) c id (soloSelf t a)).read d.typ = .ok ty₀)
    (hval : (exprReader t (fun x => E.blobs.get? x) c id (soloSelf t a)).read d.value =
      .ok val₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true)
    (hval_lbb : val₀.looseBVarsBounded 0 = true)
    (hval_def : val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true)
    (hstored : Decl.UsedRefsStored t env c)
    {hn : Ix.Kernel.ReducibilityHint} {cn : Ix.Kernel.ConstantInfo .anon}
    (hcn : canonDefn (keyOf t a) c 0 d ty₀ val₀ hn = some cn) :
    Decl.ReloadsAs E' t ⟨cn :: env.consts⟩ cn :=
  reloadsAs_defn ht hrec hinfo hlogic
    (ReaderReads.exprReader_mono (blob := fun x => E.blobs.get? x)
      (blob' := fun x => E'.blobs.get? x) hblobs hty)
    (ReaderReads.exprReader_mono (blob := fun x => E.blobs.get? x)
      (blob' := fun x => E'.blobs.get? x) hblobs hval)
    hty_lbb hty_def hval_lbb hval_def (usedRefsStored_cons cn hstored) hcn

end Solo

/-! ## A definition member of a block -/

section Member

variable {t : Ix.Kernel.RoleTable}

/-- **Every load of a held definition member of a block represents its canonical constant.**
The store `E` holds the projection record `c` at the address and the block `cb` at the block
address it names (exact decodings), the block in Lean's logic; the member is the definition
`d`; `ty₀`, `val₀` are the readings of its type and value in the block, over `E`'s blobs, well
scoped. Then for a `get_ci` at the address in calls that hash no collision with `E`, the
canonical annotations (at the member's root offset in the block) are defined and the returned
pointer represents the canonical constant, under every hint: under the table's keying, and
under the keying of any prefix that stores the references the block uses. -/
theorem get_ci_dprj_canon (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) {a : Aiur.Library.Bytes.Address}
    {addr ptr : SourceValue F} {h h' : Heap F}
    (ha : Aiur.Library.Bytes.RepAddressRef Core.addrTy h a addr)
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) {c cb : Ixon.Constant}
    {p : Ixon.DefinitionProj} {ms : Array Ixon.MutConst} {d : Ixon.Definition}
    (hrec : recordOf E (Core.ixAddr a) = some c) (hinfo : c.info = .dPrj p)
    (hblock : recordOf E p.block = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[p.idx.toNat]? = some (.defn d)) (hlogic : InLogic cb)
    {ty₀ val₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t p.block ms)).read d.typ = .ok ty₀)
    (hval : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t p.block ms)).read d.value = .ok val₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true)
    (hval_lbb : val₀.looseBVarsBounded 0 = true)
    (hval_def : val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true) :
    ∃ ty' val' : Ix.Kernel.Expr .anon,
      canonAnn cb (List.range d.lvls.toNat)
        ((L1.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) d.typ ty₀ = some ty' ∧
      canonAnn cb (List.range d.lvls.toNat)
        (((L1.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) + 1) d.value val₀ = some val' ∧
      Annotates ty' ty₀ ∧ Annotates val' val₀ ∧
      (∀ hn : Ix.Kernel.ReducibilityHint, Core.CIPtrRep (Core.keyOf t) h' ptr
        (defnConst d.kind ⟨keyOf t (Core.ixAddr a), List.range d.lvls.toNat, ty'⟩ val' hn)) ∧
      (∀ (env : Ix.Kernel.Env .anon) (lim : Option Nat), Decl.UsedRefsStored t env cb →
        ∀ hn : Ix.Kernel.ReducibilityHint,
          Core.CIPtrRep (Core.Ctx.stored ⟨E, env, t, lim⟩).κ h' ptr
            (defnConst d.kind ⟨keyOf t (Core.ixAddr a), List.range d.lvls.toNat, ty'⟩ val'
              hn)) := by
  obtain ⟨rawBytes, c', hh, haddr, hex, hres⟩ := L1.get_ci_trace_spec ha ev
  obtain ⟨lc, hget, hdec⟩ := recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hnc rawBytes hh haddr
  have hc : c = c' := by
    rw [hb, hdec] at hex
    exact Except.ok.inj hex
  subst hc
  unfold L1.GetCITraceResult at hres
  rw [hinfo] at hres
  obtain ⟨hidx, blkBytes, cb', ms', d', blobs, tree, v, hhB, haB, hexB, hcb, hms, hhp, built,
    hld, htr⟩ := hres
  obtain ⟨lcB, hgetB, hdecB⟩ := recordOf_inv hblock
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hnc blkBytes hhB haB
  have hcB : cb = cb' := by
    rw [hbB, hdecB] at hexB
    exact Except.ok.inj hexB
  subst hcB
  have hmsEq : ms = ms' := Ixon.ConstantInfo.muts.inj (hmuts.symm.trans hcb)
  subst hmsEq
  have hms' : ms[p.idx.toNat]? = some (.defn d') := by
    rw [← Array.getElem?_toList]
    exact hms
  have hdEq : d = d' := Ixon.MutConst.defn.inj (Option.some.inj (hmem.symm.trans hms'))
  subst hdEq
  have hmem' : Ixon.MutConst.defn d ∈ ms.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hmem)
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    have hl := hlogic
    unfold InLogic at hl
    rw [hmuts] at hl
    exact hl (.defn d) hmem'
  have hrecur : L1.defnMemberRecurAddrs d p.block ms.toList = [] := by
    have hf := (L1.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
    simp [L1.defnMemberRecurAddrs, hf]
  rw [hrecur] at htr
  obtain ⟨hnlvls, tyPtr, valPtr, hint, planT, planV, hv, rty, rval, hpT, hpV, hlT, hlV⟩ := htr
  subst hv
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    annotation_canon ht hnlvls hagree rty built hpT hlT hty hty_lbb hty_def
  obtain ⟨val', hcV, hannV, htmV⟩ :=
    annotation_canon ht hnlvls hagree rval built hpV hlV hval hval_lbb hval_def
  refine ⟨ty', val', hcT, hcV, hannT, hannV,
    fun hn => ⟨_, hld, ciRep_defnValShape hnlvls htmT htmV hn⟩,
    fun env lim hstored hn => ⟨_, hld, ?_⟩⟩
  have hused : ∀ i, i ∈ exprRefIdxs d.typ ++ exprRefIdxs d.value → i ∈ usedRefIdxs cb := by
    intro i hi
    unfold usedRefIdxs
    rw [hmuts]
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨.defn d, hmem', hi⟩)
  exact ciRep_defnValShape hnlvls
    (Decl.tmC_stored_of_usedRefs (E₀ := E) (lim := lim) rty
      (fun i hi => hused i (List.mem_append_left _ hi)) hstored htmT)
    (Decl.tmC_stored_of_usedRefs (E₀ := E) (lim := lim) rval
      (fun i hi => hused i (List.mem_append_right _ hi)) hstored htmV) hn

/-- **The canonical constant of a definition member reloads** at every store `E'` that holds
the member's projection record `c` at `a` and the block `cb` at the block address it names
(exact decodings), and over whose blobs the member's type and value read as `ty₀`, `val₀`,
under the keying of any prefix `env` that stores the references the block uses. -/
theorem reloadsAs_dprj (ht : t.check = .ok ()) {E' : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {a : _root_.Address} {c cb : Ixon.Constant} {p : Ixon.DefinitionProj}
    {ms : Array Ixon.MutConst} {d : Ixon.Definition}
    (hrec : recordOf E' a = some c) (hinfo : c.info = .dPrj p)
    (hblock : recordOf E' p.block = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[p.idx.toNat]? = some (.defn d)) (hlogic : InLogic cb)
    {ty₀ val₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E'.blobs.get? x) cb id
      (blockSelf t p.block ms)).read d.typ = .ok ty₀)
    (hval : (exprReader t (fun x => E'.blobs.get? x) cb id
      (blockSelf t p.block ms)).read d.value = .ok val₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true)
    (hval_lbb : val₀.looseBVarsBounded 0 = true)
    (hval_def : val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true)
    (hstored : Decl.UsedRefsStored t env cb)
    {hn : Ix.Kernel.ReducibilityHint} {cn : Ix.Kernel.ConstantInfo .anon}
    (hcn : canonDefn (keyOf t a) cb ((L1.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) d
      ty₀ val₀ hn = some cn) :
    Decl.ReloadsAs E' t env cn := by
  obtain ⟨ty', val', hcT, hcV, hcn'⟩ := canonDefn_inv hcn
  subst hcn'
  intro addr ptr h h' cs a' ev hgood ha hkey
  have hk : Core.keyOf t (Core.ixAddr a') = Core.keyOf t a :=
    hkey.trans (defnConst_name _ _ _ _)
  have haddr : Core.ixAddr a' = a := Assembly.keyOf_injective ht hk
  subst haddr
  obtain ⟨ty'', val'', hcT', hcV', -, -, -, hrep⟩ :=
    get_ci_dprj_canon ht hgood.1 ha ev hrec hinfo hblock hmuts hmem hlogic hty hval hty_lbb
      hty_def hval_lbb hval_def
  have e1 : ty'' = ty' := Option.some.inj (hcT'.symm.trans hcT)
  have e2 : val'' = val' := Option.some.inj (hcV'.symm.trans hcV)
  subst e1
  subst e2
  exact hrep env none hstored hn

/-- **The reload a step needs, for member `k` of the block at `B`**: the canonical constant
reloads under the keying of the prefix that stores it, where the prefix before it stores the
references the block uses, at every store `E'` that holds the member's projection record at
its constant address, the block at `B`, and at least the blobs of a store `E` over which the
member reads as `ty₀`, `val₀`. -/
theorem reloadsAs_member_cons (ht : t.check = .ok ()) {E E' : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {k : Nat} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {d : Ixon.Definition} (hk64 : k < UInt64.size)
    (hproj : recordOf E' (memberAddr B k (.defn d)) = some (memberProjection B k (.defn d)))
    (hblock : recordOf E' B = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[k]? = some (.defn d)) (hlogic : InLogic cb)
    (hblobs : ∀ x b, E.blobs.get? x = some b → E'.blobs.get? x = some b)
    {ty₀ val₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t B ms)).read d.typ =
      .ok ty₀)
    (hval : (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t B ms)).read d.value =
      .ok val₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true)
    (hval_lbb : val₀.looseBVarsBounded 0 = true)
    (hval_def : val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true)
    (hstored : Decl.UsedRefsStored t env cb)
    {hn : Ix.Kernel.ReducibilityHint} {cn : Ix.Kernel.ConstantInfo .anon}
    (hcn : canonDefn (keyOf t (memberAddr B k (.defn d))) cb
      ((L1.mutsRootOffset ms.toList k : Nat) : F) d ty₀ val₀ hn = some cn) :
    Decl.ReloadsAs E' t ⟨cn :: env.consts⟩ cn := by
  have hkk : k.toUInt64.toNat = k := toUInt64_toNat_c hk64
  have hinfo : (memberProjection B k (.defn d)).info = .dPrj ⟨k.toUInt64, B⟩ := rfl
  have hmem' : ms[(⟨k.toUInt64, B⟩ : Ixon.DefinitionProj).idx.toNat]? = some (.defn d) := by
    show ms[k.toUInt64.toNat]? = some (.defn d)
    rw [hkk]
    exact hmem
  have hcn' : canonDefn (keyOf t (memberAddr B k (.defn d))) cb
      ((L1.mutsRootOffset ms.toList (⟨k.toUInt64, B⟩ : Ixon.DefinitionProj).idx.toNat : Nat) : F)
      d ty₀ val₀ hn = some cn := by
    show canonDefn (keyOf t (memberAddr B k (.defn d))) cb
      ((L1.mutsRootOffset ms.toList k.toUInt64.toNat : Nat) : F) d ty₀ val₀ hn = some cn
    rw [hkk]
    exact hcn
  exact reloadsAs_dprj (p := ⟨k.toUInt64, B⟩) ht hproj hinfo hblock hmuts hmem' hlogic
    (ReaderReads.exprReader_mono (blob := fun x => E.blobs.get? x)
      (blob' := fun x => E'.blobs.get? x) hblobs hty)
    (ReaderReads.exprReader_mono (blob := fun x => E.blobs.get? x)
      (blob' := fun x => E'.blobs.get? x) hblobs hval)
    hty_lbb hty_def hval_lbb hval_def (usedRefsStored_cons cn hstored) hcn'

end Member

/-! ## An axiom record -/

section Axio

variable {t : Ix.Kernel.RoleTable}

/-- **Every load of a held axiom record represents the axiom with the canonical annotation of
its read type.** The store `E` holds the record `c` at the address (exact decoding); `ty₀` is
the reading of its type over `E`'s blobs, well scoped. Then for a `get_ci` at the address in
calls that hash no collision with `E`, the canonical annotation of the reading (at root `0`)
is defined and the returned pointer represents the axiom of that type: under the table's
keying, and under the keying of any prefix that stores the references the record uses. -/
theorem get_ci_axio_canon (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) {a : Aiur.Library.Bytes.Address}
    {addr ptr : SourceValue F} {h h' : Heap F}
    (ha : Aiur.Library.Bytes.RepAddressRef Core.addrTy h a addr)
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) {c : Ixon.Constant}
    {ax : Ixon.Axiom} (hrec : recordOf E (Core.ixAddr a) = some c)
    (hinfo : c.info = .axio ax) {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) c id (fun _ => none)).read ax.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ax.lvls.toNat) = true) :
    ∃ ty' : Ix.Kernel.Expr .anon,
      canonAnn c (List.range ax.lvls.toNat) 0 ax.typ ty₀ = some ty' ∧ Annotates ty' ty₀ ∧
      Core.CIPtrRep (Core.keyOf t) h' ptr
        (.axiomInfo ⟨keyOf t (Core.ixAddr a), List.range ax.lvls.toNat, ty'⟩) ∧
      (∀ (env : Ix.Kernel.Env .anon) (lim : Option Nat), Decl.UsedRefsStored t env c →
        Core.CIPtrRep (Core.Ctx.stored ⟨E, env, t, lim⟩).κ h' ptr
          (.axiomInfo ⟨keyOf t (Core.ixAddr a), List.range ax.lvls.toNat, ty'⟩)) := by
  obtain ⟨rawBytes, c', hh, haddr, hex, hres⟩ := L1.get_ci_trace_spec ha ev
  obtain ⟨lc, hget, hdec⟩ := recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hnc rawBytes hh haddr
  have hc : c = c' := by
    rw [hb, hdec] at hex
    exact Except.ok.inj hex
  subst hc
  unfold L1.GetCITraceResult at hres
  rw [hinfo] at hres
  obtain ⟨blobs, tree, v, hhp, built, hld, htr⟩ := hres
  obtain ⟨hnlvls, tyPtr, plan, hv, rty, hp, hl⟩ := htr
  subst hv
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    annotation_canon ht hnlvls hagree rty built hp hl hty hty_lbb hty_def
  refine ⟨ty', hcT, hannT, ⟨_, hld, .axio (valRep_range hnlvls htmT)⟩,
    fun env lim hstored => ⟨_, hld, .axio (valRep_range hnlvls ?_)⟩⟩
  have heT : ∀ i, i ∈ exprRefIdxs ax.typ → i ∈ usedRefIdxs c := by
    intro i hi
    unfold usedRefIdxs
    rw [hinfo]
    exact List.mem_append_right _ hi
  exact Decl.tmC_stored_of_usedRefs (E₀ := E) (lim := lim) rty heT hstored htmT

/-- **The axiom with the canonical annotation of its read type reloads** at every store `E'`
that holds the record `c` at `a` (exact decoding) and over whose blobs the record's type
reads as `ty₀`, under the keying of any prefix `env` that stores the references the record
uses. -/
theorem reloadsAs_axio (ht : t.check = .ok ()) {E' : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {a : _root_.Address} {c : Ixon.Constant} {ax : Ixon.Axiom}
    (hrec : recordOf E' a = some c) (hinfo : c.info = .axio ax)
    {ty₀ ty' : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E'.blobs.get? x) c id (fun _ => none)).read ax.typ =
      .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ax.lvls.toNat) = true)
    (hstored : Decl.UsedRefsStored t env c)
    (hcn : canonAnn c (List.range ax.lvls.toNat) 0 ax.typ ty₀ = some ty') :
    Decl.ReloadsAs E' t env (.axiomInfo ⟨keyOf t a, List.range ax.lvls.toNat, ty'⟩) := by
  intro addr ptr h h' cs a' ev hgood ha hkey
  have hk : Core.keyOf t (Core.ixAddr a') = Core.keyOf t a := hkey
  have haddr : Core.ixAddr a' = a := Assembly.keyOf_injective ht hk
  subst haddr
  obtain ⟨ty'', hcT', -, -, hrep⟩ :=
    get_ci_axio_canon ht hgood.1 ha ev hrec hinfo hty hty_lbb hty_def
  have e1 : ty'' = ty' := Option.some.inj (hcT'.symm.trans hcn)
  subst e1
  exact hrep env none hstored

end Axio

end IxVM.Refinement.LoadedReads
