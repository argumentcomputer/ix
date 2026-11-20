import IxVMRefinement.Binding.ShapeIffNonempty
import IxVMRefinement.Binding.EqnsValidation
import IxVMRefinement.Binding.MemberKindPins
import IxVMRefinement.Binding.MemberFamilyKey

/-! # The stored `Iff` and `Nonempty` families at groups 16 and 17

Groups 16 and 17 hold the two prerequisite inductive families the standard axioms read:
`Iff`, `Iff.intro`, `Iff.rec` (group 16) and `Nonempty`, `Nonempty.intro`, `Nonempty.rec`
(group 17). For each of the six roles, `KernelRoles::validate_role` checks the bound record's
level count against `role_levels` and delegates to `KernelRoles::validate_member`, which checks
the loaded type well scoped, pins it against `role_type`, and pins the loaded constant's kind
and counts (inductive constructor count, constructor parameter and field counts, recursor major
index and rule prefix). Joined to the closure's kept declarations (`GroupKept`) and the pinned
`Eq` basis constant (`TableShape.pins .eqK`), this proves `IffPinned` at group 16 and
`NonemptyPinned` at group 17, closing `RoleFreeShapes` at every shape group.

* `stdInduct_stored`, `stdCtor_stored`, `stdRec_stored`: the stored inductive, constructor, and
  recursor of `Iff` (group 16) and `Nonempty` (group 17) match their `stdAxiomOk` pins and
  counts; the inductive also fixes the level count read through `IndKeyAt`.
* `iffPinned_of_group16`, `nonemptyPinned_of_group17`: `IffPinned` at group 16 and
  `NonemptyPinned` at group 17 after the group's closure.
* `roleFreeShapes_iffNonempty`: `RoleFreeShapes` at groups 16 and 17 at every binding run.
* `groupWithoutRoleUnit_bindingRun`: `AtGroups (BindingRun calls) (RoleFreeShapes FormerOpenTraceAt)`
  for every call list.
-/

universe u

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Role)
open Ix.Kernel.Semantics (NativeFam)

/-! ## The six roles and their pins -/

/-- The six roles of the `Iff` and `Nonempty` families. -/
private def stdMemberRoles : List Role :=
  [.iff, .iffIntro, .iffRec, .nonempty, .nonemptyIntro, .nonemptyRec]

/-- The semantic pin that `stdAxiomOk` requires for each of the six family roles. -/
def stdMemberPin : Role → Ix.Kernel.ConstantVal .anon
  | .iff => Ix.Kernel.iffA.toConstantVal
  | .iffIntro => Ix.Kernel.iffIntroA.toConstantVal
  | .iffRec => Ix.Kernel.iffRecA.toConstantVal
  | .nonempty => Ix.Kernel.nonemptyA.toConstantVal
  | .nonemptyIntro => Ix.Kernel.nonemptyIntroA.toConstantVal
  | .nonemptyRec => Ix.Kernel.nonemptyRecA.toConstantVal
  | _ => Ix.Kernel.iffA.toConstantVal

set_option maxRecDepth 100000 in
private theorem stdMemberPin_decided {r : Role} {n : Nat} (which : StdMemberLevels r n) :
    (specTypeRaw r).map Ix.Kernel.Expr.erasePw = some (stdMemberPin r).type.erasePw ∧
      (stdMemberPin r).levelParams = List.range n ∧ (stdMemberPin r).name = .role r := by
  cases which <;> decide +kernel

private theorem stdMemberPin_spec {r : Role} {n : Nat} (which : StdMemberLevels r n) :
    (∃ T₀, specTypeRaw r = some T₀ ∧ T₀.erasePw = (stdMemberPin r).type.erasePw) ∧
      (stdMemberPin r).levelParams = List.range n ∧ (stdMemberPin r).name = .role r := by
  obtain ⟨hT, hlps, hname⟩ := stdMemberPin_decided which
  obtain ⟨T₀, hspec, her⟩ := Option.map_eq_some_iff.mp hT
  exact ⟨⟨T₀, hspec, her⟩, hlps, hname⟩

set_option maxRecDepth 100000 in
private theorem stdMember_decided {r : Role} {n : Nat} (which : StdMemberLevels r n) :
    r ∈ stdMemberRoles ∧ IxVM.Consistency.walkedRole r = true ∧
      ¬ (r ∈ RoleOps.opRoles ∨ r ∈ IxVM.Consistency.standardAxioms) ∧
      n < 18446744069414584321 := by
  cases which <;> decide +kernel

set_option maxRecDepth 100000 in
private theorem stdMember_notBasis : ∀ k : Ix.Kernel.BasisKind, ∀ r ∈ stdMemberRoles,
    ∀ ci ∈ (k.declsA : List (Ix.Kernel.ConstantInfo .anon)), ci.name ≠ .role r := by
  intro k
  cases k <;> decide +kernel

set_option maxRecDepth 100000 in
private theorem stdMember_groups :
    Role.iff ∈ IxVM.Consistency.roleGroup 16 ∧
    Role.iffIntro ∈ IxVM.Consistency.roleGroup 16 ∧
    Role.iffRec ∈ IxVM.Consistency.roleGroup 16 ∧
    Role.nonempty ∈ IxVM.Consistency.roleGroup 17 ∧
    Role.nonemptyIntro ∈ IxVM.Consistency.roleGroup 17 ∧
    Role.nonemptyRec ∈ IxVM.Consistency.roleGroup 17 := by
  decide +kernel

/-! ## Small helpers -/

private theorem find?_of_mem_nodup :
    ∀ (cs : List (Ix.Kernel.ConstantInfo .anon)) (ci : Ix.Kernel.ConstantInfo .anon),
      ci ∈ cs → (cs.map (·.name)).Nodup → (⟨cs⟩ : Ix.Kernel.Env .anon).find? ci.name = some ci
  | [], _, hm, _ => by cases hm
  | c :: cs, ci, hm, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [Ix.Kernel.Env.find?, List.find?_cons]
    rcases List.mem_cons.mp hm with rfl | hm'
    · simp
    · have hne : (c.name == ci.name) = false :=
        beq_false_of_ne fun he => hnd.1 (he ▸ List.mem_map.mpr ⟨ci, hm', rfl⟩)
      rw [hne]
      exact find?_of_mem_nodup cs ci hm' hnd.2

private theorem recordOf_up {R R' : Ixon.Env}
    (h : ∀ a lc, R.consts.get? a = some lc → R'.consts.get? a = some lc) :
    ∀ x c, IxVM.Consistency.recordOf R x = some c → IxVM.Consistency.recordOf R' x = some c := by
  intro x c hc
  unfold IxVM.Consistency.recordOf at hc ⊢
  cases hg : R.consts.get? x with
  | none => rw [hg] at hc; cases hc
  | some lc => rw [hg] at hc; rw [h x lc hg]; exact hc

private theorem block_eq {calls : List (Call F)} {E : Ixon.Env} (hS : LoadedReads.RunStore calls E)
    {cs_ld : List (Call F)} {E_ld : Ixon.Env} (hload : IxVM.Consistency.LoadedBy cs_ld E_ld)
    (hsub : ∀ cl ∈ cs_ld, cl ∈ calls) {B : _root_.Address} {lcB : Ixon.LazyConstant}
    {cb' cb : Ixon.Constant} (hgetB : E_ld.consts.get? B = some lcB)
    (hexB : Ixon.deConstantExact lcB.rawBytes = .ok cb')
    (hB : IxVM.Consistency.recordOf E B = some cb) : cb' = cb := by
  obtain ⟨hhB, haB⟩ := hload.1 B lcB hgetB
  have hrecB : Ix.Cert.recordAt E B = some cb := by
    rw [← hS.recordOf_eq_recordAt]
    exact hB
  exact hS.record_eq hrecB (Core.hashed_mono hsub hhB) haB hexB

private theorem nat_of_fieldCast_eq {a b : Nat}
    (ha : a < 18446744069414584321) (hb : b < 18446744069414584321)
    (h : ((a : Nat) : F) = ((b : Nat) : F)) : a = b :=
  (RolesAux.val_natCast ha).symm.trans ((congrArg ZMod.val h).trans (RolesAux.val_natCast hb))

private theorem defnValShape_tag {d : Ixon.Definition} {tyPtr valPtr hint : SourceValue F} :
    ∃ tag fs, L1.defnValShape d tyPtr valPtr hint = .construct kciEnum tag fs ∧
      (tag = "Defn" ∨ tag = "Opaque" ∨ tag = "Thm") := by
  unfold L1.defnValShape
  cases d.kind with
  | defn => exact ⟨"Defn", _, rfl, Or.inl rfl⟩
  | opaq => exact ⟨"Opaque", _, rfl, Or.inr (Or.inl rfl)⟩
  | thm => exact ⟨"Thm", _, rfl, Or.inr (Or.inr rfl)⟩

/-- A raw converted `KConstantInfo` value's tag restricts the decoded record's `ConstantInfo`
constructor. -/
private theorem rawCIRep_info_of_tag {E_ld : Ixon.Env} {h : Heap F} {a : _root_.Address}
    {c : Ixon.Constant} {tag : String} {fs : List (SourceValue F)}
    (hraw : L1.RawCIRep E_ld h a c (.construct kciEnum tag fs)) :
    (tag = "Induct" → ∃ p, c.info = .iPrj p) ∧
    (tag = "Ctor" → ∃ p, c.info = .cPrj p) ∧
    (tag = "Rec" → (∃ rc, c.info = .recr rc) ∨ (∃ p, c.info = .rPrj p)) := by
  unfold L1.RawCIRep at hraw
  cases hi : c.info with
  | defn d =>
    rw [hi] at hraw
    obtain ⟨_, -, -, _, _, _, hv, -⟩ := hraw
    obtain ⟨_, _, hd, hts⟩ := defnValShape_tag
    rw [hd] at hv
    have ht := (Value.construct.inj hv).2.1
    rcases hts with rfl | rfl | rfl <;>
      exact ⟨fun h => absurd (ht.symm.trans h) (by decide),
        fun h => absurd (ht.symm.trans h) (by decide),
        fun h => absurd (ht.symm.trans h) (by decide)⟩
  | axio ax =>
    rw [hi] at hraw
    obtain ⟨_, -, -, _, hv, -⟩ := hraw
    have ht := (Value.construct.inj hv).2.1
    exact ⟨fun h => absurd (ht.symm.trans h) (by decide),
      fun h => absurd (ht.symm.trans h) (by decide),
      fun h => absurd (ht.symm.trans h) (by decide)⟩
  | quot q =>
    rw [hi] at hraw
    obtain ⟨_, -, -, _, hv, -⟩ := hraw
    have ht := (Value.construct.inj hv).2.1
    exact ⟨fun h => absurd (ht.symm.trans h) (by decide),
      fun h => absurd (ht.symm.trans h) (by decide),
      fun h => absurd (ht.symm.trans h) (by decide)⟩
  | recr rc =>
    rw [hi] at hraw
    obtain ⟨_, -, raw⟩ := hraw
    obtain ⟨-, -, -, -, -, -, _, _, _, _, -, -, hv, -⟩ := raw
    have ht := (Value.construct.inj hv).2.1
    exact ⟨fun h => absurd (ht.symm.trans h) (by decide),
      fun h => absurd (ht.symm.trans h) (by decide),
      fun _ => Or.inl ⟨rc, rfl⟩⟩
  | dPrj p =>
    rw [hi] at hraw
    obtain ⟨-, _, _, _, _, _, -, -, -, -, -, -, -, -, raw⟩ := hraw
    obtain ⟨-, _, _, _, hv, -⟩ := raw
    obtain ⟨_, _, hd, hts⟩ := defnValShape_tag
    rw [hd] at hv
    have ht := (Value.construct.inj hv).2.1
    rcases hts with rfl | rfl | rfl <;>
      exact ⟨fun h => absurd (ht.symm.trans h) (by decide),
        fun h => absurd (ht.symm.trans h) (by decide),
        fun h => absurd (ht.symm.trans h) (by decide)⟩
  | iPrj p =>
    rw [hi] at hraw
    obtain ⟨-, _, _, _, _, _, -, -, -, -, -, -, -, -, raw⟩ := hraw
    obtain ⟨-, -, -, -, -, _, _, _, -, -, hv, -⟩ := raw
    have ht := (Value.construct.inj hv).2.1
    exact ⟨fun _ => ⟨p, rfl⟩,
      fun h => absurd (ht.symm.trans h) (by decide),
      fun h => absurd (ht.symm.trans h) (by decide)⟩
  | cPrj p =>
    rw [hi] at hraw
    obtain ⟨-, -, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, raw⟩ := hraw
    obtain ⟨-, -, -, -, -, _, _, _, -, -, hv, -⟩ := raw
    have ht := (Value.construct.inj hv).2.1
    exact ⟨fun h => absurd (ht.symm.trans h) (by decide),
      fun _ => ⟨p, rfl⟩,
      fun h => absurd (ht.symm.trans h) (by decide)⟩
  | rPrj p =>
    rw [hi] at hraw
    obtain ⟨-, _, _, _, _, _, -, -, -, -, -, -, -, -, raw⟩ := hraw
    obtain ⟨-, -, -, -, -, -, _, _, _, _, -, -, hv, -⟩ := raw
    have ht := (Value.construct.inj hv).2.1
    exact ⟨fun h => absurd (ht.symm.trans h) (by decide),
      fun h => absurd (ht.symm.trans h) (by decide),
      fun _ => Or.inr ⟨p, rfl⟩⟩
  | muts _ =>
    rw [hi] at hraw
    exact False.elim hraw

/-! ## Common load, validation, and type-pin extraction -/

/-- From a member's raw converted type expression, its positional reading, and the observed
`MemberTypePin`, produce an annotation of the reading whose binder-erased form equals the role's
`stdMemberPin` type. -/
private theorem rawType_pin_erasePw {calls cs : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E : Ixon.Env} {r : Role} {n : Nat} (which : StdMemberLevels r n)
    (hbound : IxVM.Consistency.Bounded calls) (ht : t.check = .ok ())
    (hsub : ∀ cl ∈ cs, cl ∈ calls) (hnlt : n < 4294967296)
    {src : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {loaded beforeMember : Heap F} {x_tbl tyPtr : SourceValue F} {e : Ixon.Expr} {ty₀ : KExpr}
    (raw : L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      loaded 4294967295 e tyPtr)
    (hblob : ∀ x bs, (x, bs) ∈ blobs → E.blobs.get? x = some bs)
    (hself : ∀ i x m k, recurAddrs[i]? = some x → self i = some m → m = .ok k → k = keyOf t x)
    (hread : (IxVM.Consistency.exprReader t (fun x => E.blobs.get? x) src id self).read e = .ok ty₀)
    (htblLoaded : TableRep t loaded x_tbl) (extLoadedMember : Heap.Extends loaded beforeMember)
    (hpin : MemberTypePin x_tbl (.field (roleNum r)) (.field (n : F)) tyPtr beforeMember cs) :
    ∃ ty' : KExpr,
      IxVM.Consistency.Annotates ty' ty₀ ∧ ty'.erasePw = (stdMemberPin r).type.erasePw := by
  obtain ⟨s, s', p, m, m', u, spec, out, sc, tc, pc, extMS, evScope, hcallScope, extS'P,
    evRoleType, evPin⟩ := hpin
  have extLS : Heap.Extends loaded s := extLoadedMember.trans extMS
  obtain ⟨-, hlbb, hdef⟩ :=
    Assembly.validate_expr_well_scoped_spec hbound hnlt raw extLS hread evScope (hsub _ hcallScope)
  have hread' : (Ix.Kernel.Reader.MemberReader.mk'
      (IxVM.Consistency.readCtx t (fun x => E.blobs.get? x)) src
      (Ix.Kernel.Reader.recParam (List.range n)) self).read e = .ok ty₀ := by
    rw [Assembly.recParam_range]
    exact hread
  obtain ⟨ty', hvs, hrep⟩ :=
    L1.rawConvExpr_to_valRepExact (κ := keyOf t) (name := .role r) (ps := List.range n)
      (by simp) (by simp) hnlt
      (LoadedReads.readCtx_keyAt_inv ht (fun x => E.blobs.get? x)) hself hblob raw hread'
      hlbb hdef
  have hann : IxVM.Consistency.Annotates ty' ty₀ := hvs.2.2
  have htm : Decl.TmCExact (keyOf t) loaded ty' tyPtr := by
    have h4 := hrep.2.2.2
    rw [Decl.posOf_range] at h4
    exact h4
  have extLP : Heap.Extends loaded p := extLS.trans (evScope.heap_extends.trans extS'P)
  have htblP : TableRep t p x_tbl := htblLoaded.mono extLP
  obtain ⟨⟨T₀, hT₀, hT₀_er⟩, -, -⟩ := stdMemberPin_spec which
  have hpinE : ty'.erasePw = T₀.erasePw :=
    typePinned_erasePw (wf_of_check ht) hT₀ htblP (htm.mono extLP) evRoleType evPin
  exact ⟨ty', hann, hpinE.trans hT₀_er⟩

/-- For any of the six roles in groups 16 and 17, join `GroupKept` with the run's observed
`validate_role`: the stored constant is a kept reading of the bound record, loaded as a raw
`KConstantInfo` with the role's checked level count, passed into `validate_member`, with a
`MemberTypePin`. -/
private theorem stdMember_loaded {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun}
    {Rs : Nat → Ixon.Env} (hrun : BindingRun calls t ρ Rs) (hall : IxVM.Consistency.AllBound t)
    {g : Nat} {R R₁ R' : Ixon.Env} {env₁ : Ix.Kernel.Env .anon}
    (hadm : Admits ρ t g R R') (hle : StoreLe R₁ R') (hk : GroupKept t g R₁ env₁)
    {r : Role} {n : Nat} (which : StdMemberLevels r n) (hrg : r ∈ IxVM.Consistency.roleGroup g) :
    ∃ (a : _root_.Address) (c : Ixon.Constant) (ci ci₀ : Ix.Kernel.ConstantInfo .anon)
      (E_ld : Ixon.Env) (loaded beforeMember h' : Heap F) (cs loadCalls memberCalls : List (Call F))
      (x_rc x_tbl addr vci tyPtr res : SourceValue F) (tag : String) (rest : List (SourceValue F)),
      t.addressOf? r = some a ∧
      env₁.find? (.role r) = some ci ∧
      IxVM.Consistency.recordOf ρ.E₀ a = some c ∧
      IxVM.Consistency.ReadsRecord t (IxVM.Consistency.recordOf ρ.E₀)
        (fun x => ρ.E₀.blobs.get? x) a c ci₀ c.info ∧
      IxVM.Consistency.StoredAs ci ci₀ ∧
      IxVM.Consistency.LoadedBy loadCalls E_ld ∧
      (∀ cl ∈ loadCalls, cl ∈ calls) ∧
      L1.RawCIRep E_ld loaded a c vci ∧
      vci = .construct kciEnum tag (.field (n : F) :: tyPtr :: rest) ∧
      TableRep t loaded x_tbl ∧
      Heap.Extends loaded beforeMember ∧
      Obs.«KernelRoles::validate_member».Path x_rc x_tbl (.field (roleNum r)) addr vci beforeMember
        res h' memberCalls ∧
      (∀ cl ∈ cs, cl ∈ calls) ∧
      MemberTypePin x_tbl (.field (roleNum r)) (.field (n : F)) tyPtr beforeMember cs := by
  obtain ⟨hmem, hwalk, hnotUnit, -⟩ := stdMember_decided which
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall r)
  obtain ⟨ci, hf, hkp⟩ := hk.1 r hrg (Or.inl (Or.inl hwalk)) hnotUnit a ha
  have hname_ci : ci.name = .role r := Ix.Kernel.Semantics.Env.find?_name hf
  rcases hkp with ⟨kind, hbasis⟩ | ⟨-, ci₀, hrd₁, hst⟩
  · exact absurd hname_ci (stdMember_notBasis kind r hmem ci hbasis)
  have hRE : ∀ x c, IxVM.Consistency.recordOf R₁ x = some c →
      IxVM.Consistency.recordOf ρ.E₀ x = some c :=
    recordOf_up fun x lc h => hadm.loaded x lc (hle.1 x lc h)
  have hbE : ∀ x b, R₁.blobs.get? x = some b → ρ.E₀.blobs.get? x = some b :=
    fun x b h => hadm.loadedBlobs x b (hle.2 x b h)
  obtain ⟨c, hcE, hrr⟩ := IxVM.Consistency.ReadsIn.mono hRE hbE hrd₁
  have hval := hadm.validated r hrg
  obtain ⟨bAddr, -, -, -, hρ⟩ := hrun.observed
  have hval' : RoleValidationIn calls bAddr t g r := by
    have e : ρ.validated = (observedRun calls bAddr t ρ.E₀ ρ.rank).validated :=
      congrArg BRun.validated hρ
    rw [e] at hval
    exact hval
  obtain ⟨h, h', x_rc, x_tbl, res, cs, -, htbl, ev, hsub⟩ := hval'
  have htblR : TableRep t h x_tbl := htbl.toTableRep
  obtain ⟨addr, _, vci, tyPtr, tag, rest, _, loaded, beforeMember,
    _, loadCalls, memberCalls,
    evAddr, evGet, hsubLoad, hld, hvci_eq, extLoadedMember, mpath, -, htypePin⟩ :=
    validateRole_stdMember which (Obs.«KernelRoles::validate_role».obs ev)
  have hsubL : ∀ cl ∈ loadCalls, cl ∈ calls := fun cl hm => hsub cl (hsubLoad cl hm)
  obtain ⟨ext_ba, a', ha_beforeLoad, had⟩ := RoleVal.role_bound_addr_uncond htblR evAddr
  obtain rfl : a' = a := Option.some.inj (had.symm.trans ha)
  obtain ⟨b, hb_rep, rfl⟩ := ha_beforeLoad
  have hboundL : IxVM.Consistency.Bounded loadCalls := RomBound.bounded_mono hrun.bounded hsubL
  obtain ⟨-, _, E_ld, hhash, hblake, hloaded, hL1⟩ :=
    L1.get_ci_loadedL1_spec hboundL hb_rep evGet
  have hrecA : Ix.Cert.recordAt ρ.E₀ (ixAddr b) = some c := by
    rw [← hrun.runStore.recordOf_eq_recordAt]
    exact hcE
  obtain ⟨-, -, v, hld_v, hraw⟩ :=
    LoadedReads.loadedL1_record hrun.runStore hsubL hhash hblake hL1 hrecA
  obtain rfl : vci = v := (Except.ok.inj (hld_v.symm.trans hld)).symm
  exact ⟨ixAddr b, c, ci, ci₀, E_ld, loaded, beforeMember, h', cs, loadCalls, memberCalls,
    x_rc, x_tbl, addr, vci, tyPtr, res, tag, rest,
    ha, hf, hcE, hrr, hst, hloaded, hsubL, hraw, hvci_eq,
    htblR.mono (ext_ba.trans evGet.heap_extends), extLoadedMember, mpath, hsub, htypePin⟩

/-! ## The stored inductive, constructor, and recursor -/

/-- **The stored inductive of `Iff` (group 16) or `Nonempty` (group 17)** matches its `stdAxiomOk`
pin, and fixes the level count read through `IndKeyAt` in the run's store. -/
theorem stdInduct_stored {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun}
    {Rs : Nat → Ixon.Env} (hrun : BindingRun calls t ρ Rs) (hall : IxVM.Consistency.AllBound t)
    (ht : t.check = .ok ()) {g : Nat} {R R₁ R' : Ixon.Env} {env₁ : Ix.Kernel.Env .anon}
    (hadm : Admits ρ t g R R') (hle : StoreLe R₁ R') (hk : GroupKept t g R₁ env₁)
    {r : Role} {n : Nat} (which : StdMemberLevels r n) (whichInd : r = .iff ∨ r = .nonempty)
    (hrg : r ∈ IxVM.Consistency.roleGroup g) :
    (∃ cv caps, env₁.find? (.role r) = some (.indInfo cv caps) ∧
      cv.matchesPin (stdMemberPin r) = true) ∧
    (∀ B i ind, IxVM.Consistency.IndKeyAt t (IxVM.Consistency.recordOf ρ.E₀) (.role r) B i ind →
      ind.lvls.toNat = n) := by
  have htwf : t.wf = true := wf_of_check ht
  obtain ⟨-, -, -, hltF⟩ := stdMember_decided which
  obtain ⟨-, hpinLps, hpinName⟩ := stdMemberPin_spec which
  obtain ⟨a, c, ci, _, _, _, _, _, _, _, _, _, _, _, _, tyPtr, _, _, _,
    ha, hf, hcE, hrr, hst, hloaded, hsubL, hraw, hvci_eq,
    htblLoaded, extLoadedMember, mpath, hsubCs, htypePin⟩ :=
    stdMember_loaded hrun hall hadm hle hk which hrg
  obtain ⟨_, _, _, _, _, _, _, hv_ind⟩ := validateMember_induct whichInd mpath
  obtain ⟨p, hp⟩ := (rawCIRep_info_of_tag (hv_ind ▸ hraw)).1 rfl
  unfold L1.RawCIRep at hraw
  rw [hp] at hraw hrr
  dsimp only [IxVM.Consistency.ReadsRecord] at hrr
  obtain ⟨-, lcB, cb, ms, ind, blobs, hgetB, -, -, hexB, -, hcb', hms', hbl, rawInd⟩ := hraw
  obtain ⟨cb', ms', ind', ⟨hB, hmuts, hm, -, -, -⟩, hindReads⟩ := hrr
  obtain rfl := block_eq hrun.runStore hloaded hsubL hgetB hexB hB
  obtain rfl : ms = ms' := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hmuts)
  have hm' : ms[p.idx.toNat]? = some (.indc ind) := by
    rw [← Array.getElem?_toList]
    exact hms'
  obtain rfl : ind = ind' := Ixon.MutConst.indc.inj (Option.some.inj (hm'.symm.trans hm))
  obtain ⟨hlvls, -, -, -, -, tyPtr', _, _, -, -, hv_raw, rawTy⟩ := rawInd
  have hv_eq := hv_raw.symm.trans hvci_eq
  have hfs := (Value.construct.inj hv_eq).2.2
  simp only [List.cons.injEq] at hfs
  have hlvls_eq : ind.lvls.toNat = n :=
    nat_of_fieldCast_eq (by omega) hltF (Value.field.inj hfs.1)
  have hty_eq : tyPtr' = tyPtr := hfs.2.1
  subst hty_eq
  obtain ⟨ty₀, caps₀, hread, rfl⟩ := hindReads
  obtain ⟨ty', hann', hpinE⟩ := rawType_pin_erasePw which hrun.bounded ht hsubCs (hlvls_eq ▸ hlvls)
    rawTy (hrun.runStore.blob_of_table hloaded hsubL hbl) (LoadedReads.blockSelf_key t p.block ms)
    hread htblLoaded extLoadedMember htypePin
  refine ⟨?_, ?_⟩
  · cases ci with
    | indInfo cv caps =>
      obtain ⟨hname, hlps, hann⟩ := hst.1
      refine ⟨cv, caps, hf, matchesPin_of_fields ?_ ?_ ?_⟩
      · exact hname.trans ((keyOf_of_addressOf htwf ha).trans hpinName.symm)
      · exact hlps.trans ((congrArg List.range hlvls_eq).trans hpinLps.symm)
      · exact (annotates_erasePw_eq hann hann').trans hpinE
    | _ => exact False.elim hst.2
  · intro B₂ i₂ ind₂ hInd
    obtain ⟨a₂, c₂, p₂, cb₂, ms₂, hkey₂, hc₂, hinfo₂, rfl, rfl, hB₂, hmuts₂, hm₂, -, -, -⟩ := hInd
    have ha₂ : t.addressOf? r = some a₂ := addressOf_of_keyOf htwf hkey₂.symm
    obtain rfl : a₂ = a := Option.some.inj (ha₂.symm.trans ha)
    obtain rfl : c₂ = c := Option.some.inj (hc₂.symm.trans hcE)
    obtain rfl : p₂ = p := Ixon.ConstantInfo.iPrj.inj (hinfo₂.symm.trans hp)
    obtain rfl : cb₂ = cb := Option.some.inj (hB₂.symm.trans hB)
    obtain rfl : ms₂ = ms := Ixon.ConstantInfo.muts.inj (hmuts₂.symm.trans hmuts)
    obtain rfl : ind₂ = ind := Ixon.MutConst.indc.inj (Option.some.inj (hm₂.symm.trans hm))
    exact hlvls_eq

/-- **The stored constructor of `Iff` (group 16) or `Nonempty` (group 17)** has the required
parameter and field counts and matches its `stdAxiomOk` pin. -/
theorem stdCtor_stored {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun}
    {Rs : Nat → Ixon.Env} (hrun : BindingRun calls t ρ Rs) (hall : IxVM.Consistency.AllBound t)
    (ht : t.check = .ok ()) {g : Nat} {R R₁ R' : Ixon.Env} {env₁ : Ix.Kernel.Env .anon}
    (hadm : Admits ρ t g R R') (hle : StoreLe R₁ R') (hk : GroupKept t g R₁ env₁)
    {r family : Role} {n m : Nat} (which : StdMemberLevels r n) (pin : StdCtorPin r family m)
    (hrg : r ∈ IxVM.Consistency.roleGroup g) :
    ∃ cv, env₁.find? (.role r) = some (.ctorInfo cv m m) ∧
      cv.matchesPin (stdMemberPin r) = true := by
  have htwf : t.wf = true := wf_of_check ht
  obtain ⟨-, -, -, hltF⟩ := stdMember_decided which
  obtain ⟨-, hpinLps, hpinName⟩ := stdMemberPin_spec which
  have hm_lt : m < 18446744069414584321 := by cases pin <;> decide
  obtain ⟨a, _, ci, _, _, _, _, _, _, _, _, _, _, _, _, tyPtr, _, _, _,
    ha, hf, -, hrr, hst, hloaded, hsubL, hraw, hvci_eq,
    htblLoaded, extLoadedMember, mpath, hsubCs, htypePin⟩ :=
    stdMember_loaded hrun hall hadm hle hk which hrg
  obtain ⟨_, _, _, _, _, _, _, _, _, hv_ctor, -⟩ := validateMember_ctor pin mpath
  obtain ⟨p, hp⟩ := (rawCIRep_info_of_tag (hv_ctor ▸ hraw)).2.1 rfl
  unfold L1.RawCIRep at hraw
  rw [hp] at hraw hrr
  dsimp only [IxVM.Consistency.ReadsRecord] at hrr
  obtain ⟨-, -, lcB, cb, ms, ind, ct, blobs, hgetB, -, -, hexB, -, hcb', hms', hct', hbl,
    rawCtor⟩ := hraw
  obtain ⟨cb', ms', ind', ct', hB, hmuts, hm, hct, -, -, -, -, hctorReads⟩ := hrr
  obtain rfl := block_eq hrun.runStore hloaded hsubL hgetB hexB hB
  obtain rfl : ms = ms' := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hmuts)
  have hm' : ms[p.idx.toNat]? = some (.indc ind) := by
    rw [← Array.getElem?_toList]
    exact hms'
  obtain rfl : ind = ind' := Ixon.MutConst.indc.inj (Option.some.inj (hm'.symm.trans hm))
  have hct'' : ind.ctors[p.cidx.toNat]? = some ct := by
    rw [← Array.getElem?_toList]
    exact hct'
  obtain rfl : ct = ct' := Option.some.inj (hct''.symm.trans hct)
  obtain ⟨hlvls, -, hp56, hf56, -, tyPtr', _, _, -, -, hv_raw, rawTy⟩ := rawCtor
  have hv_eq := hv_raw.symm.trans hvci_eq
  have hfs := (Value.construct.inj hv_eq).2.2
  simp only [List.cons.injEq] at hfs
  have hlvls_eq : ct.lvls.toNat = n :=
    nat_of_fieldCast_eq (by omega) hltF (Value.field.inj hfs.1)
  have hty_eq : tyPtr' = tyPtr := hfs.2.1
  subst hty_eq
  have hfs' := (Value.construct.inj (hv_raw.symm.trans hv_ctor)).2.2
  simp only [List.cons.injEq, and_true] at hfs'
  obtain ⟨-, -, -, -, -, hpf, hff, -⟩ := hfs'
  have hparams_eq : ct.params.toNat = m :=
    nat_of_fieldCast_eq (by omega) hm_lt (Value.field.inj hpf)
  have hfields_eq : ct.fields.toNat = m :=
    nat_of_fieldCast_eq (by omega) hm_lt (Value.field.inj hff)
  obtain ⟨ty₀, hread, rfl⟩ := hctorReads
  obtain ⟨ty', hann', hpinE⟩ := rawType_pin_erasePw which hrun.bounded ht hsubCs (hlvls_eq ▸ hlvls)
    rawTy (hrun.runStore.blob_of_table hloaded hsubL hbl) (LoadedReads.blockSelf_key t p.block ms)
    hread htblLoaded extLoadedMember htypePin
  cases ci with
  | ctorInfo cv nP nF =>
    obtain ⟨⟨hname, hlps, hann⟩, hnP, hnF⟩ := hst
    have hnP' : nP = m := hnP.trans hparams_eq
    have hnF' : nF = m := hnF.trans hfields_eq
    subst hnP'
    subst hnF'
    refine ⟨cv, hf, matchesPin_of_fields ?_ ?_ ?_⟩
    · exact hname.trans ((keyOf_of_addressOf htwf ha).trans hpinName.symm)
    · exact hlps.trans ((congrArg List.range hlvls_eq).trans hpinLps.symm)
    · exact (annotates_erasePw_eq hann hann').trans hpinE
  | _ => exact False.elim hst.2

/-- **The stored recursor of `Iff` (group 16) or `Nonempty` (group 17)** has the required major
index and rule prefix and matches its `stdAxiomOk` pin, given the family inductive's level count. -/
theorem stdRec_stored {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun}
    {Rs : Nat → Ixon.Env} (hrun : BindingRun calls t ρ Rs) (hall : IxVM.Consistency.AllBound t)
    (ht : t.check = .ok ()) {g : Nat} {R R₁ R' : Ixon.Env} {env₁ : Ix.Kernel.Env .anon}
    (hadm : Admits ρ t g R R') (hle : StoreLe R₁ R') (hk : GroupKept t g R₁ env₁)
    {r : Role} {m : Nat} (which : StdMemberLevels r 1) (pin : StdRecPin r m)
    (hrg : r ∈ IxVM.Consistency.roleGroup g)
    (hfamLvls : ∀ B i ind,
      IxVM.Consistency.IndKeyAt t (IxVM.Consistency.recordOf ρ.E₀)
        (.role (stdRecFamilyPin r).1) B i ind →
      ind.lvls.toNat = if r = .iffRec then 0 else 1) :
    ∃ cv rules, env₁.find? (.role r) = some (.recInfo cv m m rules) ∧
      cv.matchesPin (stdMemberPin r) = true := by
  have htwf : t.wf = true := wf_of_check ht
  obtain ⟨-, -, -, hltF⟩ := stdMember_decided which
  obtain ⟨-, hpinLps, hpinName⟩ := stdMemberPin_spec which
  obtain ⟨a, c, ci, ci₀, _, loaded, _, _, _, _, _, _, _, _, vci, tyPtr, _, _, _,
    ha, hf, -, hrr, hst, hloaded, hsubL, hraw, hvci_eq,
    htblLoaded, extLoadedMember, mpath, hsubCs, htypePin⟩ :=
    stdMember_loaded hrun hall hadm hle hk which hrg
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hv_rec, -, -⟩ := validateMember_recCounts pin mpath
  have hrecInfo : ∃ (src : Ixon.Constant)
      (self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)))
      (recurAddrs : List _root_.Address) (blobs : List (_root_.Address × ByteArray))
      (blk : _root_.Address) (idx : Nat) (rc : Ixon.Recursor),
      (∀ x bs, (x, bs) ∈ blobs → ρ.E₀.blobs.get? x = some bs) ∧
      L1.RawRecrValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
        loaded rc blk idx vci ∧
      IxVM.Consistency.RecReads t (IxVM.Consistency.recordOf ρ.E₀)
        (fun x => ρ.E₀.blobs.get? x) src self (keyOf t a) rc ci₀ := by
    rcases (rawCIRep_info_of_tag (hv_rec ▸ hraw)).2.2 rfl with ⟨rc, hinfo⟩ | ⟨p, hinfo⟩
    · unfold L1.RawCIRep at hraw
      rw [hinfo] at hraw hrr
      dsimp only [IxVM.Consistency.ReadsRecord] at hrr
      obtain ⟨blobs, hbl, rawRec⟩ := hraw
      obtain ⟨-, hrecReads⟩ := hrr
      exact ⟨c, IxVM.Consistency.soloSelf t a, [a], blobs, a, 0, rc,
        hrun.runStore.blob_of_table hloaded hsubL hbl, rawRec, hrecReads⟩
    · unfold L1.RawCIRep at hraw
      rw [hinfo] at hraw hrr
      dsimp only [IxVM.Consistency.ReadsRecord] at hrr
      obtain ⟨-, lcB, cb, ms, rc, blobs, hgetB, -, -, hexB, -, hcb', hms', hbl, rawRec⟩ := hraw
      obtain ⟨cb', ms', rc', ⟨hB, hmuts, hm, -, -, -⟩, hrecReads⟩ := hrr
      obtain rfl := block_eq hrun.runStore hloaded hsubL hgetB hexB hB
      obtain rfl : ms = ms' := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hmuts)
      have hm' : ms[p.idx.toNat]? = some (.recr rc) := by
        rw [← Array.getElem?_toList]
        exact hms'
      obtain rfl : rc = rc' := Ixon.MutConst.recr.inj (Option.some.inj (hm'.symm.trans hm))
      exact ⟨cb, IxVM.Consistency.blockSelf t p.block ms, L1.blockRecurAddrs p.block ms.toList,
        blobs, p.block, p.idx.toNat, rc,
        hrun.runStore.blob_of_table hloaded hsubL hbl, rawRec, hrecReads⟩
  obtain ⟨src, self, recurAddrs, blobs, blk, idx, rc, hblob, rawRec, hrecReads⟩ := hrecInfo
  obtain ⟨cv, rules, hci_eq, hcv_name, tyP, kF, B, i, ind, ty,
    hreadP, hfam, horigin, hcv_lps, hreadTy, hannCv⟩ :=
    validateMember_storedRecCounts pin mpath rawRec hrecReads hst
  obtain ⟨hlvls, -, -, -, -, -, tyPtr', _, _, _, -, -, hv_raw, rawTy, -⟩ := rawRec
  have hv_eq := hv_raw.symm.trans hvci_eq
  have hfs := (Value.construct.inj hv_eq).2.2
  simp only [List.cons.injEq] at hfs
  have hrecLvls : rc.lvls.toNat = 1 :=
    nat_of_fieldCast_eq (by omega) hltF (Value.field.inj hfs.1)
  have hty_eq : tyPtr' = tyPtr := hfs.2.1
  subst hty_eq
  obtain ⟨ty', hannP, hpinE⟩ := rawType_pin_erasePw which hrun.bounded ht hsubCs (hrecLvls ▸ hlvls)
    rawTy hblob (fun _ _ _ _ hx => by simp at hx) hreadP htblLoaded extLoadedMember htypePin
  have hpinSame : (stdMemberPin r).type = (stdRecFamilyPin r).2.type := by
    cases pin <;> rfl
  have hkF : kF = .role (stdRecFamilyPin r).1 :=
    familyKey_of_stdRecPin pin hfam hannP (hpinE.trans (congrArg Ix.Kernel.Expr.erasePw hpinSame))
  have hindLvls : ind.lvls.toNat = if r = .iffRec then 0 else 1 :=
    hfamLvls B i ind (hkF ▸ horigin)
  have hlps0 : cv.levelParams = [0] :=
    hcv_lps.trans (recLps_of_stdRecPin pin hrecLvls hindLvls)
  have hrecParam : Ix.Kernel.Reader.recParam cv.levelParams = id := by
    rw [hlps0]
    exact Assembly.recParam_range 1
  rw [hrecParam] at hreadTy
  have htyP_eq : ty = tyP := Except.ok.inj (hreadTy.symm.trans hreadP)
  subst htyP_eq
  rw [hci_eq] at hf
  refine ⟨cv, rules, hf, matchesPin_of_fields ?_ ?_ ?_⟩
  · exact hcv_name.trans ((keyOf_of_addressOf htwf ha).trans hpinName.symm)
  · exact hlps0.trans hpinLps.symm
  · exact (annotates_erasePw_eq hannCv hannP).trans hpinE

/-! ## `IffPinned`, `NonemptyPinned`, and `groupWithoutRoleUnit` -/

/-- **`IffPinned` at group 16**: after the closure of group 16, `Eq` is the pinned basis constant
and `Iff`, `Iff.intro`, `Iff.rec` are stored matching their `stdAxiomOk` pins and counts. -/
theorem iffPinned_of_group16 {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun} {Rs : Nat → Ixon.Env}
    (hrun : BindingRun calls t ρ Rs) (hall : IxVM.Consistency.AllBound t)
    (ht : t.check = .ok ()) {R R₁ R' : Ixon.Env} {env₁ : Ix.Kernel.Env .anon}
    (hadm : Admits ρ t 16 R R') (hle : StoreLe R₁ R')
    (hb : BndOver.{u} L t (· < 16) R₁ env₁) (hk : GroupKept t 16 R₁ env₁) :
    IffPinned env₁ := by
  have hmem : (Ix.Kernel.eqA : Ix.Kernel.ConstantInfo .anon) ∈ env₁.consts :=
    hb.shape.pins .eqK _ (List.Mem.head _)
  have heq : env₁.find? Ix.Kernel.eqName = some Ix.Kernel.eqA :=
    find?_of_mem_nodup env₁.consts _ hmem hb.shape.reading.nodup
  obtain ⟨⟨cvI, capsI, hfI, hmI⟩, hI_lvls⟩ :=
    stdInduct_stored hrun hall ht hadm hle hk .iff (Or.inl rfl) stdMember_groups.1
  obtain ⟨cvIi, hfIi, hmIi⟩ :=
    stdCtor_stored hrun hall ht hadm hle hk .iffIntro .iff stdMember_groups.2.1
  obtain ⟨cvIr, rulesIr, hfIr, hmIr⟩ :=
    stdRec_stored hrun hall ht hadm hle hk .iffRec .iff stdMember_groups.2.2.1
      (fun B i ind h => hI_lvls B i ind h)
  change env₁.find? Ix.Kernel.iffName = some (.indInfo cvI capsI) at hfI
  change env₁.find? Ix.Kernel.iffIntroName = some (.ctorInfo cvIi 2 2) at hfIi
  change env₁.find? Ix.Kernel.iffRecName = some (.recInfo cvIr 4 4 rulesIr) at hfIr
  change cvI.matchesPin Ix.Kernel.iffA.toConstantVal = true at hmI
  change cvIi.matchesPin Ix.Kernel.iffIntroA.toConstantVal = true at hmIi
  change cvIr.matchesPin Ix.Kernel.iffRecA.toConstantVal = true at hmIr
  intro cvA hname hmatch
  unfold Ix.Kernel.stdAxiomOk
  simp only [hname, ↓reduceIte, heq, decide_true, Bool.true_and, hfI, hfIi, hfIr,
    hmI, hmIi, hmIr, hmatch]

/-- **`NonemptyPinned` at group 17**: after the closure of group 17, `Nonempty`, `Nonempty.intro`,
and `Nonempty.rec` are stored matching their `stdAxiomOk` pins and counts. -/
theorem nonemptyPinned_of_group17 {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun}
    {Rs : Nat → Ixon.Env} (hrun : BindingRun calls t ρ Rs) (hall : IxVM.Consistency.AllBound t)
    (ht : t.check = .ok ()) {R R₁ R' : Ixon.Env} {env₁ : Ix.Kernel.Env .anon}
    (hadm : Admits ρ t 17 R R') (hle : StoreLe R₁ R') (hk : GroupKept t 17 R₁ env₁) :
    NonemptyPinned env₁ := by
  obtain ⟨⟨cvN, capsN, hfN, hmN⟩, hN_lvls⟩ :=
    stdInduct_stored hrun hall ht hadm hle hk .nonempty (Or.inr rfl) stdMember_groups.2.2.2.1
  obtain ⟨cvNi, hfNi, hmNi⟩ :=
    stdCtor_stored hrun hall ht hadm hle hk .nonemptyIntro .nonempty stdMember_groups.2.2.2.2.1
  obtain ⟨cvNr, rulesNr, hfNr, hmNr⟩ :=
    stdRec_stored hrun hall ht hadm hle hk .nonemptyRec .nonempty stdMember_groups.2.2.2.2.2
      (fun B i ind h => hN_lvls B i ind h)
  change env₁.find? Ix.Kernel.nonemptyName = some (.indInfo cvN capsN) at hfN
  change env₁.find? Ix.Kernel.nonemptyIntroName = some (.ctorInfo cvNi 1 1) at hfNi
  change env₁.find? Ix.Kernel.nonemptyRecName = some (.recInfo cvNr 3 3 rulesNr) at hfNr
  change cvN.matchesPin Ix.Kernel.nonemptyA.toConstantVal = true at hmN
  change cvNi.matchesPin Ix.Kernel.nonemptyIntroA.toConstantVal = true at hmNi
  change cvNr.matchesPin Ix.Kernel.nonemptyRecA.toConstantVal = true at hmNr
  intro cvA hname hmatch
  unfold Ix.Kernel.stdAxiomOk
  have hne : Ix.Kernel.choiceName (md := .anon) ≠ Ix.Kernel.propextName := by decide
  simp only [hname, hne, ↓reduceIte, hfN, hfNi, hfNr, hmN, hmNi, hmNr, hmatch, Bool.and_self]

/-- **`RoleFreeShapes` at groups 16 and 17**, at every binding run of a table binding every role. -/
theorem roleFreeShapes_iffNonempty {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun} {Rs : Nat → Ixon.Env}
    (hrun : BindingRun calls t ρ Rs) (hall : IxVM.Consistency.AllBound t)
    (ht : t.check = .ok ()) {g : Nat} (hg : g = 16 ∨ g = 17) :
    RoleFreeShapes.{u} L ρ t g :=
  roleFreeShapes_iffNonempty_of_pinned hg fun _ _ _ _ hadm _ hle hb hk =>
    ⟨fun h16 => by subst h16; exact iffPinned_of_group16 hrun hall ht hadm hle hb hk,
     fun h17 => by subst h17; exact nonemptyPinned_of_group17 hrun hall ht hadm hle hk⟩

/-- **The stored shapes at every group without a role unit, at every binding run**: joins the
anchor groups (`roleFreeShapes_anchorGroup`), groups 16 and 17 (`roleFreeShapes_iffNonempty`), and
the groups with no shape role (`groupWithoutRoleUnit_of_shapeGroups`). -/
theorem groupWithoutRoleUnit_bindingRun :
    ∀ calls : List (Call F),
      AtGroups (BindingRun calls) (RoleFreeShapes.{u} Typing.FormerOpenTraceAt) :=
  groupWithoutRoleUnit_of_iffNonempty.{u}
    (fun _ _ _ _ hrun hall ht _ _ _ hg => roleFreeShapes_iffNonempty.{u} hrun hall ht hg)
    (fun _ _ _ _ hrun hall ht _ _ _ hg => roleFreeShapes_eqnsGroup.{u} hrun hall ht hg)

end IxVM.Refinement.Binding
