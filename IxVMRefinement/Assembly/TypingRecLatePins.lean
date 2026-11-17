import IxVMRefinement.Assembly.TypingRecParentTie
import IxVMRefinement.Claim.Constant

/-! # The recursor record's counts against its parent's

The late relation pins the record against the family: the major index and rule prefix are the
family's (`nP + 1 + #ctors + nIdx`, `nP + 1 + #ctors`), one rule per constructor. This module
reads the counts off the circuit's check of the record:

* `AnnShape`, `annotates_annShape`, `majorKey_annotates_eq`: two annotations of one term agree
  up to binder data and free-variable annotations, so they have one major key; the parent the
  route reads at the step is the tie's (`RecMajorTie`);
* `get_ci_bytes_bound`, `recr_rules_size_lt`: the record the walk loaded has fewer than `2^33`
  rules (its bytes are fewer than `2^32`, and a rule takes at least one unit of the decoder's
  resource bound), so the rule count is read exactly from its field image;
* `rec_counts_of_arm`: the record's parameter, index and motive counts and its rule count, against
  the parent's member inductive: `n_p = parent_np`, `n_i = parent_ni` (the member check),
  `n_mot = 1` (the arm), and the length of the rule list the parent's constructor count (the
  member check's `Lists::length` run).
-/

universe u

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)

/-! ## Two annotations of one term -/

/-- Two terms of one shape, up to binder data and free-variable annotations. -/
inductive AnnShape : Ix.Kernel.Expr .anon → Ix.Kernel.Expr .anon → Prop
  | bvar (i : Nat) : AnnShape (.bvar i) (.bvar i)
  | fvar (i : Nat) (x y : Ix.Kernel.Expr .anon) : AnnShape (.fvar i x) (.fvar i y)
  | sort (l : Ix.Kernel.Level) : AnnShape (.sort l) (.sort l)
  | const (k : Ix.Kernel.Key .anon) (us : List Ix.Kernel.Level) :
      AnnShape (.const k us) (.const k us)
  | lit (l : Ix.Kernel.Literal) : AnnShape (.lit l) (.lit l)
  | app {f g a b : Ix.Kernel.Expr .anon} :
      AnnShape f g → AnnShape a b → AnnShape (.app f a) (.app g b)
  | lam {t t' b b' : Ix.Kernel.Expr .anon} {m m' : Ix.Kernel.BinderMeta} :
      AnnShape t t' → AnnShape b b' → AnnShape (.lam t b m) (.lam t' b' m')
  | forallE {t t' b b' : Ix.Kernel.Expr .anon} {m m' : Ix.Kernel.BinderMeta} :
      AnnShape t t' → AnnShape b b' → AnnShape (.forallE t b m) (.forallE t' b' m')
  | proj {s : Ix.Kernel.Key .anon} {i : Nat} {e e' : Ix.Kernel.Expr .anon} :
      AnnShape e e' → AnnShape (.proj s i e) (.proj s i e')

/-- **Two annotations of one term have one shape**: `Annotates` fixes all but binder data and
free-variable annotations, and reduces a `let` the same way in both. -/
theorem annotates_annShape {E' T : Ix.Kernel.Expr .anon} (h : Annotates E' T) :
    ∀ {E'' : Ix.Kernel.Expr .anon}, Annotates E'' T → AnnShape E' E'' := by
  induction h with
  | bvar => intro E'' h2; cases h2; exact .bvar _
  | fvar _ _ => intro E'' h2; cases h2; exact .fvar _ _ _
  | sort => intro E'' h2; cases h2; exact .sort _
  | const => intro E'' h2; cases h2; exact .const _ _
  | lit => intro E'' h2; cases h2; exact .lit _
  | app _ _ ihf iha =>
    intro E'' h2
    cases h2 with
    | app hf ha => exact .app (ihf hf) (iha ha)
  | lam _ _ iht ihb =>
    intro E'' h2
    cases h2 with
    | lam ht hb => exact .lam (iht ht) (ihb hb)
  | forallE _ _ iht ihb =>
    intro E'' h2
    cases h2 with
    | forallE ht hb => exact .forallE (iht ht) (ihb hb)
  | proj _ ih =>
    intro E'' h2
    cases h2 with
    | proj he => exact .proj (ih he)
  | letE _ ih =>
    intro E'' h2
    cases h2 with
    | letE he => exact ih he

/-- The heads of two terms of one shape have one shape. -/
theorem AnnShape.getAppFn {a b : Ix.Kernel.Expr .anon} (h : AnnShape a b) :
    AnnShape a.getAppFn b.getAppFn := by
  induction h with
  | bvar i => exact .bvar i
  | fvar i x y => exact .fvar i x y
  | sort l => exact .sort l
  | const k us => exact .const k us
  | lit l => exact .lit l
  | app _ _ ihf _ => exact ihf
  | lam ht hb _ _ => exact .lam ht hb
  | forallE ht hb _ _ => exact .forallE ht hb
  | proj he _ => exact .proj he

/-- Two terms of one shape have one head key. -/
theorem headKey_eq_of_annShape {a b : Ix.Kernel.Expr .anon} (h : AnnShape a b) :
    headKey a = headKey b := by
  unfold headKey
  have hg := h.getAppFn
  generalize a.getAppFn = x at hg ⊢
  generalize b.getAppFn = y at hg ⊢
  cases hg <;> rfl

/-- Two terms of one shape strip the same number of `∀`s, to bodies of one shape. -/
theorem annShape_stripPis : ∀ (n : Nat) {a b : Ix.Kernel.Expr .anon}, AnnShape a b →
    (a.stripPis n = none ∧ b.stripPis n = none) ∨
      ∃ bs body bs' body', a.stripPis n = some (bs, body) ∧ b.stripPis n = some (bs', body') ∧
        AnnShape body body' := by
  intro n
  induction n with
  | zero =>
    intro a b h
    exact Or.inr ⟨[], a, [], b, rfl, rfl, h⟩
  | succ k ih =>
    intro a b h
    cases h with
    | @forallE t t' b₁ b₁' m m' ht hb =>
      rcases ih hb with ⟨h1, h2⟩ | ⟨bs, body, bs', body', h1, h2, h3⟩
      · left
        simp [Ix.Kernel.Expr.stripPis, h1, h2]
      · right
        exact ⟨(t, m) :: bs, body, (t', m') :: bs', body',
          by simp [Ix.Kernel.Expr.stripPis, h1], by simp [Ix.Kernel.Expr.stripPis, h2], h3⟩
    | bvar => exact Or.inl ⟨rfl, rfl⟩
    | fvar => exact Or.inl ⟨rfl, rfl⟩
    | sort => exact Or.inl ⟨rfl, rfl⟩
    | const => exact Or.inl ⟨rfl, rfl⟩
    | lit => exact Or.inl ⟨rfl, rfl⟩
    | app => exact Or.inl ⟨rfl, rfl⟩
    | lam => exact Or.inl ⟨rfl, rfl⟩
    | proj => exact Or.inl ⟨rfl, rfl⟩

/-- Two terms of one shape have one major key. -/
theorem majorKey_eq_of_annShape {rc : Ixon.Recursor} {a b : Ix.Kernel.Expr .anon}
    (h : AnnShape a b) : majorKey rc a = majorKey rc b := by
  unfold majorKey binderDom
  rcases annShape_stripPis (rc.params.toNat + rc.motives.toNat + rc.minors.toNat +
      rc.indices.toNat) h with ⟨h1, h2⟩ | ⟨bs, body, bs', body', h1, h2, h3⟩
  · rw [h1, h2]
  · rw [h1, h2]
    cases h3 with
    | forallE hd _ => exact headKey_eq_of_annShape hd
    | bvar => rfl
    | fvar => rfl
    | sort => rfl
    | const => rfl
    | lit => rfl
    | app => rfl
    | lam => rfl
    | proj => rfl

/-- **Two annotations of one term have one major key.** -/
theorem majorKey_annotates_eq {rc : Ixon.Recursor} {E' E'' T : Ix.Kernel.Expr .anon}
    (h1 : Annotates E' T) (h2 : Annotates E'' T) : majorKey rc E' = majorKey rc E'' :=
  majorKey_eq_of_annShape (annotates_annShape h1 h2)

/-! ## The rule count of a loaded record is small -/

/-- **The record `get_ci` loaded**: bytes fewer than `2^32`, hashed in the run, at the address,
decoding exactly to a record (every arm of `get_ci` starts with `load_verified_constant`). -/
theorem get_ci_bytes_bound {A : _root_.Address} {x_addr r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} (ha : Core.S0.addr h x_addr A)
    (ev : ObsFn Obs.W "Ingress::get_ci" [x_addr] h r h' calls) :
    ∃ (rawBytes : ByteArray) (c : Ixon.Constant), rawBytes.size < 4294967296 ∧
      Hashed calls rawBytes ∧ Address.blake3Pure rawBytes = A ∧
      Ixon.deConstantExact rawBytes = .ok c := by
  have key : ∀ {v : SourceValue F} {m : Heap F} {cs : List (Call F)},
      ObsFn Obs.W "Ingress::load_verified_constant" [x_addr] h v m cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∃ (rawBytes : ByteArray) (c : Ixon.Constant), rawBytes.size < 4294967296 ∧
        Hashed calls rawBytes ∧ Address.blake3Pure rawBytes = A ∧
        Ixon.deConstantExact rawBytes = .ok c := by
    intro v m cs e hsub
    obtain ⟨-, rawBytes, c, hsz, hh, hb, -, hex, -, -⟩ := Claim.load_verified_constant_de ha e
    exact ⟨rawBytes, c, hsz, Core.hashed_mono hsub hh, hb, hex⟩
  match Obs.«Ingress::get_ci».obs ev with
  | .Defn_n0 (ev14 := e) (hc302 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])
  | .Defn_other (ev14 := e) (hc423 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])
  | .Axio (ev14 := e) (hc515 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])
  | .Quot (ev14 := e) (hc606 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])
  | .DPrj (ev14 := e) (hc675 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])
  | .IPrj (ev14 := e) (hc750 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])
  | .CPrj (ev14 := e) (hc851 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])
  | .RPrj (ev14 := e) (hc926 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])
  | .Recr (ev14 := e) (hc1071 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])

/-- A list of rules is no longer than its resource size. -/
theorem rules_length_le_resourceSum :
    ∀ rs : List Ixon.RecursorRule, rs.length ≤ (rs.map Ixon.RecursorRule.resourceSize).sum
  | [] => by simp
  | r :: rs => by
    have hr : 1 ≤ r.resourceSize := by dsimp [Ixon.RecursorRule.resourceSize]; omega
    have hrs := rules_length_le_resourceSum rs
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- **A decoded recursor record of fewer than `2^32` bytes has fewer than `2^33` rules.** -/
theorem recr_rules_size_lt {rawBytes : ByteArray} {c : Ixon.Constant} {rc : Ixon.Recursor}
    (hsz : rawBytes.size < 4294967296) (hde : Ixon.deConstantExact rawBytes = .ok c)
    (hinfo : c.info = .recr rc) : rc.rules.size < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound rawBytes c hde
  have hlen := rules_length_le_resourceSum rc.rules.toList
  rw [Array.length_toList] at hlen
  have hrc : rc.rules.size ≤ c.resourceSize := by
    have h1 : (rc.rules.toList.map Ixon.RecursorRule.resourceSize).sum ≤ rc.resourceSize := by
      dsimp [Ixon.Recursor.resourceSize]
      omega
    have h2 : rc.resourceSize ≤ c.info.resourceSize := by
      rw [hinfo]
      dsimp [Ixon.ConstantInfo.resourceSize]
      omega
    have h3 : c.info.resourceSize ≤ c.resourceSize := by
      dsimp [Ixon.Constant.resourceSize]
      omega
    omega
  omega

/-! ## Field images of small counts -/

/-- Field images of two counts below the modulus are equal only if the counts are. -/
theorem field_nat_inj {a b : Nat} (ha : a < 18446744069414584321)
    (hb : b < 18446744069414584321)
    (h : ((.field (a : F)) : SourceValue F) = .field (b : F)) : a = b := by
  have h' := congrArg ZMod.val (Value.field.inj h)
  rwa [ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega),
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)] at h'

/-- A converted rule list is a list of its cells. -/
theorem RulesTraceRep.toRepListTrue {refs recurAddrs : List _root_.Address}
    {univs : List Ixon.Univ} {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {tree : L1.BinderTreeData} {h : Heap F} {j : Nat} {root : F}
    {rus : List Ixon.RecursorRule} {p : SourceValue F}
    (r : L1.RulesTraceRep refs recurAddrs univs sharing blobs tree h j root rus p) :
    RepList Core.krrListEnum (fun _ _ _ => True) h rus p := by
  induction r with
  | nil cell => exact .nil cell
  | cons cell _ _ _ _ _ ih => exact .cons cell trivial ih

/-- `Lists::length` of a converted rule list is its length. -/
theorem rulesTrace_length_spec {refs recurAddrs : List _root_.Address}
    {univs : List Ixon.Univ} {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {tree : L1.BinderTreeData} {j : Nat} {root : F} {rus : List Ixon.RecursorRule}
    {p r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::length<KernelTypes::KRecRule>» [p] h r h' cs)
    (hr : L1.RulesTraceRep refs recurAddrs univs sharing blobs tree h j root rus p) :
    r = .field (rus.length : F) := by
  have ev' : ObsFn Obs.W
      (Instance.mk "Lists::length" [(.named "KernelTypes::KRecRule" [])]).symbol
      [p] h r h' cs := by
    rw [Obs.Names.«Lists::length<KernelTypes::KRecRule>».symbol]
    exact ev
  have hl' : RepList
      (Instance.mk "Lists::Node" [(.named "KernelTypes::KRecRule" [])]).symbol
      (fun _ _ _ => True) h rus p := by
    rw [Obs.Names.«Lists::Node<KernelTypes::KRecRule>».symbol]
    exact RulesTraceRep.toRepListTrue hr
  exact (Lib.Lists.length_spec ev' hl').1

/-- **The minor premises are the constructors**: `check_recursor_canonical_full` at an inductive
parent runs `nat_rec_check`, which asserts `n_min = num_ctors` (its other arm refuses a parent
that is not an inductive). -/
theorem canonical_full_minors
    {rc levels type parameters indices motives minors rules k unsafeFlag block position address
      parentLevels parentType parentParams parentIndices constructors parentUnsafe parentBlock
      parentIndex parent result : SourceValue F}
    {heap final : Heap F} {calls : List (Call F)}
    (observed : ObsFn Obs.W "KernelCheck::check_recursor_canonical_full"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
          position], address,
        .construct "KernelTypes::KConstantInfo" "Induct"
          [parentLevels, parentType, parentParams, parentIndices, constructors, parentUnsafe,
            parentBlock, parentIndex], parent]
      heap result final calls) :
    minors = constructors := by
  match Obs.«KernelCheck::check_recursor_canonical_full».obs observed with
  | .other (hne568 := hne) .. =>
    exact absurd rfl (hne [_, _, _, _, _, _, _, _] rfl)
  | .Induct (ev518 := natRun) .. =>
    match Obs.«KernelCheck::nat_rec_check».obs natRun with
    | .run (hv11 := recShape) (hv81 := parentShape) (heq217 := minorsEq) .. =>
      injection recShape with _ _ recFields
      simp only [List.cons.injEq, and_true] at recFields
      injection parentShape with _ _ parentFields
      simp only [List.cons.injEq, and_true] at parentFields
      exact recFields.2.2.2.2.2.1.trans (minorsEq.trans parentFields.2.2.2.2.1.symm)

/-! ## The counts -/

/-- **The record's counts against its parent's member inductive.** At an environment the
skeleton hands the step, for the parent `P` tied to the record (`RecMajorTie`) whose record in
`E` is the projection `ip` of member `ind` of the block `cb`: the record declares the member's
parameter and index counts, one motive, and one rule per constructor. -/
theorem rec_counts_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) (hlim : lim = some n)
    (hnat : NativeRecArm calls bAddr t A n) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind)) :
    rc.params.toNat = ind.params.toNat ∧ rc.indices.toNat = ind.indices.toNat ∧
      rc.motives.toNat = 1 ∧ rc.rules.size = ind.ctors.size ∧
      rc.minors.toNat = ind.ctors.size := by
  subst hlim
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have hgood : Core.Good ⟨E, env, t, some n⟩ calls := hst.good env (some n)
  have hbound : Bounded calls := hgood.2
  have hrec₀ : Ix.Cert.recordAt E₀ A = some c := (hS.recordOf_eq_recordAt A).symm.trans hc
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hstep.ext, hstep.refs, hstep.fresh⟩) hinert
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, -, -, ha_pre, -, ev_ld, hsub_ld,
    hld, ev_chk, hsub_chk⟩ := hnat
  -- the record has few rules
  obtain ⟨rawB, cB, hszB, hhB, hbaB, hexB⟩ := get_ci_bytes_bound ha_pre ev_ld
  have hcB : cB = c := hS.record_eq hrec₀ (Core.hashed_mono hsub_ld hhB) hbaB hexB
  subst cB
  have hrules_lt := recr_rules_size_lt hszB hexB hinfo
  -- one motive
  have hmot := (check_const_rec_arm ev_chk).1
  obtain ⟨a', ha'_ref, haA⟩ := ha_pre
  subst haA
  -- the load of the record, traced
  obtain ⟨rawBytes, c', hh, hba, hex, -, hres'⟩ :=
    L1.get_ci_block_trace_spec (hgood.sub hsub_ld).2 ha'_ref ev_ld
  have hcc : c' = c := hS.record_eq hrec₀ (Core.hashed_mono hsub_ld hh) hba hex
  subst c'
  unfold L1.GetCIBlockTraceResult at hres'
  rw [hinfo] at hres'
  obtain ⟨blobs, tree, v, hhp, built, hldv, htr⟩ := hres'
  rw [hld] at hldv
  obtain ⟨hlvls, hp56, hi56, hm56, hmi56, -, tyPtr, rulesPtr, blkPtr, b, planT, -, -, hv, rty,
    -, -, hrulesTr⟩ := htr
  subst hv
  injection hldv with hv'
  injection hv' with _ _ hfields
  simp only [List.cons.injEq, and_true] at hfields
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -, -, -⟩ := hfields
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hhx' : Hashed cs_load bs := hhx
    have hxa' : Address.blake3Pure bs = x := hxa
    have hrun := hS.blobs bs (Core.hashed_mono hsub_ld hhx')
    rw [hxa'] at hrun
    exact hrun
  -- the type reads, well scoped, represented under the prefix keying
  obtain ⟨tyP, htyP⟩ := LoadedReads.exprReader_read_ok (t := t)
    (blob := fun x => E₀.blobs.get? x) ht (param := id) (self := soloSelf t (Core.ixAddr a'))
    rty (fun i x hx => by simp at hx) hblob
  obtain ⟨sB, sA, mH, sR, sCs, mCs, hextS, evS, hmemS, hextM, evM, hsubM⟩ :=
    check_const_rec_route ev_chk
  obtain ⟨-, hlbb, hdef⟩ := Assembly.validate_expr_well_scoped_spec
    (cx := readCtx t (fun x => E₀.blobs.get? x)) (self := soloSelf t (Core.ixAddr a'))
    hbound hlvls rty hextS htyP evS (hsub_chk _ hmemS)
  have hrd : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t (fun x => E₀.blobs.get? x)) c
      (Ix.Kernel.Reader.recParam (List.range rc.lvls.toNat))
      (soloSelf t (Core.ixAddr a'))).read rc.typ = .ok tyP := by
    rw [Assembly.recParam_range]
    exact htyP
  obtain ⟨E', hann, htm⟩ := rty.toTmC (κ := Core.keyOf t) (ps := List.range rc.lvls.toNat)
    (by simp) (by simpa using hlvls) (LoadedReads.readCtx_keyAt_inv ht _)
    (fun i x m k hx => by simp at hx) hblob hrd hlbb hdef
  have htmS := Decl.tmC_stored_of_usedRefs (E₀ := E) (env := env) (lim := some n) rty
    (recr_typ_usedRefs hinfo) hstored htm
  rw [Decl.posOf_range] at htmS
  have hsum : ZMod.val ((rc.params.toNat : F) + (rc.motives.toNat : F) + (rc.minors.toNat : F) +
      (rc.indices.toNat : F)) =
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat := by
    rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
    exact ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  -- the member check: route, counts, rule list length
  obtain ⟨parent, pointer, scanHeap, loadedHeap, routedHeap, scanCalls, loadCalls, routeCalls,
    nl, pty, np, ni, nc, pu, blk, idx, lenHeap, lenAfter, kHeap, kAfter, canonHeap, len, kTarget,
    lenCalls, kCalls, canonCalls, evScan, hsScan, evLoad, hsLoad, hldP, evRoute, hsRoute,
    hnp, hni, eLen, evLen, hsLen, hlenEq, -, -, -, -, -, evCanon, -⟩ := native_rec_member_full evM
  have hsScan' : ∀ x ∈ scanCalls, x ∈ calls := fun x hx => hsub_chk x (hsubM x (hsScan x hx))
  have hsLoad' : ∀ x ∈ loadCalls, x ∈ calls := fun x hx => hsub_chk x (hsubM x (hsLoad x hx))
  -- the route's parent is the tied one
  let cS : Core.ScopedCtx := Core.Ctx.stored ⟨E, env, t, some n⟩
  have hcS : Core.ScopedCoreFacts cS := hstep.inv.scopedCoreFacts
  have htmM := htmS.mono hextM
  obtain ⟨a, dom, us, ha, hpi, hhead⟩ := Decl.scopedCalleesSpec cS hcS .rec_to_parent_addr _ _ _
    _ _ evScan _ _ _ _ _ rfl (Core.CoreGood.ofRaw (hgood.sub hsScan') (fun _ _ => trivial)) E' htmM
  have hkr : Core.KeysResolved E' := (htmM 0 (fun _ => .sort .zero)).keysResolved
  have hne : cS.κ (Core.ixAddr a) ≠ Core.unresolvedKey :=
    keysResolved_getAppFn (keysResolved_piDomAt _ hkr hpi) hhead
  have hkey : cS.κ (Core.ixAddr a) = Core.keyOf t (Core.ixAddr a) := cS.key_eq hne
  have hhead' := hhead
  rw [hkey] at hhead'
  have hmajA : majorKey rc E' = some (keyOf t (Core.ixAddr a)) :=
    majorKey_of_piDomAt (by rw [← hsum]; exact hpi) hhead'
  obtain ⟨tyP', E'', htyP', hann', hmajP⟩ := htie
  have htyEq : tyP' = tyP := Except.ok.inj (htyP'.symm.trans htyP)
  subst htyEq
  have hkeys : keyOf t P = keyOf t (Core.ixAddr a) :=
    Option.some.inj (hmajP.symm.trans ((majorKey_annotates_eq (rc := rc) hann' hann).trans hmajA))
  have hPa : P = Core.ixAddr a := keyOf_inj hroles hkeys
  subst hPa
  -- the parent's load, traced: the member `ind` of the block `cb`
  have hgL : Core.Good ⟨E, env, t, some n⟩ loadCalls := hgood.sub hsLoad'
  obtain ⟨rawP, cP, hhP, hbaP, hexP, -, hresP⟩ := L1.get_ci_block_trace_spec hgL.2 ha evLoad
  have hrecP : recordOf E (Core.ixAddr a) = some cm := by
    rw [recordOf_eq_recordAt_of_decoded hst.decoded]
    exact hcm
  obtain ⟨lc, hget, hdec⟩ := LoadedReads.recordOf_inv hrecP
  have hbP : rawP = lc.rawBytes := Core.load_escape hget hgL.1 rawP hhP hbaP
  have hcP : cP = cm := by
    rw [hbP, hdec] at hexP
    exact (Except.ok.inj hexP).symm
  subst hcP
  unfold L1.GetCIBlockTraceResult at hresP
  rw [hcmi] at hresP
  obtain ⟨-, blkBytes, cb', ms', ind', blobs', tree', plan', v₀, hhB', haB', hexB', hcb', hms',
    -, -, -, hld₀, hraw, -⟩ := hresP
  have hrecB : recordOf E ip.block = some cb := by
    rw [recordOf_eq_recordAt_of_decoded hst.decoded]
    exact hcb
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hrecB
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hgL.1 blkBytes hhB' haB'
  have hcbEq : cb' = cb := by
    rw [hbB, hdecB] at hexB'
    exact (Except.ok.inj hexB').symm
  subst hcbEq
  have hmsEq : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hms)
  subst hmsEq
  have hlist : ms'.toList[ip.idx.toNat]? = ms'[ip.idx.toNat]? := by simp
  rw [hlist, hind] at hms'
  have hindEq : ind = ind' := Ixon.MutConst.indc.inj (Option.some.inj hms')
  subst hindEq
  obtain ⟨hlvlsP, hpP, hiP, hcP56, hidxP, tyPtrP, blkPtrP, bP, -, -, hvP, -⟩ := hraw
  subst hvP
  rw [hld₀] at hldP
  injection hldP with hvP'
  injection hvP' with _ _ hpf
  simp only [List.cons.injEq, and_true] at hpf
  obtain ⟨-, -, hnpEq, hniEq, hncEq, -, -, -⟩ := hpf
  -- the counts
  have hparams : rc.params.toNat = ind.params.toNat :=
    field_nat_inj (by omega) (by omega) (hnp.trans hnpEq.symm)
  have hindices : rc.indices.toNat = ind.indices.toNat :=
    field_nat_inj (by omega) (by omega) (hni.trans hniEq.symm)
  have hmotives : rc.motives.toNat = 1 := by
    have h1 : ((.field ((rc.motives.toNat : Nat) : F)) : SourceValue F) =
        .field ((1 : Nat) : F) := by
      rw [Nat.cast_one]
      exact hmot
    exact field_nat_inj (by omega) (by norm_num) h1
  have extL : Heap.Extends m_chk lenHeap :=
    hextM.trans (evScan.heap_extends.trans (evLoad.heap_extends.trans eLen))
  have hlenV := rulesTrace_length_spec evLen (hrulesTr.mono extL (fun q hq => hq))
  have hrulesN : rc.rules.toList.length = ind.ctors.size :=
    field_nat_inj (by rw [Array.length_toList]; omega) (by omega)
      (hlenV.symm.trans (hlenEq.trans hncEq.symm))
  rw [Array.length_toList] at hrulesN
  have hminors : rc.minors.toNat = ind.ctors.size :=
    field_nat_inj (by omega) (by omega) ((canonical_full_minors evCanon).trans hncEq.symm)
  exact ⟨hparams, hindices, hmotives, hrulesN, hminors⟩

end IxVM.Refinement.Typing
