import IxVMRefinement.Binding.PinnedType
import IxVMRefinement.Binding.LoadedType
import IxVMRefinement.Binding.ShapesWiden

/-! # The stored shapes at the anchor groups

Six of the eight groups that hold a shape role hold anchors whose stored type the kernel's rules
read: `Bool` and its constructors (group 6), `Char`, `String`, `List` with its constructors,
`Char.ofNat` and `String.ofList` (groups 41 to 45). `KernelRoles::validate_anchor` pins each of
them: it loads the bound record, checks its type well scoped with the record's level count, and
asserts the type structurally equal to `role_type(tbl, r)` (`KernelRoles.lean:865-888`);
`validate_role` asserts the level count (`:760`). This file turns that into the stored shapes.

* `pinnedAnchors`, `pinnedAnchor_facts`: the ten anchors, and what is decided about them.
* `seg1_pinned`, `validate_anchor_pin`: the observed `validate_anchor` of a pinned anchor, with
  its type, level count, well-scoping check, `role_type` and `assert_type_pinned` calls.
* `domForallAt` and its lemmas: a recursor's reading has a `∀` domain where its family's motive
  is (`familyKey`), which annotations and binder data keep; no anchor's pinned type has one.
* `anchor_stored_matchesPin`: **at a binding run, after the closure of the anchor's group, the
  stored constant at a pinned anchor's key matches the anchor's pin** (`anchorPin?`).
* `roleFreeShapes_anchorGroup`: `RoleFreeShapes` at the six anchor groups; `groupWithoutRoleUnit_of_iffNonempty`: the residual's hypothesis from its instances at groups 16 and 17.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Role)
open Ix.Kernel.Semantics (NativeFam)

/-! ## The pinned anchors -/

/-- **The anchors whose stored type a shape reads**: `Bool`, `Bool.false`, `Bool.true`, `List`,
`List.nil`, `List.cons`, `String`, `String.ofList`, `Char`, `Char.ofNat`. -/
def pinnedAnchors : List Role :=
  [.bool, .boolFalse, .boolTrue, .list, .listNil, .listCons, .string, .stringOfList, .char,
    .charOfNat]

/-- The role numbers `validate_anchor` pins (`KernelRoles.lean:873-886`). -/
def pinnedNums : List F := [4, 5, 6, 7, 20, 21, 22, 29, 30, 31, 37, 38, 39, 40]

/-- The number of leading `∀` binders of a term. -/
def forallDepth : KExpr → Nat
  | .forallE _ b _ => forallDepth b + 1
  | _ => 0

/-- **The binder at depth `p` has a `∀` as its domain.** -/
def domForallAt : Nat → KExpr → Bool
  | 0, .forallE d _ _ => match d with
    | .forallE .. => true
    | _ => false
  | p + 1, .forallE _ b _ => domForallAt p b
  | _, _ => false

set_option maxRecDepth 100000 in
/-- What is decided about the ten anchors: each is an anchor role validated with a pinned
type, kept, neither an operation nor a standard axiom, with an anchor pin whose type has no
`∀` domain. -/
theorem pinnedAnchor_decided : pinnedAnchors.all (fun r =>
    decide (RoleVal.roleSpecKindNat r = 1) && decide (roleNum r ∈ pinnedNums) &&
    decide (r ∈ IxVM.Consistency.shapeAnchors) && !decide (r ∈ RoleOps.opRoles) &&
    !decide (r ∈ IxVM.Consistency.standardAxioms) &&
    (match anchorPin? (.role r) with
      | some pin => (List.range (forallDepth pin.type)).all (fun p => !domForallAt p pin.type)
      | none => false)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- No basis or quotient pin is at an anchor's key. -/
theorem pinnedAnchor_notBasis : ∀ k : Ix.Kernel.BasisKind, ∀ r ∈ pinnedAnchors,
    ∀ ci ∈ (k.declsA : List (Ix.Kernel.ConstantInfo .anon)), ci.name ≠ .role r := by
  intro k
  cases k <;> decide +kernel

theorem domForallAt_lt : ∀ (p : Nat) (e : KExpr), domForallAt p e = true → p < forallDepth e
  | 0, .forallE d b m, _ => Nat.succ_pos _
  | p + 1, .forallE d b m, h => Nat.succ_lt_succ (domForallAt_lt p b h)
  | 0, .bvar _, h | 0, .fvar _ _, h | 0, .sort _, h | 0, .const _ _, h | 0, .app _ _, h
  | 0, .lam _ _ _, h | 0, .letE _ _ _ _, h | 0, .lit _, h | 0, .proj _ _ _, h => by
    simp [domForallAt] at h
  | p + 1, .bvar _, h | p + 1, .fvar _ _, h | p + 1, .sort _, h | p + 1, .const _ _, h
  | p + 1, .app _ _, h | p + 1, .lam _ _ _, h | p + 1, .letE _ _ _ _, h | p + 1, .lit _, h
  | p + 1, .proj _ _ _, h => by
    simp [domForallAt] at h

structure PinnedAnchorFacts (r : Role) : Prop where
  specKind : RoleVal.roleSpecKindNat r = 1
  num : roleNum r ∈ pinnedNums
  kept : IxVM.Consistency.keptRole r
  notUnit : ¬ (r ∈ RoleOps.opRoles ∨ r ∈ IxVM.Consistency.standardAxioms)
  notBasis : ∀ (k : Ix.Kernel.BasisKind) (ci : Ix.Kernel.ConstantInfo .anon),
    ci ∈ (k.declsA : List (Ix.Kernel.ConstantInfo .anon)) → ci.name ≠ .role r
  noDom : ∀ pin, anchorPin? (.role r) = some pin → ∀ p, domForallAt p pin.type = false
  pinSome : ∃ pin, anchorPin? (.role r) = some pin

theorem pinnedAnchor_facts {r : Role} (hr : r ∈ pinnedAnchors) : PinnedAnchorFacts r := by
  have h := List.all_eq_true.mp pinnedAnchor_decided r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    at h
  obtain ⟨⟨⟨⟨⟨hsk, hnum⟩, hsh⟩, hop⟩, hstd⟩, hpin⟩ := h
  have hsome : ∃ pin, anchorPin? (.role r) = some pin := by
    cases hap : anchorPin? (.role r) with
    | none => rw [hap] at hpin; simp at hpin
    | some pin => exact ⟨pin, rfl⟩
  refine ⟨hsk, hnum, Or.inl (Or.inr hsh), fun h => h.elim hop hstd,
    fun k ci hci => pinnedAnchor_notBasis k r hr ci hci, fun pin hp p => ?_, hsome⟩
  simp only [hp] at hpin
  cases hd : domForallAt p pin.type with
  | false => rfl
  | true =>
    have hlt := domForallAt_lt p pin.type hd
    have := List.all_eq_true.mp hpin p (List.mem_range.mpr hlt)
    rw [hd] at this
    cases this

/-! ## A recursor's family motive, against an anchor's pin -/

theorem domForallAt_of_strip : ∀ (p : Nat) (ty : KExpr)
    (bs : List (KExpr × Ix.Kernel.BinderMeta)) (d b : KExpr) (m : Ix.Kernel.BinderMeta),
    ty.stripPis p = some (bs, .forallE d b m) →
    (∃ d₁ b₁ m₁, d = .forallE d₁ b₁ m₁) → domForallAt p ty = true
  | 0, ty, bs, d, b, m, h, ⟨d₁, b₁, m₁, hd⟩ => by
    have h2 : ty = .forallE d b m := (Prod.mk.inj (Option.some.inj h)).2
    subst h2
    subst hd
    rfl
  | p + 1, .forallE ty' b' m', bs, d, b, m, h, hd => by
    cases hs : b'.stripPis p with
    | none =>
      rw [Ix.Kernel.Expr.stripPis, hs] at h
      simp at h
    | some pr =>
      rw [Ix.Kernel.Expr.stripPis, hs] at h
      obtain ⟨bs', X⟩ := pr
      have h2 : X = .forallE d b m := (Prod.mk.inj (Option.some.inj h)).2
      subst h2
      exact domForallAt_of_strip p b' bs' d b m hs hd
  | p + 1, .bvar _, _, _, _, _, h, _ | p + 1, .fvar _ _, _, _, _, _, h, _
  | p + 1, .sort _, _, _, _, _, h, _ | p + 1, .const _ _, _, _, _, _, h, _
  | p + 1, .app _ _, _, _, _, _, h, _ | p + 1, .lam _ _ _, _, _, _, _, h, _
  | p + 1, .letE _ _ _ _, _, _, _, _, h, _ | p + 1, .lit _, _, _, _, _, h, _
  | p + 1, .proj _ _ _, _, _, _, _, h, _ => by
    simp [Ix.Kernel.Expr.stripPis] at h

/-- **A recursor's reading has a `∀` domain at its family's motive.** -/
theorem domForallAt_of_familyKey {rc : Ixon.Recursor} {ty : KExpr}
    {kF : Ix.Kernel.Key .anon} (h : IxVM.Consistency.familyKey rc ty = some kF) :
    domForallAt rc.params.toNat ty = true := by
  unfold IxVM.Consistency.familyKey IxVM.Consistency.binderDom at h
  cases hs : ty.stripPis rc.params.toNat with
  | none => rw [hs] at h; cases h
  | some pr =>
    obtain ⟨bs, X⟩ := pr
    rw [hs] at h
    cases X with
    | forallE d b m =>
      apply domForallAt_of_strip _ ty bs d b m hs
      cases d with
      | forallE d₁ b₁ m₁ => exact ⟨d₁, b₁, m₁, rfl⟩
      | _ => simp [IxVM.Consistency.lastBinderDom] at h
    | _ => simp at h

/-- **An annotation keeps a `∀` domain.** -/
theorem domForallAt_annot : ∀ (p : Nat) {e' e : KExpr}, IxVM.Consistency.Annotates e' e →
    domForallAt p e = true → domForallAt p e' = true
  | 0, e', e, ha, h => by
    cases e with
    | forallE d b m =>
      cases ha with
      | forallE hd hb =>
        cases d with
        | forallE d₁ b₁ m₁ =>
          cases hd with
          | forallE _ _ => rfl
        | _ => simp [domForallAt] at h
    | _ => simp [domForallAt] at h
  | p + 1, e', e, ha, h => by
    cases e with
    | forallE d b m =>
      cases ha with
      | forallE hd hb => exact domForallAt_annot p hb h
    | _ => simp [domForallAt] at h

/-- **Binder data does not change a `∀` domain.** -/
theorem domForallAt_erasePw : ∀ (p : Nat) (e : KExpr), domForallAt p e.erasePw = domForallAt p e
  | 0, .forallE d b m => by cases d <;> rfl
  | p + 1, .forallE d b m => domForallAt_erasePw p b
  | 0, .bvar _ | 0, .fvar _ _ | 0, .sort _ | 0, .const _ _ | 0, .app _ _ | 0, .lam _ _ _
  | 0, .letE _ _ _ _ | 0, .lit _ | 0, .proj _ _ _ => rfl
  | _ + 1, .bvar _ | _ + 1, .fvar _ _ | _ + 1, .sort _ | _ + 1, .const _ _ | _ + 1, .app _ _
  | _ + 1, .lam _ _ _ | _ + 1, .letE _ _ _ _ | _ + 1, .lit _ | _ + 1, .proj _ _ _ => rfl

/-! ## A loaded constant's first two fields -/

/-- `KernelInfer::const_num_lvls` returns a constant's first field. -/
theorem const_num_lvls_fields {tag : String} {nl ty : SourceValue F}
    {rest : List (SourceValue F)} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelInfer::const_num_lvls" [.construct kciEnum tag (nl :: ty :: rest)] h r h'
      cs) : r = nl ∧ h' = h := by
  rcases Obs.«KernelInfer::const_num_lvls».obs ev with
    ⟨x_n, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩
  all_goals
    have hl := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq] at hl
    exact ⟨he.trans hl.1.symm, hh⟩

/-- `KernelInfer::const_type_of` returns a constant's second field. -/
theorem const_type_of_fields {tag : String} {nl ty : SourceValue F}
    {rest : List (SourceValue F)} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelInfer::const_type_of" [.construct kciEnum tag (nl :: ty :: rest)] h r h'
      cs) : r = ty ∧ h' = h := by
  rcases Obs.«KernelInfer::const_type_of».obs ev with
    ⟨_, x_ty, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩
  all_goals
    have hl := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq] at hl
    exact ⟨he.trans hl.2.1.symm, hh⟩

/-! ## The observed `validate_anchor` of a pinned anchor -/

/-- The `match r` of `validate_anchor` at a pinned role number takes `assert_type_pinned`. -/
theorem seg1_pinned {spec ty rc tbl ci res : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {k : F} (hk : k ∈ pinnedNums)
    (hs : Obs.«KernelRoles::validate_anchor».Seg1 spec ty rc tbl (.field k) ci h res h' cs) :
    ∃ cs', ObsFn W "KernelRoles::assert_type_pinned" [ty, spec] h res h' cs' := by
  cases hs with
  | other _ h4 h5 h6 h7 h20 h21 h22 h29 h30 h31 h37 h38 h39 h40 _ _ =>
    exfalso
    simp only [pinnedNums, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    · exact h4 rfl
    · exact h5 rfl
    · exact h6 rfl
    · exact h7 rfl
    · exact h20 rfl
    · exact h21 rfl
    · exact h22 rfl
    · exact h29 rfl
    · exact h30 rfl
    · exact h31 rfl
    · exact h37 rfl
    · exact h38 rfl
    · exact h39 rfl
    · exact h40 rfl
  | _ => exact ⟨_, ‹_›⟩

/-- **What the observed `validate_anchor` of a pinned anchor checks**: the loaded constant's
type pointer and level count, the well-scoping check of the type with that count (a call among
the validation's calls), and the type pinned against `role_type(tbl, r)`. -/
theorem validate_anchor_pin {x_rc x_tbl x_ci res : SourceValue F} {k : F} {h h' : Heap F}
    {cs : List (Call F)} (hk : k ∈ pinnedNums)
    (ev : ObsFn W "KernelRoles::validate_anchor" [x_rc, x_tbl, .field k, x_ci] h res h' cs) :
    ∃ (m₁ m₂ m₃ m₄ m₅ m₆ m₇ : Heap F) (ty nl spec u w : SourceValue F)
      (cs₁ cs₂ cs₃ cs₄ cs₅ : List (Call F)),
      Heap.Extends h m₁ ∧
      ObsFn W "KernelInfer::const_type_of" [x_ci] m₁ ty m₂ cs₁ ∧
      ObsFn W "KernelInfer::const_num_lvls" [x_ci] m₂ nl m₃ cs₂ ∧
      ObsFn W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl] m₃ u m₄ cs₃ ∧
      (⟨"KernelCheck::validate_expr_well_scoped", [ty, .field 0, nl], m₃⟩ : Call F) ∈ cs ∧
      Heap.Extends m₄ m₅ ∧
      ObsFn W "KernelRoleSpec::role_type" [x_tbl, .field k] m₅ spec m₆ cs₄ ∧
      ObsFn W "KernelRoles::assert_type_pinned" [ty, spec] m₆ w m₇ cs₅ := by
  cases Obs.«KernelRoles::validate_anchor».obs ev with
  | n1 v1 m2 cs12 v23 m24 cs34 v45 m46 cs56 v61 m76 cs84 v95 m96 cs106 m127 v139 m140 cs150 v605
      m606 cs608 m615 cs626 cs644 v648 m657 cs665 ev14 ev36 ev86 ev58 hm135 ev108 ev152 sg613
      ev628 ev667 ev646 hc684 =>
    obtain ⟨cs', evP⟩ := seg1_pinned hk sg613
    have e127 : Heap.Extends m46 m127 := by rw [hm135]; exact Heap.Extends.snoc m46 _
    exact ⟨m2, m24, m76, m46, m96, m140, m606, v23, v61, v139, v45, v605, cs34, cs84, cs56,
      cs150, cs', ev14.heap_extends, ev36, ev86, ev58, by rw [hc684]; simp,
      e127.trans ev108.heap_extends, ev152, evP⟩
  | other v1 m2 cs12 v23 m24 cs34 v45 m46 cs56 v61 m76 cs84 v95 m96 cs106 m127 v139 m140 cs150
      v605 m606 cs608 v614 m615 cs626 ev14 ev36 ev86 ev58 hm135 ev108 ev152 sg613 ev628 hne685
      he691 he692 hc693 =>
    obtain ⟨cs', evP⟩ := seg1_pinned hk sg613
    have e127 : Heap.Extends m46 m127 := by rw [hm135]; exact Heap.Extends.snoc m46 _
    exact ⟨m2, m24, m76, m46, m96, m140, m606, v23, v61, v139, v45, v605, cs34, cs84, cs56,
      cs150, cs', ev14.heap_extends, ev36, ev86, ev58, by rw [hc693]; simp,
      e127.trans ev108.heap_extends, ev152, evP⟩

/-! ## The stored constant at a pinned anchor's key -/

private theorem recordOf_up {R R' : Ixon.Env}
    (h : ∀ a lc, R.consts.get? a = some lc → R'.consts.get? a = some lc) :
    ∀ x c, IxVM.Consistency.recordOf R x = some c → IxVM.Consistency.recordOf R' x = some c := by
  intro x c hc
  unfold IxVM.Consistency.recordOf at hc ⊢
  cases hg : R.consts.get? x with
  | none => rw [hg] at hc; cases hc
  | some lc => rw [hg] at hc; rw [h x lc hg]; exact hc

/-- **At a binding run, after the closure of a pinned anchor's group, the stored constant at the
anchor's key matches the anchor's pin.** From the run's validation of the anchor in its group
(`Admits.validated`, observed by `BindingRun.observed`): the load of the bound record, whose
type is checked well scoped with the record's level count and pinned against `role_type`
(`validate_anchor`), the level count against `role_levels` (`validate_role`); and from the
closure (`GroupKept`): the stored constant is the record's reading, stored. -/
theorem anchor_stored_matchesPin {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun}
    {Rs : Nat → Ixon.Env} (hrun : BindingRun calls t ρ Rs) (hall : IxVM.Consistency.AllBound t)
    (ht : t.check = .ok ()) {g : Nat} {r : Role} (hr : r ∈ pinnedAnchors)
    (hrg : r ∈ IxVM.Consistency.roleGroup g) {R R₁ R' : Ixon.Env} {env₁ : Ix.Kernel.Env .anon}
    (hadm : Admits ρ t g R R') (hle : StoreLe R₁ R') (hk : GroupKept t g R₁ env₁)
    {pin : Ix.Kernel.ConstantVal .anon} (hpin : anchorPin? (.role r) = some pin) :
    ∃ ci, env₁.find? (.role r) = some ci ∧ ci.toConstantVal.matchesPin pin = true := by
  have htwf : t.wf = true := wf_of_check ht
  have hfacts := pinnedAnchor_facts hr
  obtain ⟨hT, hn, hlps, hname⟩ := anchorPin_spec hpin
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall r)
  have hkeya : keyOf t a = .role r := keyOf_of_addressOf htwf ha
  obtain ⟨ci, hf, hkp⟩ := hk.1 r hrg hfacts.kept hfacts.notUnit a ha
  refine ⟨ci, hf, ?_⟩
  have hname_ci : ci.name = .role r := Ix.Kernel.Semantics.Env.find?_name hf
  rcases hkp with ⟨kind, hmem⟩ | ⟨-, ci₀, hrd₁, hst⟩
  · exact absurd hname_ci (hfacts.notBasis kind ci hmem)
  -- the reading over the run's store
  have hRE : ∀ x c, IxVM.Consistency.recordOf R₁ x = some c →
      IxVM.Consistency.recordOf ρ.E₀ x = some c :=
    recordOf_up fun x lc h => hadm.loaded x lc (hle.1 x lc h)
  have hbE : ∀ x b, R₁.blobs.get? x = some b → ρ.E₀.blobs.get? x = some b :=
    fun x b h => hadm.loadedBlobs x b (hle.2 x b h)
  obtain ⟨c, hcE, hrr⟩ := IxVM.Consistency.ReadsIn.mono hRE hbE hrd₁
  -- the run's validation of the anchor
  have hval := hadm.validated r hrg
  obtain ⟨bAddr, tb, -, -, hρ⟩ := hrun.observed
  have hval' : RoleValidationIn calls bAddr t g r := by
    have e : ρ.validated = (observedRun calls bAddr t ρ.E₀ ρ.rank).validated :=
      congrArg BRun.validated hρ
    rw [e] at hval
    exact hval
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hval'
  have htblR : TableRep t h x_tbl := htbl.toTableRep
  cases Obs.«KernelRoles::validate_role».obs ev with
  | n1 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs192
      ev14 ev47 ld41 ev80 ev100 heq109 ev124 ev194 hc227 =>
    have hsubV : ∀ cl ∈ cs, cl ∈ calls := hsub
    have hsub45 : ∀ cl ∈ cs45, cl ∈ calls := fun cl hm => hsubV cl (by rw [hc227]; simp [hm])
    have hsub192 : ∀ cl ∈ cs192, cl ∈ calls := fun cl hm => hsubV cl (by rw [hc227]; simp [hm])
    obtain ⟨ext_ba, a', ha_m2, had⟩ := RoleVal.role_bound_addr_uncond htblR ev14
    obtain rfl : a' = a := Option.some.inj (had.symm.trans ha)
    obtain ⟨b, hb, rfl⟩ := ha_m2
    -- the load
    have hbound45 : IxVM.Consistency.Bounded cs45 := RomBound.bounded_mono hrun.bounded hsub45
    obtain ⟨-, bytes, E_ld, hhash, hblake, hloaded, hL1⟩ :=
      L1.get_ci_loadedL1_spec hbound45 hb ev47
    have hrecA : Ix.Cert.recordAt ρ.E₀ (ixAddr b) = some c := by
      rw [← hrun.runStore.recordOf_eq_recordAt]
      exact hcE
    obtain ⟨-, -, v, hld, hraw⟩ :=
      LoadedReads.loadedL1_record hrun.runStore hsub45 hhash hblake hL1 hrecA
    obtain rfl : v = v31 := Except.ok.inj (hld.symm.trans ld41)
    obtain ⟨tag, n, tyPtr, rest, src, recurAddrs, blobs, self, e, ty₀, hv, hnlt, raw, hblob,
      hself, hread, hcases⟩ := LoadedReads.loadedTypeReads hrun.runStore hloaded hsub45 hraw hrr
    subst hv
    -- the level count
    obtain ⟨e67, -⟩ := const_num_lvls_fields ev80
    obtain ⟨e68, -, hlt8⟩ := role_levels_spec hn ev100
    have hnn : n = pin.levelParams.length := by
      have hf' : ((n : Nat) : F) = ((pin.levelParams.length : Nat) : F) :=
        Value.field.inj (e67.symm.trans (heq109.trans e68))
      have hv' := congrArg ZMod.val hf'
      rw [RolesAux.val_natCast (by omega), RolesAux.val_natCast (by omega)] at hv'
      exact hv'
    -- the anchor's checks
    obtain ⟨m₁, m₂, m₃, m₄, m₅, m₆, m₇, tyF, nlF, spec, u, w, cs₁, cs₂, cs₃, cs₄, cs₅, e1, evT,
      evN, evW, hcallW, e45, evR, evP⟩ := validate_anchor_pin hfacts.num ev194
    obtain ⟨htyF, hm21⟩ := const_type_of_fields evT
    rw [hm21] at evN
    obtain ⟨hnlF, hm31⟩ := const_num_lvls_fields evN
    rw [htyF, hnlF, hm31] at evW hcallW
    rw [htyF] at evP
    have ext32 : Heap.Extends m32 m111 :=
      ev80.heap_extends.trans (ev100.heap_extends.trans ev124.heap_extends)
    have ext_m3 : Heap.Extends m32 m₁ := ext32.trans e1
    obtain ⟨-, hlbb, hdef⟩ :=
      Assembly.validate_expr_well_scoped_spec hrun.bounded hnlt raw ext_m3 hread evW
        (hsub192 _ hcallW)
    have hread' : (Ix.Kernel.Reader.MemberReader.mk'
        (IxVM.Consistency.readCtx t (fun x => ρ.E₀.blobs.get? x)) src
        (Ix.Kernel.Reader.recParam (List.range n)) self).read e = .ok ty₀ := by
      rw [Assembly.recParam_range]
      exact hread
    obtain ⟨ty', hvs, hrep⟩ :=
      L1.rawConvExpr_to_valRepExact (κ := keyOf t) (name := keyOf t (ixAddr b))
        (ps := List.range n) (by simp) (by simp) hnlt
        (LoadedReads.readCtx_keyAt_inv ht (fun x => ρ.E₀.blobs.get? x)) hself hblob raw hread'
        hlbb hdef
    have hann : IxVM.Consistency.Annotates ty' ty₀ := hvs.2.2
    have htm : Decl.TmCExact (keyOf t) m32 ty' tyPtr := by
      have h4 := hrep.2.2.2
      rw [Decl.posOf_range] at h4
      exact h4
    have ext_m5 : Heap.Extends m32 m₅ := ext_m3.trans (evW.heap_extends.trans e45)
    have htbl5 : TableRep t m₅ x_tbl :=
      htblR.mono (ext_ba.trans (ev47.heap_extends.trans ext_m5))
    have hpinE : ty'.erasePw = pin.type.erasePw :=
      typePinned_erasePw htwf hT htbl5 (htm.mono ext_m5) evR evP
    rcases hcases with hcv | ⟨rc, kF, hfam⟩ | hq
    · -- the reading declares the anchor's constant; the stored constant stores it
      have hvsS := hst.1
      rw [hcv] at hvsS
      obtain ⟨hn1, hl1, ha1⟩ := hvsS
      refine matchesPin_of_fields (hn1.trans (hkeya.trans hname.symm)) ?_ ?_
      · rw [hl1, hnn, ← hlps]
      · exact (annotates_erasePw_eq ha1 hann).trans hpinE
    · -- a recursor's reading has a `∀` domain at its motive, which the pin has not
      exfalso
      have h1 := domForallAt_annot _ hann (domForallAt_of_familyKey hfam)
      rw [← domForallAt_erasePw, hpinE, domForallAt_erasePw] at h1
      rw [hfacts.noDom pin hpin] at h1
      cases h1
    · -- a quotient pin is at its own key
      exfalso
      have hn2 : ci.name = ci₀.name := hst.name_eq
      exact hfacts.notBasis .quotK ci₀ hq (hn2.symm.trans hname_ci)
  | n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hfacts.specKind] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hfacts.specKind] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hfacts.specKind] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hfacts.specKind] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hfacts.specKind] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)

/-! ## The stored shapes at the anchor groups -/

set_option maxRecDepth 100000 in
/-- The groups of the shape roles and of the anchors' constructors. -/
theorem anchor_groups :
    Ix.SpecDigest.groupOf .bool = 6 ∧ Ix.SpecDigest.groupOf .boolFalse = 6 ∧
      Ix.SpecDigest.groupOf .boolTrue = 6 ∧ Ix.SpecDigest.groupOf .char = 41 ∧
      Ix.SpecDigest.groupOf .string = 42 ∧ Ix.SpecDigest.groupOf .list = 43 ∧
      Ix.SpecDigest.groupOf .listNil = 43 ∧ Ix.SpecDigest.groupOf .listCons = 43 ∧
      Ix.SpecDigest.groupOf .charOfNat = 44 ∧ Ix.SpecDigest.groupOf .stringOfList = 45 ∧
      Ix.SpecDigest.groupOf .iff = 16 ∧ Ix.SpecDigest.groupOf .nonempty = 17 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pins of `Bool` and its constructors: no level parameter, `Sort 1` and `Bool`. -/
theorem bool_pins :
    (anchorPin? (.role .bool)).map (fun p => (p.levelParams, p.type.erasePw)) =
        some ([], .sort (.succ .zero)) ∧
      (anchorPin? (.role .boolTrue)).map (fun p => (p.levelParams, p.type.erasePw)) =
        some ([], .const Ix.Kernel.boolName []) ∧
      (anchorPin? (.role .boolFalse)).map (fun p => (p.levelParams, p.type.erasePw)) =
        some ([], .const Ix.Kernel.boolName []) := by
  decide +kernel

private theorem pin_of_map {r : Role} {lps : List Ix.Kernel.LevelParam} {T : KExpr}
    (h : (anchorPin? (.role r)).map (fun p => (p.levelParams, p.type.erasePw)) = some (lps, T)) :
    ∃ pin, anchorPin? (.role r) = some pin ∧ pin.levelParams = lps ∧ pin.type.erasePw = T := by
  cases hp : anchorPin? (.role r) with
  | none => rw [hp] at h; simp at h
  | some pin =>
    rw [hp] at h
    have h' := Option.some.inj h
    exact ⟨pin, rfl, (Prod.mk.inj h').1, (Prod.mk.inj h').2⟩

private theorem pin_fields {ci : Ix.Kernel.ConstantInfo .anon} {pin : Ix.Kernel.ConstantVal .anon}
    (hm : ci.toConstantVal.matchesPin pin = true) :
    ci.toConstantVal.levelParams = pin.levelParams ∧
      ci.toConstantVal.type.erasePw = pin.type.erasePw := by
  unfold Ix.Kernel.ConstantVal.matchesPin at hm
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
  exact ⟨hm.1.2, hm.2⟩

private theorem erasePw_sort_inv' {e : KExpr} {l : KLevel} (h : e.erasePw = .sort l) :
    e = .sort l := by
  cases e <;> simp [Ix.Kernel.Expr.erasePw] at h
  exact congrArg Ix.Kernel.Expr.sort h

private theorem erasePw_const_inv' {e : KExpr} {n : KKey} {us : List KLevel}
    (h : e.erasePw = .const n us) : e = .const n us := by
  cases e <;> simp [Ix.Kernel.Expr.erasePw] at h
  exact congrArg₂ Ix.Kernel.Expr.const h.1 h.2

/-- **`RoleFreeShapes` at an anchor group** (6 and 41 to 45), at every binding run of a table
that binds every role: the shapes below the group are the invariant's, and the shapes the group
adds are the anchors' pins (`anchor_stored_matchesPin`). -/
theorem roleFreeShapes_anchorGroup {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun} {Rs : Nat → Ixon.Env}
    (hrun : BindingRun calls t ρ Rs) (hall : IxVM.Consistency.AllBound t)
    (ht : t.check = .ok ()) {g : Nat} (hg : g = 6 ∨ (41 ≤ g ∧ g ≤ 45)) :
    RoleFreeShapes.{u} L ρ t g := by
  intro _ R R₁ R' env₁ hadm _ hle hb hk
  have hs := hb.facts.shapes
  obtain ⟨gB, gBF, gBT, gC, gS, gL, gLN, gLC, gCN, gSL, gI, gN⟩ := anchor_groups
  have pinAt : ∀ r ∈ pinnedAnchors, Ix.SpecDigest.groupOf r = g →
      ∀ pin, anchorPin? (.role r) = some pin →
        ∃ ci, env₁.find? (.role r) = some ci ∧ ci.toConstantVal.matchesPin pin = true := by
    intro r hr hgr pin hp
    exact anchor_stored_matchesPin hrun hall ht hr
      (hgr ▸ IxVM.Consistency.role_mem_roleGroup r) hadm hle hk hp
  have at_or_below : ∀ X : Role, Ix.SpecDigest.groupOf X < g + 1 →
      Ix.SpecDigest.groupOf X < g ∨ Ix.SpecDigest.groupOf X = g := fun X h =>
    Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h)
  obtain ⟨pB, hpB, hlB, htB⟩ := pin_of_map bool_pins.1
  obtain ⟨pT, hpT, hlT, htT⟩ := pin_of_map bool_pins.2.1
  obtain ⟨pF, hpF, hlF, htF⟩ := pin_of_map bool_pins.2.2
  have litAt : ∀ r ∈ pinnedAnchors, Ix.SpecDigest.groupOf r = g →
      ∃ ci pin, env₁.find? (.role r) = some ci ∧ anchorPin? (.role r) = some pin ∧
        ci.toConstantVal.matchesPin pin = true := by
    intro r hr hgr
    obtain ⟨pin, hp⟩ := (pinnedAnchor_facts hr).pinSome
    obtain ⟨ci, hf, hm⟩ := pinAt r hr hgr pin hp
    exact ⟨ci, pin, hf, hp, hm⟩
  exact {
    bool := fun h => by
      rcases at_or_below _ h with h' | h'
      · exact hs.bool h'
      · obtain ⟨cB, hfB, hmB⟩ := pinAt .bool (by decide) h' pB hpB
        obtain ⟨cT, hfT, hmT⟩ := pinAt .boolTrue (by decide) (gBT.trans (gB.symm.trans h')) pT hpT
        obtain ⟨cF, hfF, hmF⟩ :=
          pinAt .boolFalse (by decide) (gBF.trans (gB.symm.trans h')) pF hpF
        obtain ⟨lB, eB⟩ := pin_fields hmB
        obtain ⟨lT, eT⟩ := pin_fields hmT
        obtain ⟨lF, eF⟩ := pin_fields hmF
        exact ⟨⟨cB, hfB, lB.trans hlB, erasePw_sort_inv' (eB.trans htB)⟩,
          ⟨⟨cT, hfT, lT.trans hlT⟩, ⟨cF, hfF, lF.trans hlF⟩⟩,
          ⟨⟨cT, hfT, erasePw_const_inv' (eT.trans htT)⟩,
            ⟨cF, hfF, erasePw_const_inv' (eF.trans htF)⟩⟩⟩
    char := fun h => by
      rcases at_or_below _ h with h' | h'
      · exact hs.char h'
      · obtain ⟨ci, pin, hf, hp, hm⟩ := litAt .char (by decide) h'
        show Ix.Kernel.charTyOk (env₁.find? (.role .char)) = true
        rw [hf]
        exact Assembly.charTyOk_of_matchesPin hp hm
    string := fun h => by
      rcases at_or_below _ h with h' | h'
      · exact hs.string h'
      · obtain ⟨ci, pin, hf, hp, hm⟩ := litAt .string (by decide) h'
        show Ix.Kernel.stringTyOk (env₁.find? (.role .string)) = true
        rw [hf]
        exact Assembly.stringTyOk_of_matchesPin hp hm
    list := fun h => by
      rcases at_or_below _ h with h' | h'
      · exact hs.list h'
      · obtain ⟨ci, pin, hf, hp, hm⟩ := litAt .list (by decide) h'
        obtain ⟨ciN, pinN, hfN, hpN, hmN⟩ :=
          litAt .listNil (by decide) (gLN.trans (gL.symm.trans h'))
        obtain ⟨ciC, pinC, hfC, hpC, hmC⟩ :=
          litAt .listCons (by decide) (gLC.trans (gL.symm.trans h'))
        refine ⟨?_, ?_, ?_⟩
        · show Ix.Kernel.listTyOk (env₁.find? (.role .list)) = true
          rw [hf]
          exact Assembly.listTyOk_of_matchesPin hp hm
        · show Ix.Kernel.listNilTyOk (env₁.find? (.role .listNil)) = true
          rw [hfN]
          exact Assembly.listNilTyOk_of_matchesPin hpN hmN
        · show Ix.Kernel.listConsTyOk (env₁.find? (.role .listCons)) = true
          rw [hfC]
          exact Assembly.listConsTyOk_of_matchesPin hpC hmC
    charOfNat := fun h => by
      rcases at_or_below _ h with h' | h'
      · exact hs.charOfNat h'
      · obtain ⟨ci, pin, hf, hp, hm⟩ := litAt .charOfNat (by decide) h'
        show Ix.Kernel.charOfNatTyOk (env₁.find? (.role .charOfNat)) = true
        rw [hf]
        exact Assembly.charOfNatTyOk_of_matchesPin hp hm
    stringOfList := fun h => by
      rcases at_or_below _ h with h' | h'
      · exact hs.stringOfList h'
      · obtain ⟨ci, pin, hf, hp, hm⟩ := litAt .stringOfList (by decide) h'
        show Ix.Kernel.stringOfListTyOk (env₁.find? (.role .stringOfList)) = true
        rw [hf]
        exact Assembly.stringOfListTyOk_of_matchesPin hp hm
    iff := fun h => by
      rcases at_or_below _ h with h' | h'
      · exact hs.iff h'
      · exfalso
        rw [gI] at h'
        omega
    nonempty := fun h => by
      rcases at_or_below _ h with h' | h'
      · exact hs.nonempty h'
      · exfalso
        rw [gN] at h'
        omega }

/-- **The composed residual's `groupWithoutRoleUnit`, from its instances at groups 16 and 17**:
the other shape groups are the anchor groups (`roleFreeShapes_anchorGroup`), and the groups
with no shape role read no new shape (`groupWithoutRoleUnit_of_shapeGroups`). -/
theorem groupWithoutRoleUnit_of_iffNonempty
    (h1617 : ∀ calls : List (Call F), AtGroups (BindingRun calls)
      (fun ρ t g => (g = 16 ∨ g = 17) → RoleFreeShapes.{u} Typing.FormerOpenTraceAt ρ t g)) :
    ∀ calls : List (Call F),
      AtGroups (BindingRun calls) (RoleFreeShapes.{u} Typing.FormerOpenTraceAt) := by
  apply groupWithoutRoleUnit_of_shapeGroups
  intro calls t ρ Rs hrun hall ht g h6 h77 hsg
  rcases (shapeGroup_iff g).mp hsg with h | h | h | h
  · exact roleFreeShapes_anchorGroup hrun hall ht (Or.inl h)
  · exact h1617 calls t ρ Rs hrun hall ht g h6 h77 (Or.inl h)
  · exact h1617 calls t ρ Rs hrun hall ht g h6 h77 (Or.inr h)
  · exact roleFreeShapes_anchorGroup hrun hall ht (Or.inr h)

end IxVM.Refinement.Binding
