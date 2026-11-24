import IxVMRefinement.Obs.KernelModeled5
import IxVMRefinement.Obs.KernelModeled6
import IxVMRefinement.Obs.KernelModeled7
import IxVMRefinement.Obs.KernelModeled8
import IxVMRefinement.Obs.KernelModeled9
import IxVMRefinement.Obs.KernelWhnf
import IxVMRefinement.Obs.KernelCheck
import IxVMRefinement.FamilyAlias.CallIotaRule
import IxVMRefinement.FamilyAlias.CheckFamilyReads
import IxVMRefinement.FamilyAlias.ProjFacts
import IxVMRefinement.FamilyAlias.ProjEligible
import IxVMRefinement.Decl.NativeRec
import IxVMRefinement.Decl.NativeCommon
import IxVMRefinement.Decl.ModeledTele
import IxVMRefinement.Decl.ModeledRules
import IxVMRefinement.Levels.Spec
import IxVMRefinement.Levels.Smart
import IxVMRefinement.Core.SpineChain
import IxVMRefinement.Lib.Lists
import IxVMRefinement.Lib.Words
import IxVMRefinement.StatementRel.ClosedFacts

/-! # Auxiliaries and witness structures for `KernelModeled::check_projs`

Provides the helper specifications and witness structures used to invert
`KernelModeled::check_projs` and its callees (`CallProjs.lean`) and to install projection
tables and bounded-graph chain axioms on eligible modeled inductive members
(`ProjTableInstall.lean`):

* `check_recs_stream`: tracks `Ingress.Stream` from `s8` to `s9` across `KernelModeled::check_recs`;
* explicit-symbol `Lib.Lists` wrappers for `KExpr`, `KLevel`, and `KRecRule` lists;
* `Core.Tm` / `ExprSemEq` helpers: `tm_monoK`, `tm_liftD_closed`, `tm_stored_to_famKey`,
  `openDummiesP`, `tm_openDummiesP`, `peel_n_lams_collect_tm`, `collect_spine_tm`,
  `bvars_desc_tm`, `spec_params_ptr_eq_tm_one`, `struct_eq_tele_tm`, `StripPisZeta`,
  `peel_n_foralls_zeta_open`, `type_sort_never_tm`, `StripPisZetaSort`, and
  `type_sort_fixed_zeta_tm`;
* stored-constant loaders (`ctorRecord_raw_of_get_ci`) and reserved-basis exclusion lemmas
  (`not_reserved_ind_of_neverZero_arity`, `not_reserved_ctor_of_nP_pos_or_eqRefl`,
  `not_reserved_tag_ind`, `not_reserved_tag_ctor`);
* witness structures (`NativeIndWitness`, `NativeCtorWitness`, `UnpackRebuildArgWitness`,
  `UnpackMinorWitness`, `ProjMinorWitness`, `ProjPureBodyWitness`, `ProjPureWitness`,
  `FieldProjFacts`, `MemberProjFacts`, `BlockProjFacts`). -/

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Decl (ExprSemEq)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList substLevel)
open IxVM.Consistency
open IxVM (F)
open Ix.Kernel (Expr Level ConstantInfo ConstantVal RecRule LevelParam)
open Ix.Kernel.Semantics (NativeFam)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false

universe u

/-! ## Field / arithmetic helpers -/

theorem nat_eq_of_field_eq_u56_p {a b : Nat} (ha : a < 72057594037927936)
    (hb : b < 72057594037927936) (heq : (a : F) = (b : F)) : a = b := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  have hv := congrArg ZMod.val heq
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv

theorem nat_eq_of_field_eq_wide_p {a b : Nat} (ha : a < 4611686018427387904)
    (hb : b < 4611686018427387904) (heq : (a : F) = (b : F)) : a = b := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  have hv := congrArg ZMod.val heq
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv

theorem evalBinOp_add_field_p {a b : F} {v : SourceValue F}
    (op : evalBinOp .add (.field a) (.field b) = .ok v) : v = .field (a + b) := by
  simp only [evalBinOp, Except.ok.injEq] at op; exact op.symm

theorem evalBinOp_sub_field_p {a b : F} {v : SourceValue F}
    (op : evalBinOp .sub (.field a) (.field b) = .ok v) : v = .field (a - b) := by
  simp only [evalBinOp, Except.ok.injEq] at op; exact op.symm

theorem val_natCast_wide_p {n : Nat} (hn : n < 4611686018427387904) :
    ZMod.val (n : F) = n := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  exact ZMod.val_natCast_of_lt (by omega)

/-! ## Section 1: Stream tracking across `KernelModeled::check_recs` -/

theorem check_rules_go_stream :
    ∀ {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {cs : List (Call F)},
      ObsFn Obs.W "KernelModeled::check_rules_go" args h r h' cs →
      ∀ rc rm nl ty rp ni rules ib iidx inp ilvls pins src dst aset s j bytes,
        args = [rc, rm, nl, ty, rp, ni, rules, ib, iidx, inp, ilvls, pins, src, dst, aset, s, j] →
        Ingress.Stream h bytes s →
        ∃ bytes', Ingress.Stream h' bytes' r := by
  have hmain : ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn Obs.W fname args h r h' cs → fname = "KernelModeled::check_rules_go" →
      ∀ rc rm nl ty rp ni rules ib iidx inp ilvls pins src dst aset s j bytes,
        args = [rc, rm, nl, ty, rp, ni, rules, ib, iidx, inp, ilvls, pins, src, dst, aset, s, j] →
        Ingress.Stream h bytes s →
        ∃ bytes', Ingress.Stream h' bytes' r :=
    ObsFn.strong_induction (world := Obs.W)
      (fun fname args h r h' cs => fname = "KernelModeled::check_rules_go" →
        ∀ rc rm nl ty rp ni rules ib iidx inp ilvls pins src dst aset s j bytes,
          args = [rc, rm, nl, ty, rp, ni, rules, ib, iidx, inp, ilvls, pins, src, dst, aset, s, j] →
          Ingress.Stream h bytes s →
          ∃ bytes', Ingress.Stream h' bytes' r)
      (fun fname args h r h' cs ev ih hfn rc rm nl ty rp ni rules ib iidx inp ilvls pins src dst
          aset s j bytes hargs hstr => by
        subst hfn hargs
        match Obs.«KernelModeled::check_rules_go».obs ev with
        | .Nil (he21 := hr) (he22 := hh) .. =>
          subst hr hh; exact ⟨bytes, hstr⟩
        | .Cons (cs432 := csNext) (ev54 := eAddr) (ev129 := eProj) (ev171 := eCi) (ev292 := eIota)
            (ev434 := eNext) (hc579 := hc) .. =>
          obtain ⟨_, bytes1, _, _, -, htup, -, hstr1, -, -⟩ := Decl.get_address_spec hstr eAddr
          simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
          obtain ⟨-, hx2⟩ := htup
          rw [← hx2] at hstr1
          have ext := eProj.heap_extends.trans (eCi.heap_extends.trans eIota.heap_extends)
          have hlt : csNext.length < cs.length := by
            rw [hc]; simp only [List.length_cons, List.length_append]; omega
          exact ih _ _ _ _ _ _ hlt eNext rfl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bytes1 rfl
            (hstr1.mono ext))
  intro args h h' r cs ev rc rm nl ty rp ni rules ib iidx inp ilvls pins src dst aset s j bytes
    hargs hstr
  exact hmain _ _ _ _ _ _ ev rfl rc rm nl ty rp ni rules ib iidx inp ilvls pins src dst aset s j
    bytes hargs hstr

theorem check_rules_stream {rc rm nl ty rp ni rules src dst aset s r : SourceValue F}
    {bytes : List UInt8} {h h' : Heap F} {cs : List (Call F)}
    (hstr : Ingress.Stream h bytes s)
    (ev : ObsFn Obs.W "KernelModeled::check_rules"
      [rc, rm, nl, ty, rp, ni, rules, src, dst, aset, s] h r h' cs) :
    ∃ bytes', Ingress.Stream h' bytes' r := by
  match Obs.«KernelModeled::check_rules».obs ev with
  | .run (ev14 := ePins) (ev74 := eCi) (ev157 := eLen) (ev_bcyyrzqq := eRen) (ev179 := eGo) .. =>
    have ext := ePins.heap_extends.trans (eCi.heap_extends.trans (eLen.heap_extends.trans eRen.heap_extends))
    exact check_rules_go_stream eGo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bytes rfl (hstr.mono ext)

theorem check_recs_stream {recAs : List Bytes.Address} :
    ∀ {rc tys recs models src dst aset s n k np uo bnl fam form r : SourceValue F}
      {bytes : List UInt8} {h h' : Heap F} {cs : List (Call F)},
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h recAs recs →
      Ingress.Stream h bytes s →
      ObsFn Obs.W "KernelModeled::check_recs"
        [rc, tys, recs, models, src, dst, aset, s, n, k, np, uo, bnl, fam, form] h r h' cs →
      ∃ bytes', Ingress.Stream h' bytes' r := by
  induction recAs with
  | nil =>
    intro rc tys recs models src dst aset s n k np uo bnl fam form r bytes h h' cs hrep hstr ev
    rcases checkRecs_step ev with ⟨-, hr, hh⟩ | ⟨⟨C⟩⟩
    · subst hr hh; exact ⟨bytes, hstr⟩
    · obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hrep C.ldRecs
      cases he
  | cons a rest ih =>
    intro rc tys recs models src dst aset s n k np uo bnl fam form r bytes h h' cs hrep hstr ev
    rcases checkRecs_step ev with ⟨ldNil, -, -⟩ | ⟨⟨C⟩⟩
    · exact absurd (Lib.rep_nil_of_load hrep ldNil) (List.cons_ne_nil _ _)
    · obtain ⟨_, _, he, -, hrest⟩ := Lib.rep_cons_of_load hrep C.ldRecs
      injection he with _ h2; subst h2
      obtain ⟨bytes1, hstr1⟩ := check_rules_stream (hstr.mono C.ext_h_m838) C.evRules.obs
      have ext := C.ext_h_m838.trans C.evRules.extends
      exact ih (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext hrest) hstr1
        C.evNext.obs

/-! ## Section 2: Explicit-symbol `Lib.Lists` wrappers and `RulesRep` lookup -/

theorem kexprList_length_spec {R : Heap F → KExpr → SourceValue F → Prop} {xs : List KExpr}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    r = .field (xs.length : F) ∧ h' = h := by
  rw [← Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol] at ev
  change RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» R h xs l at hl
  rw [← Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hl
  exact Lib.Lists.length_spec ev hl

theorem kexprList_take_spec {R : Heap F → KExpr → SourceValue F → Prop} (hR : HeapMono₂ R)
    {xs : List KExpr} {l r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::take<&KernelTypes::KExprNode>» [l, .field n] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    n.val ≤ xs.length ∧ RepList kexprListEnum R h' (xs.take n.val) r := by
  rw [← Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol] at ev
  change RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» R h xs l at hl
  rw [← Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hl
  obtain ⟨hle, hr⟩ := Lib.Lists.take_spec hR ev hl
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hr
  exact ⟨hle, hr⟩

theorem kexprList_drop_spec {R : Heap F → KExpr → SourceValue F → Prop}
    {xs : List KExpr} {l r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [l, .field n] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    n.val ≤ xs.length ∧ RepList kexprListEnum R h (xs.drop n.val) r ∧ h' = h := by
  rw [← Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol] at ev
  change RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» R h xs l at hl
  rw [← Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hl
  obtain ⟨hle, hr, hh⟩ := Lib.Lists.drop_spec n.val rfl ev hl
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hr
  exact ⟨hle, hr, hh⟩

theorem kexprList_lookup_spec {R : Heap F → KExpr → SourceValue F → Prop}
    {xs : List KExpr} {l r : SourceValue F} {i : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [l, .field i] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) :
    (∃ x, xs[i.val]? = some x ∧ R h x r) ∧ h' = h := by
  rw [← Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>».symbol] at ev
  change RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» R h xs l at hl
  rw [← Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hl
  exact Lib.Lists.lookup_spec ev hl

theorem kexprList_concat_spec {R : Heap F → KExpr → SourceValue F → Prop} (hR : HeapMono₂ R)
    {xs ys : List KExpr} {a b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::concat<&KernelTypes::KExprNode>» [a, b] h r h' cs)
    (ha : RepList kexprListEnum R h xs a) (hb : RepList kexprListEnum R h ys b) :
    RepList kexprListEnum R h' (xs ++ ys) r := by
  rw [← Obs.Names.«Lists::concat<&KernelTypes::KExprNode>».symbol] at ev
  change RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» R h xs a at ha
  change RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» R h ys b at hb
  rw [← Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at ha hb
  have hr := Lib.Lists.concat_spec hR ev ha hb
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hr
  exact hr

theorem kexprList_snoc_spec {R : Heap F → KExpr → SourceValue F → Prop} (hR : HeapMono₂ R)
    {xs : List KExpr} {x : KExpr} {l v r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>» [l, v] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) (hx : R h x v) :
    RepList kexprListEnum R h' (xs ++ [x]) r := by
  rw [← Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>».symbol] at ev
  change RepList Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» R h xs l at hl
  rw [← Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hl
  have hr := Lib.Lists.snoc_spec hR ev hl hx
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hr
  exact hr

theorem klevelList_length_spec {ls : List KLevel} {l r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [l] h r h' cs)
    (hl : RepKLevelList h ls l) :
    r = .field (ls.length : F) ∧ h' = h := by
  rw [← Obs.Names.«Lists::length<&KernelTypes::KLevelNode>».symbol] at ev
  change RepList KernelLevels.klevelListEnum RepKLevel h ls l at hl
  rw [Levels.klevelList_names, ← Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol] at hl
  exact Lib.Lists.length_spec ev hl

theorem klevelList_drop_spec {ls : List KLevel} {l r : SourceValue F} {n : F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::drop<&KernelTypes::KLevelNode>» [l, .field n] h r h' cs)
    (hl : RepKLevelList h ls l) :
    n.val ≤ ls.length ∧ RepKLevelList h (ls.drop n.val) r ∧ h' = h := by
  rw [← Obs.Names.«Lists::drop<&KernelTypes::KLevelNode>».symbol] at ev
  change RepList KernelLevels.klevelListEnum RepKLevel h ls l at hl
  rw [Levels.klevelList_names, ← Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol] at hl
  obtain ⟨hle, hr, hh⟩ := Lib.Lists.drop_spec n.val rfl ev hl
  rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol, ← Levels.klevelList_names] at hr
  exact ⟨hle, hr, hh⟩

/-- View `RulesRep` as a `RepList` over `(rl, j)` pairs indexed from `j0`. -/
theorem rulesRep_to_repList {κ : _root_.Address → KKey} {h : Heap F} {ps : List LevelParam} :
    ∀ {j0 : Nat} {v : SourceValue F} {rls : List (RecRule .anon)},
      RulesRep κ h ps j0 v rls →
      RepList krrListEnum (fun h p v => RuleRep κ h ps p.2 v p.1) h (rls.zipIdx j0) v := by
  intro j0 v rls hr
  induction hr with
  | nil cell => exact .nil cell
  | cons cell h1 _ ih => exact .cons cell h1 ih

theorem krecRuleList_lookup_spec {κ : _root_.Address → KKey} {h h' : Heap F}
    {ps : List LevelParam} {j0 : Nat} {v r : SourceValue F} {i : F} {rls : List (RecRule .anon)}
    {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::lookup<KernelTypes::KRecRule>» [v, .field i] h r h' cs)
    (hr : RulesRep κ h ps j0 v rls) :
    (∃ rl, rls[i.val]? = some rl ∧ RuleRep κ h ps (j0 + i.val) r rl) ∧ h' = h := by
  have hl := rulesRep_to_repList hr
  rw [← Obs.Names.«Lists::lookup<KernelTypes::KRecRule>».symbol] at ev
  change RepList Obs.Names.«Lists::Node<KernelTypes::KRecRule>» _ h (rls.zipIdx j0) v at hl
  rw [← Obs.Names.«Lists::Node<KernelTypes::KRecRule>».symbol] at hl
  obtain ⟨⟨⟨rl, idx⟩, hget, hrule⟩, rfl⟩ := Lib.Lists.lookup_spec ev hl
  rw [List.getElem?_zipIdx] at hget
  cases hg : rls[i.val]? with
  | none => rw [hg] at hget; cases hget
  | some rl' =>
    rw [hg] at hget
    injection hget with hp
    injection hp with hrl hidx
    subst hrl hidx
    exact ⟨⟨rl', rfl, hrule⟩, rfl⟩

/-! ## Section 3: `Core.Tm`, `ExprSemEq`, and telescope helpers -/

/-- Monotonicity of `Core.Tm` in the local binder count `k` when `d = 0`. -/
theorem tm_monoK {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F} :
    ∀ {k k' : Nat} {E : KExpr} {p : SourceValue F},
      k ≤ k' → Tm κ 0 Γ h k E p → Tm κ 0 Γ h k' E p := by
  intro k k' E p hle rep
  induction rep generalizing k' with
  | bvarLocal cell hs hi => exact .bvarLocal cell hs (by omega)
  | bvarFree _ _ _ hd => exact nomatch hd
  | sort cell rl hu => exact .sort cell rl hu
  | const cell ra rls hus => exact .const cell ra rls hus
  | app cell _ _ ihf iha => exact .app cell (ihf hle) (iha hle)
  | lam cell _ _ rl iht ihb => exact .lam cell (iht hle) (ihb (Nat.add_le_add_right hle 1)) rl
  | forallE cell _ _ rl iht ihb =>
    exact .forallE cell (iht hle) (ihb (Nat.add_le_add_right hle 1)) rl
  | letE cell _ _ _ iht ihv ihb =>
    exact .letE cell (iht hle) (ihv hle) (ihb (Nat.add_le_add_right hle 1))
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | proj cell ra _ ihe => exact .proj cell ra (ihe hle)

/-- Lift a closed `Core.Tm` (`d = 0`) to any outer depth `d'`. -/
theorem tm_liftD_closed {κ : _root_.Address → KKey} {Γ₁ Γ₂ : Nat → KExpr} {h : Heap F}
    (d' : Nat) :
    ∀ {k : Nat} {E : KExpr} {p : SourceValue F},
      Tm κ 0 Γ₁ h k E p → Tm κ d' Γ₂ h k E p := by
  intro k E p rep
  induction rep with
  | bvarLocal cell hs hi => exact .bvarLocal cell hs hi
  | bvarFree _ _ _ hd => exact nomatch hd
  | sort cell rl hu => exact .sort cell rl hu
  | const cell ra rls hus => exact .const cell ra rls hus
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | letE cell _ _ _ iht ihv ihb => exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | proj cell ra _ ihe => exact .proj cell ra ihe

theorem tm_openDummiesP {κ : _root_.Address → KKey} {h : Heap F} :
    ∀ (m d c : Nat) {E : KExpr} {p : SourceValue F},
      Tm κ d zeroGhost h (c + m) E p →
      Tm κ (d + m) zeroGhost h c (openDummiesP m d c E) p
  | 0, d, c, _, _, rep => by simpa [openDummiesP] using rep
  | m + 1, d, c, E, p, rep => by
    have hop := rep.open (Γ' := zeroGhost) (T := .sort .zero) rfl (fun _ _ => rfl) (c + m)
      (by omega)
    have ih := tm_openDummiesP m (d + 1) c hop
    rwa [show d + 1 + m = d + (m + 1) by omega] at ih

/-- `KernelCheck::peel_n_lams_collect` on `Tm` at `d = 0, k`: strips `n` lambdas and returns the
body represented at `k + n`. -/
private theorem peel_n_lams_collect_tm_go (rem : Nat) :
    ∀ {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat}
      {e acc r_e r_acc : SourceValue F} {n peeled d_out : F}
      {h h' : Heap F} {cs : List (Call F)} {E : KExpr},
      ZMod.val n = rem →
      ZMod.val peeled + rem = ZMod.val d_out →
      ZMod.val d_out < 4611686018427387904 →
      ObsFn Obs.W "KernelCheck::peel_n_lams_collect" [e, .field n, .field peeled, acc]
        h (.tuple [r_e, .field d_out, r_acc]) h' cs →
      Tm κ 0 Γ h k E e →
      ∃ bs body, E.stripLams rem = some (bs, body) ∧ Tm κ 0 Γ h' (k + rem) body r_e := by
  induction rem with
  | zero =>
    intro κ Γ k e acc r_e r_acc n peeled d_out h h' cs E hn _ _ ev hE
    have h0 : n = 0 := (ZMod.val_eq_zero n).mp hn
    subst h0
    rcases Obs.«KernelCheck::peel_n_lams_collect».obs ev with ⟨_, he_tup, hh, _⟩ |
      ⟨_, _, _, _, _, _, _, hne, _, _, _, _, _, _⟩ | ⟨_, hne, _, _, _, _, _⟩
    · subst hh
      injection he_tup with hl; injection hl with h1 _; subst h1
      exact ⟨[], E, rfl, by simpa using hE⟩
    · exact absurd rfl hne
    · exact absurd rfl hne
  | succ rem ih =>
    intro κ Γ k e acc r_e r_acc n peeled d_out h h' cs E hn hsum hlt ev hE
    rcases Obs.«KernelCheck::peel_n_lams_collect».obs ev with ⟨hv, _, _, _⟩ |
      ⟨x_dom, x_body, _, _, _, _, m131, hne, ld, op_sub, op_add, rfl, ev_rec, _⟩ |
      ⟨_, hne, _, _, he_tup, _, _⟩
    · injection hv with h0; subst h0; simp at hn
    · obtain rfl := Lib.sub_one_inv op_sub
      have hpred := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e]))
      rw [SubstAux.add_ok op_add] at ev_rec
      have h1v : ZMod.val (1 : F) = 1 := ZMod.val_one _
      have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
      have hp1 : ZMod.val (peeled + 1) = ZMod.val peeled + 1 := by
        have := SubstAux.val_add (x := peeled) (y := (1 : F)) (by omega)
        omega
      obtain ⟨T, B, ℓ, rfl, _, hb, _⟩ := hE.lam_of_load ld
      have ext := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [x_dom, acc])
      obtain ⟨bs, body, hstrip, hbody⟩ := ih (k := k + 1) (n := n - 1) (peeled := peeled + 1)
        (d_out := d_out) (by omega) (by omega) hlt ev_rec (hb.mono ext)
      refine ⟨(T, Core.bmeta ℓ) :: bs, body, ?_, ?_⟩
      · simp [Expr.stripLams, hstrip]
      · rwa [show k + 1 + rem = k + (rem + 1) by omega] at hbody
    · injection he_tup with h1; injection h1 with _ h2; injection h2 with h2 _
      injection h2 with hpeel; subst hpeel; omega

theorem peel_n_lams_collect_tm {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat}
    {e acc r_e r_acc : SourceValue F} {d : F} {h h' : Heap F} {cs : List (Call F)} {E : KExpr}
    (hd : ZMod.val d < 4611686018427387904)
    (ev : ObsFn Obs.W "KernelCheck::peel_n_lams_collect" [e, .field d, .field 0, acc]
      h (.tuple [r_e, .field d, r_acc]) h' cs)
    (hE : Tm κ 0 Γ h k E e) :
    ∃ bs body, E.stripLams (ZMod.val d) = some (bs, body) ∧
      Tm κ 0 Γ h' (k + ZMod.val d) body r_e :=
  peel_n_lams_collect_tm_go (ZMod.val d) rfl (by simp) hd ev hE

/-- `KernelTypes::collect_spine` on `Tm` at any `(d, k)`. -/
theorem collect_spine_tm {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {e r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {k : Nat} {E : KExpr}
    (ev : ObsFn Obs.W "KernelTypes::collect_spine" [e] h r h' cs)
    (hE : Tm κ d Γ h k E e) :
    ∃ hd sp H As, r = .tuple [hd, sp] ∧ Tm κ d Γ h' k H hd ∧
      RepList kexprListEnum (fun h A p => Tm κ d Γ h k A p) h' As sp ∧
      E = Expr.mkAppN H As := by
  obtain ⟨hd, sp, ps, rfl, hch, -, hrep⟩ := Core.collect_spine_chain ev
  have hch' := hch.mono ev.heap_extends
  have haux :
      ∀ {xe xhd' : SourceValue F} {ps : List (SourceValue F)},
        Core.SpineChain h' xe xhd' ps →
        ∀ {X : KExpr}, Tm κ d Γ h' k X xe →
          ∃ (H : KExpr) (As : List KExpr),
            Tm κ d Γ h' k H xhd' ∧
            List.Forall₂ (fun A p => Tm κ d Γ h' k A p) As ps ∧
            X = Expr.mkAppN H As := by
    intro xe xhd' ps sc
    induction sc with
    | head _ _ =>
      intro X hX
      exact ⟨X, [], hX, .nil, rfl⟩
    | app ld _ ih =>
      intro X hX
      obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hX.app_of_load ld
      obtain ⟨H, As, hH, hAs, rfl⟩ := ih hf
      exact ⟨H, As ++ [Ea], hH, Core.forall₂_append hAs (.cons ha .nil),
        (SubstAux.mkAppN_snoc As H Ea).symm⟩
  obtain ⟨H, As, hH, hAs, hEq⟩ := haux hch' (hE.mono ev.heap_extends)
  exact ⟨hd, sp, H, As, rfl, hH, Core.repList_of_eq_forall₂ hrep hAs, hEq⟩

/-- `KernelModeled::bvars_desc` at `(d = 0, k)`: produces `.bvar (top - 1), ..., .bvar (top - cnt)`. -/
private theorem bvars_desc_tm_go (rem : Nat) :
    ∀ {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat}
      {top cnt : F} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val cnt = rem →
      rem ≤ ZMod.val top →
      ZMod.val top ≤ k →
      k < 4611686018427387904 →
      ObsFn Obs.W "KernelModeled::bvars_desc" [.field top, .field cnt] h r h' cs →
      RepList kexprListEnum (fun h E p => Tm κ 0 Γ h k E p) h'
        ((List.range rem).map fun m => .bvar (ZMod.val top - 1 - m)) r := by
  induction rem with
  | zero =>
    intro κ Γ k top cnt r h h' cs hcnt _ _ _ ev
    have h0 : cnt = 0 := (ZMod.val_eq_zero cnt).mp hcnt
    subst h0
    match Obs.«KernelModeled::bvars_desc».obs ev with
    | .n0 (he19 := hr) (hm18 := hh) .. => subst hr hh; exact .nil (by simp)
    | .other (hne24 := hne) .. => exact absurd rfl hne
  | succ rem ih =>
    intro κ Γ k top cnt r h h' cs hcnt hle htop hk ev
    match Obs.«KernelModeled::bvars_desc».obs ev with
    | .n0 (hv14 := hv) .. => injection hv with h0; subst h0; simp at hcnt
    | .other (hne24 := hne) (he32 := hr) (hm31 := hm2) (hm47 := hm1)
        (op65 := op_t1) (op94 := op_t2) (op109 := op_c) (ev78 := ev_rec) .. =>
      subst hr hm1 hm2
      obtain rfl := Lib.sub_one_inv op_t1
      obtain rfl := Lib.sub_one_inv op_t2
      obtain rfl := Lib.sub_one_inv op_c
      have hcne : cnt ≠ 0 := fun e => hne (by rw [e])
      have htne : top ≠ 0 := by intro e; subst e; simp at hle
      have hpc := Lib.val_sub_one hcne
      have hpt := Lib.val_sub_one htne
      have hhead : Tm κ 0 Γ (h ++ [.construct kexprEnum "BVar" [.field (top - 1)]]) k
          (.bvar (ZMod.val top - 1)) (.ptr (.enum kexprEnum) h.length) := by
        have h1 : Tm κ 0 Γ (h ++ [.construct kexprEnum "BVar" [.field (top - 1)]]) k
            (.bvar (ZMod.val (top - 1))) (.ptr (.enum kexprEnum) h.length) :=
          .bvarLocal (by simp) (by omega) (by omega)
        rwa [show ZMod.val (top - 1) = ZMod.val top - 1 by omega] at h1
      have htail := ih (κ := κ) (Γ := Γ) (k := k) (top := top - 1) (cnt := cnt - 1)
        (by omega) (by omega) (by omega) hk ev_rec
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.sub_zero]
      have htail_eq :
          ((List.range rem).map ((fun m => (Expr.bvar (ZMod.val top - 1 - m) : KExpr)) ∘ (· + 1))) =
          (List.range rem).map (fun m => .bvar (ZMod.val (top - 1) - 1 - m)) := by
        apply List.map_congr_left
        intro m _; simp only [Function.comp_apply]
        congr 1; omega
      rw [htail_eq]
      exact Lib.rep_store_cons (fun _ _ _ _ e x => x.mono e) (hhead.mono ev_rec.heap_extends) htail

theorem bvars_desc_tm {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat}
    {top cnt : F} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hle_top : ZMod.val cnt ≤ ZMod.val top) (htop_k : ZMod.val top ≤ k)
    (hk : k < 4611686018427387904)
    (ev : ObsFn Obs.W "KernelModeled::bvars_desc" [.field top, .field cnt] h r h' cs) :
    RepList kexprListEnum (fun h E p => Tm κ 0 Γ h k E p) h'
      ((List.range (ZMod.val cnt)).map fun m => .bvar (ZMod.val top - 1 - m)) r :=
  bvars_desc_tm_go (ZMod.val cnt) rfl hle_top htop_k hk ev

/-- `KernelCheck::spec_params_ptr_eq` returning `1` on two `Tm` lists implies pairwise `ExprSemEq`. -/
theorem spec_params_ptr_eq_tm_one {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} :
    ∀ {as_ bs : List KExpr} {pa pb : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      RepList kexprListEnum (fun h e p => Tm κ d Γ h k e p) h as_ pa →
      RepList kexprListEnum (fun h e p => Tm κ d Γ h k e p) h bs pb →
      ObsFn Obs.W "KernelCheck::spec_params_ptr_eq" [pa, pb] h (.field 1) h' cs →
      List.Forall₂ ExprSemEq as_ bs := by
  intro as_
  induction as_ with
  | nil =>
    intro bs pa pb h h' cs ha hb ev
    match Obs.«KernelCheck::spec_params_ptr_eq».obs ev with
    | .Nil_Nil (ld31 := ld2) .. => obtain rfl := Lib.rep_nil_of_load hb ld2; exact .nil
    | .Nil_other (he46 := he) .. => exact absurd (Value.field.inj he) one_ne_zero
    | .Cons_Nil (he85 := he) .. => exact absurd (Value.field.inj he) one_ne_zero
    | .Cons_Cons_n1 (ld12 := ld1) .. =>
      obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load ha ld1; cases he
    | .Cons_Cons_other (ld12 := ld1) .. =>
      obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load ha ld1; cases he
  | cons a rest ih =>
    intro bs pa pb h h' cs ha hb ev
    match Obs.«KernelCheck::spec_params_ptr_eq».obs ev with
    | .Nil_Nil (ld12 := ld1) .. => cases Lib.rep_nil_of_load ha ld1
    | .Nil_other (ld12 := ld1) .. => cases Lib.rep_nil_of_load ha ld1
    | .Cons_Nil (he85 := he) .. => exact absurd (Value.field.inj he) one_ne_zero
    | .Cons_Cons_n1 (ld12 := ld1) (ld77 := ld2) (ev119 := ev1) (ev145 := ev2) .. =>
      obtain ⟨_, _, h1, hxa, hra⟩ := Lib.rep_cons_of_load ha ld1
      injection h1 with h11 h12; subst h11 h12
      obtain ⟨b, bs', rfl, hxb, hrb⟩ := Lib.rep_cons_of_load hb ld2
      have hxy := Decl.kexpr_struct_eq_tm_one hxa hxb ev1
      have htl := ih (RepLinkedList.mono (fun _ _ _ _ ext x => x.mono ext) ev1.heap_extends hra)
        (RepLinkedList.mono (fun _ _ _ _ ext x => x.mono ext) ev1.heap_extends hrb) ev2
      exact .cons hxy htl
    | .Cons_Cons_other (ld12 := ld1) .. =>
      match Obs.«KernelCheck::spec_params_ptr_eq».obs ev with
      | .Cons_Cons_other (he167 := he) .. => exact absurd (Value.field.inj he) one_ne_zero
      | .Nil_Nil (ld12 := ld1') .. => cases Lib.rep_nil_of_load ha ld1'
      | .Nil_other (ld12 := ld1') .. => cases Lib.rep_nil_of_load ha ld1'
      | .Cons_Nil (he85 := he) .. => exact absurd (Value.field.inj he) one_ne_zero
      | .Cons_Cons_n1 (ld12 := ld1') (ld77 := ld2) (ev119 := ev1) (ev145 := ev2) .. =>
        obtain ⟨_, _, h1, hxa, hra⟩ := Lib.rep_cons_of_load ha ld1'
        injection h1 with h11 h12; subst h11 h12
        obtain ⟨b, bs', rfl, hxb, hrb⟩ := Lib.rep_cons_of_load hb ld2
        have hxy := Decl.kexpr_struct_eq_tm_one hxa hxb ev1
        have htl := ih (RepLinkedList.mono (fun _ _ _ _ ext x => x.mono ext) ev1.heap_extends hra)
          (RepLinkedList.mono (fun _ _ _ _ ext x => x.mono ext) ev1.heap_extends hrb) ev2
        exact .cons hxy htl

/-- `KernelModeled::struct_eq_tele` on two `Tm` terms at `(d = 0, k)`: peels `n` `Forall`s from
both with pairwise `ExprSemEq` domains, returning the first term's residual at `k + n`. -/
theorem struct_eq_tele_tm {κ : _root_.Address → KKey} {Γ : Nat → KExpr} :
    ∀ (n : Nat) {k : Nat} {Ea Eb : KExpr} {pa pb r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      n < 4611686018427387904 →
      Tm κ 0 Γ h k Ea pa → Tm κ 0 Γ h k Eb pb →
      ObsFn Obs.W "KernelModeled::struct_eq_tele" [pa, pb, .field (n : F)] h r h' cs →
      ∃ bsa bsb rema remb,
        Ea.stripPis n = some (bsa, rema) ∧
        Eb.stripPis n = some (bsb, remb) ∧
        List.Forall₂ ExprSemEq (bsa.map Prod.fst) (bsb.map Prod.fst) ∧
        Tm κ 0 Γ h' (k + n) rema r := by
  intro n
  induction n with
  | zero =>
    intro k Ea Eb pa pb r h h' cs _ ha hb ev
    match Obs.«KernelModeled::struct_eq_tele».obs ev with
    | .n0 (he_whiproaa := hr) (he_bzwoglyf := hh) .. =>
      subst hr hh
      exact ⟨[], [], Ea, Eb, rfl, rfl, .nil, by simpa using ha⟩
    | .other (hne_xjnibfzs := hne) .. =>
      exact absurd (by simp) hne
  | succ n ih =>
    intro k Ea Eb pa pb r h h' cs hn ha hb ev
    match Obs.«KernelModeled::struct_eq_tele».obs ev with
    | .n0 (hv_fdljvuxp := hv) .. =>
      have h0 : n + 1 = 0 := nat_eq_of_field_eq_wide_p hn (by decide) (by simpa using Value.field.inj hv)
      omega
    | .other (ld_wiaoglet := lda) (ld_bjdlatns := ldb) (ev_lubnqwpv := ev_eq)
        (heq_vcugsbsx := h1) (op_ovxfisas := op) (ev_tnjccnvm := ev_rec) .. =>
      subst h1
      obtain ⟨Da, Ba, ℓa, rfl, hDa, hBa, _⟩ := ha.forallE_of_load lda
      obtain ⟨Db, Bb, ℓb, rfl, hDb, hBb, _⟩ := hb.forallE_of_load ldb
      have hdeq := Decl.kexpr_struct_eq_tm_one hDa hDb ev_eq
      have hop := evalBinOp_sub_field_p op
      rw [hop, show ((n + 1 : Nat) : F) - 1 = (n : F) by push_cast; ring] at ev_rec
      obtain ⟨bsa, bsb, rema, remb, hsa, hsb, hdoms, hrem⟩ :=
        ih (k := k + 1) (by omega) (hBa.mono ev_eq.heap_extends) (hBb.mono ev_eq.heap_extends) ev_rec
      refine ⟨(Da, Core.bmeta ℓa) :: bsa, (Db, Core.bmeta ℓb) :: bsb, rema, remb, ?_, ?_,
        .cons hdeq hdoms, ?_⟩
      · simp [Expr.stripPis, hsa]
      · simp [Expr.stripPis, hsb]
      · rwa [show k + 1 + n = k + (n + 1) by omega] at hrem

/-- `KernelCheck::peel_n_foralls_zeta` on a `Tm` at `(d, k = 0)`: opens `n` `Forall` binders
(stepping through `Let`s) and returns the residual at `(d + n, k = 0)`. -/
theorem peel_n_foralls_zeta_open {κ : _root_.Address → KKey} :
    ∀ {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {cs : List (Call F)},
      ObsFn Obs.W "KernelCheck::peel_n_foralls_zeta" args h r h' cs →
      Bounded cs →
      ∀ (e : SourceValue F) (n d : Nat) (E : KExpr),
        args = [e, .field (n : F)] → n < 4611686018427387904 →
        Tm κ d zeroGhost h 0 E e →
        ∃ rem, StripPisZeta n d E rem ∧ Tm κ (d + n) zeroGhost h' 0 rem r := by
  have hmain : ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn Obs.W fname args h r h' cs → fname = "KernelCheck::peel_n_foralls_zeta" →
      Bounded cs →
      ∀ (e : SourceValue F) (n d : Nat) (E : KExpr),
        args = [e, .field (n : F)] → n < 4611686018427387904 →
        Tm κ d zeroGhost h 0 E e →
        ∃ rem, StripPisZeta n d E rem ∧ Tm κ (d + n) zeroGhost h' 0 rem r :=
    ObsFn.strong_induction (world := Obs.W)
      (fun fname args h r h' cs => fname = "KernelCheck::peel_n_foralls_zeta" → Bounded cs →
        ∀ (e : SourceValue F) (n d : Nat) (E : KExpr),
          args = [e, .field (n : F)] → n < 4611686018427387904 →
          Tm κ d zeroGhost h 0 E e →
          ∃ rem, StripPisZeta n d E rem ∧ Tm κ (d + n) zeroGhost h' 0 rem r)
      (fun fname args h r h' cs ev ih hfn hbd e n d E hargs hn hE => by
        subst hfn hargs
        match Obs.«KernelCheck::peel_n_foralls_zeta».obs ev with
        | .n0 (hv_fdljvuxp := hv) (he_whiproaa := hr) (he_bzwoglyf := hh) .. =>
          subst hr hh
          have hn0 : n = 0 := nat_eq_of_field_eq_wide_p hn (by decide) (Value.field.inj hv)
          subst hn0
          exact ⟨E, .zero d E, by simpa using hE⟩
        | .other_Forall (cs_eadgpktx := cs1) (hne_xjnibfzs := hne) (ld_hdultwxn := ld) (op_czjgbwao := op)
            (ev_imkwftmt := ev_rec) (hc_ydqmxojp := hc) .. =>
          cases n with
          | zero => exact absurd (by simp) hne
          | succ n =>
            obtain ⟨T, B, ℓ, rfl, -, hB, -⟩ := hE.forallE_of_load ld
            have hB' : Tm κ (d + 1) zeroGhost h 0 (B.instantiate1 (.fvar d (.sort .zero)) 0) _ :=
              hB.open (Γ' := zeroGhost) (T := .sort .zero) rfl (fun _ _ => rfl) 0 (by omega)
            have hop := evalBinOp_sub_field_p op
            rw [hop, show ((n + 1 : Nat) : F) - 1 = (n : F) by push_cast; ring] at ev_rec
            have hlt : cs1.length < cs.length := by rw [hc]; simp
            have hbd1 : Bounded cs1 := bounded_sub (fun _ hcl => by rw [hc]; simp [hcl]) hbd
            obtain ⟨rem, hsz, hrem⟩ := ih _ _ _ _ _ _ hlt ev_rec rfl hbd1 _ n (d + 1) _ rfl
              (by omega) hB'
            exact ⟨rem, .forallE n d T B (Core.bmeta ℓ) rem hsz,
              by rwa [show d + 1 + n = d + (n + 1) by omega] at hrem⟩
        | .other_Let (cs_webebuuu := csR) (cs_cuwzkjio := csI) (hne_xjnibfzs := hne) (ld_hdultwxn := ld)
            (ev_mtsqvowg := ev_inst) (ev_vgbqehni := ev_rec) (hc_thparjte := hc) .. =>
          cases n with
          | zero => exact absurd (by simp) hne
          | succ n =>
            obtain ⟨T, V, B, rfl, -, hV, hB⟩ := hE.letE_of_load ld
            have hbdI : Bounded csI := bounded_sub (fun _ hcl => by rw [hc]; simp [hcl]) hbd
            have hbdR : Bounded csR := bounded_sub (fun _ hcl => by rw [hc]; simp [hcl]) hbd
            have hinst : Tm κ d zeroGhost _ 0 (B.instantiate1 V 0) _ :=
              SubstAux.gall κ .expr_inst1 _ _ _ _ _ ev_inst _ _ (0 : F) rfl hbdI d zeroGhost B V
                hB hV
            rw [← instShift_eq_instantiate1 (Tm.looseBVarsBounded hV)] at hinst
            have hlt : csR.length < cs.length := by
              rw [hc]; simp only [List.length_cons, List.length_append]; omega
            obtain ⟨rem, hsz, hrem⟩ := ih _ _ _ _ _ _ hlt ev_rec rfl hbdR _ (n + 1) d _ rfl hn hinst
            exact ⟨rem, hsz, hrem⟩)
  intro args h h' r cs ev hbd e n d E hargs hn hE
  exact hmain _ _ _ _ _ _ ev rfl hbd e n d E hargs hn hE

/-- `KernelWhnf::type_sort_never` returning `1` on a `Tm` at `(d = 0, k)`: certifies `E` strips
`n` `Forall`s directly to `.sort l` whose instantiation at `ls` is never zero. -/
theorem type_sort_never_tm {κ : _root_.Address → KKey} {Γ : Nat → KExpr} :
    ∀ (n : Nat) {k : Nat} {E : KExpr} {ls : List KLevel} {pe pls : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      n < 4611686018427387904 → Bounded cs →
      Tm κ 0 Γ h k E pe → RepKLevelList h ls pls →
      ObsFn Obs.W "KernelWhnf::type_sort_never" [pe, .field (n : F), pls] h (.field 1) h' cs →
      ∃ bs l, E.stripPis n = some (bs, .sort l) ∧
        ∀ φ, (substLevel l ls).eval φ > 0 := by
  intro n
  induction n with
  | zero =>
    intro k E ls pe pls h h' cs _ hbd hE hls ev
    match Obs.«KernelWhnf::type_sort_never».obs ev with
    | .Forall_n0 (he51 := hr) .. => exact absurd (Value.field.inj hr) one_ne_zero
    | .Forall_other (hne54 := hne) .. => exact absurd (by simp) hne
    | .Srt_other (hne159 := hne) .. => exact absurd (by simp) hne
    | .other (he170 := hr) .. => exact absurd (Value.field.inj hr) one_ne_zero
    | .Srt_n0 (cs126 := csN) (cs139 := csI) (ld12 := ld) (ev141 := ev_inst) (ev128 := ev_nz)
        (hc158 := hc) .. =>
      obtain ⟨l, rfl, l', hrepL, hlEq⟩ := hE.sort_of_load ld
      have hbdI : Bounded csI := bounded_sub (fun _ hcl => by rw [hc]; simp [hcl]) hbd
      have hbdN : Bounded csN := bounded_sub (fun _ hcl => by rw [hc]; simp [hcl]) hbd
      obtain ⟨-, hrepInst, -⟩ := IxVM.Refinement.Levels.levelInstParams_obs ev_inst hbdI
        hrepL hls
      have hnz := IxVM.Refinement.Levels.levelIsNotZero_step ev_nz _ rfl (substLevel l' ls) hrepInst
      have hnz_b : Ix.Kernel.Level.isNeverZero (substLevel l' ls) = true := by
        cases h : Ix.Kernel.Level.isNeverZero (substLevel l' ls)
        · rw [h] at hnz; exact absurd (Value.field.inj hnz.1) one_ne_zero
        · rfl
      refine ⟨[], l, rfl, fun φ => ?_⟩
      have hpos : (substLevel l' ls).eval φ ≠ 0 :=
        IxVM.Refinement.KernelLevels.isNeverZero_eval_ne_zero hnz_b φ
      have hev : (substLevel l ls).eval φ = (substLevel l' ls).eval φ :=
        (SubstAux.lvEq_subst (LvEq.refl l) (LvEqList.refl ls) φ).symm.trans
          (SubstAux.lvEq_subst hlEq (LvEqList.refl ls) φ)
      omega
  | succ n ih =>
    intro k E ls pe pls h h' cs hn hbd hE hls ev
    match Obs.«KernelWhnf::type_sort_never».obs ev with
    | .Forall_n0 (he51 := hr) .. => exact absurd (Value.field.inj hr) one_ne_zero
    | .Srt_n0 (hv122 := hv) .. =>
      have h0 : n + 1 = 0 := nat_eq_of_field_eq_wide_p hn (by decide) (by simpa using Value.field.inj hv)
      omega
    | .Srt_other (he163 := hr) .. => exact absurd (Value.field.inj hr) one_ne_zero
    | .other (he170 := hr) .. => exact absurd (Value.field.inj hr) one_ne_zero
    | .Forall_other (cs61 := csR) (ld12 := ld) (op87 := op) (ev63 := ev_rec) (hc96 := hc) .. =>
      obtain ⟨T, B, ℓ, rfl, -, hB, -⟩ := hE.forallE_of_load ld
      have hop := evalBinOp_sub_field_p op
      rw [hop, show ((n + 1 : Nat) : F) - 1 = (n : F) by push_cast; ring] at ev_rec
      have hbdR : Bounded csR := bounded_sub (fun _ hcl => by rw [hc]; simp [hcl]) hbd
      obtain ⟨bs, l, hstrip, hpos⟩ := ih (k := k + 1) (by omega) hbdR hB hls ev_rec
      exact ⟨(T, Core.bmeta ℓ) :: bs, l, by simp [Expr.stripPis, hstrip], hpos⟩

/-- `KernelModeled::peel_n_lams_pw_eq` on a `Tm` at `(d = 0, k)`: peels `n` leading `Lam`s,
each carrying binder-datum equal to `ltgt.zeronessOf`, returning the residual body at `k + n`. -/
theorem peel_n_lams_pw_eq_tm {κ : _root_.Address → KKey} {Γ : Nat → KExpr} :
    ∀ (n : Nat) {k : Nat} {E : KExpr} {ltgt : KLevel} {pe ptgt r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      n < 4611686018427387904 →
      Tm κ 0 Γ h k E pe → RepKLevel h ltgt ptgt →
      ObsFn Obs.W "KernelModeled::peel_n_lams_pw_eq" [pe, .field (n : F), ptgt] h r h' cs →
      ∃ bs body, E.stripLams n = some (bs, body) ∧
        Tm κ 0 Γ h' (k + n) body r ∧
        ∀ bm ∈ bs, bm.2.pw = ltgt.zeronessOf := by
  intro n
  induction n with
  | zero =>
    intro k E ltgt pe ptgt r h h' cs _ hE _ ev
    match Obs.«KernelModeled::peel_n_lams_pw_eq».obs ev with
    | .n0 (he_whiproaa := hr) (he_bzwoglyf := hh) .. =>
      subst hr hh
      exact ⟨[], E, by simp [Expr.stripLams], hE, fun _ hm => nomatch hm⟩
    | .other (hne_xjnibfzs := hne) .. => exact absurd (by simp) hne
  | succ n ih =>
    intro k E ltgt pe ptgt r h h' cs hn hE hltgt ev
    match Obs.«KernelModeled::peel_n_lams_pw_eq».obs ev with
    | .n0 (hv_fdljvuxp := hv) .. =>
      have h0 := nat_eq_of_field_eq_wide_p (a := n + 1) (b := 0) hn (by decide)
        (by simpa using Value.field.inj hv)
      omega
    | .other (ld_wuzaflfx := ld) (ev_rgupupjh := ev_pw) (heq_ptbxpeax := hp1)
        (op_ceyyvofv := op) (ev_ijrvpuwl := ev_rec) .. =>
      subst hp1
      obtain ⟨T, B, ℓ, rfl, -, hB, hℓ⟩ := hE.lam_of_load ld
      have hpw : ℓ.zeronessOf = ltgt.zeronessOf := Decl.pw_eq_one hℓ hltgt ev_pw
      have hop := evalBinOp_sub_field_p op
      rw [hop, show ((n + 1 : Nat) : F) - 1 = (n : F) by push_cast; ring] at ev_rec
      obtain ⟨bs, body, hstrip, hbody, hbs⟩ :=
        ih (k := k + 1) (by omega) (hB.mono ev_pw.heap_extends) (hltgt.mono ev_pw.heap_extends) ev_rec
      refine ⟨(T, Core.bmeta ℓ) :: bs, body, by simp [Expr.stripLams, hstrip], ?_, ?_⟩
      · rwa [show k + (n + 1) = k + 1 + n by omega]
      · intro bm hbm
        rcases List.mem_cons.mp hbm with rfl | hmem
        · exact hpw
        · exact hbs bm hmem

/-- `KernelModeled::type_sort_fixed_zeta` returning `1` (never-zero) or `2` (always-zero) on a
`Tm` at `(d, k = 0)`: certifies that the result sort instantiated at `ls` is either always positive
(when `r = 1`) or always zero (when `r = 2`) across all level assignments `φ`. -/
theorem type_sort_fixed_zeta_tm {κ : _root_.Address → KKey} :
    ∀ {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {cs : List (Call F)},
      ObsFn Obs.W "KernelModeled::type_sort_fixed_zeta" args h r h' cs →
      (r = .field 1 ∨ r = .field 2) →
      Bounded cs →
      ∀ (pe pls : SourceValue F) (n d : Nat) (E : KExpr) (ls : List KLevel),
        args = [pe, .field (n : F), pls] → n < 4611686018427387904 →
        Tm κ d zeroGhost h 0 E pe → RepKLevelList h ls pls →
        ∃ l, StripPisZetaSort n d E l ∧
          ((r = .field 1 ∧ ∀ φ, (substLevel l ls).eval φ > 0) ∨
           (r = .field 2 ∧ ∀ φ, (substLevel l ls).eval φ = 0)) := by
  have h12_ne0 : ∀ {r : SourceValue F}, (r = .field 1 ∨ r = .field 2) → r = .field 0 → False := by
    intro r hr h0
    rcases hr with rfl | rfl
    · exact one_ne_zero (Value.field.inj h0)
    · exact (by decide : (2 : F) ≠ 0) (Value.field.inj h0)
  have hmain : ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn Obs.W fname args h r h' cs → fname = "KernelModeled::type_sort_fixed_zeta" →
      (r = .field 1 ∨ r = .field 2) → Bounded cs →
      ∀ (pe pls : SourceValue F) (n d : Nat) (E : KExpr) (ls : List KLevel),
        args = [pe, .field (n : F), pls] → n < 4611686018427387904 →
        Tm κ d zeroGhost h 0 E pe → RepKLevelList h ls pls →
        ∃ l, StripPisZetaSort n d E l ∧
          ((r = .field 1 ∧ ∀ φ, (substLevel l ls).eval φ > 0) ∨
           (r = .field 2 ∧ ∀ φ, (substLevel l ls).eval φ = 0)) :=
    ObsFn.strong_induction (world := Obs.W)
      (fun fname args h r h' cs => fname = "KernelModeled::type_sort_fixed_zeta" →
        (r = .field 1 ∨ r = .field 2) → Bounded cs →
        ∀ (pe pls : SourceValue F) (n d : Nat) (E : KExpr) (ls : List KLevel),
          args = [pe, .field (n : F), pls] → n < 4611686018427387904 →
          Tm κ d zeroGhost h 0 E pe → RepKLevelList h ls pls →
          ∃ l, StripPisZetaSort n d E l ∧
            ((r = .field 1 ∧ ∀ φ, (substLevel l ls).eval φ > 0) ∨
             (r = .field 2 ∧ ∀ φ, (substLevel l ls).eval φ = 0)))
      (fun fname args h r h' cs ev ih hfn hr12 hbd pe pls n d E ls hargs hn hE hls => by
        subst hfn hargs
        match Obs.«KernelModeled::type_sort_fixed_zeta».obs ev with
        | .Forall_n0 (he_jwdquhsj := hr) .. => exact (h12_ne0 hr12 hr).elim
        | .Srt_other (he_krkybuoo := hr) .. => exact (h12_ne0 hr12 hr).elim
        | .Srt_n0_other_other (he_aerwnprt := hr) .. => exact (h12_ne0 hr12 hr).elim
        | .other (he_vpckpvxl := hr) .. => exact (h12_ne0 hr12 hr).elim
        | .Forall_other (cs_rjdotect := csR) (ld_bolbylmd := ld) (hne_pigtkltp := hne)
            (op_zolfdmjq := op) (ev_vhnccrtc := ev_rec) (hc_hkhtpxta := hc) .. =>
          cases n with
          | zero => exact absurd (by simp) hne
          | succ n =>
            obtain ⟨T, B, ℓ, rfl, -, hB, -⟩ := hE.forallE_of_load ld
            have hB' : Tm κ (d + 1) zeroGhost h 0 (B.instantiate1 (.fvar d (.sort .zero)) 0) _ :=
              hB.open (Γ' := zeroGhost) (T := .sort .zero) rfl (fun _ _ => rfl) 0 (by omega)
            have hop := evalBinOp_sub_field_p op
            rw [hop, show ((n + 1 : Nat) : F) - 1 = (n : F) by push_cast; ring] at ev_rec
            have hlt : csR.length < cs.length := by rw [hc]; simp
            have hbdR : Bounded csR := bounded_sub (fun _ hcl => by rw [hc]; simp [hcl]) hbd
            obtain ⟨l, hsz, hfix⟩ := ih _ _ _ _ _ _ hlt ev_rec rfl hr12 hbdR _ pls n (d + 1) _ ls
              rfl (by omega) hB' hls
            exact ⟨l, .forallE n d T B (Core.bmeta ℓ) l hsz, hfix⟩
        | .Srt_n0_n1 (cs_fmwzbmlc := csI) (cs_nlhntdye := csN) (ld_bolbylmd := ld)
            (hv_nnibqruc := hv) (ev_sxlthtfw := ev_inst) (ev_svpvjrxo := ev_nz)
            (he_rtqmuoja := hr) (hc_oyewrryg := hc) .. =>
          have hn0 : n = 0 := nat_eq_of_field_eq_wide_p hn (by decide) (by simpa using Value.field.inj hv)
          subst hn0
          obtain ⟨l, rfl, l', hrepL, hlEq⟩ := hE.sort_of_load ld
          have hbdI : Bounded csI := bounded_sub (fun _ hcl => by rw [hc]; simp [hcl]) hbd
          obtain ⟨-, hrepInst, -⟩ := IxVM.Refinement.Levels.levelInstParams_obs ev_inst hbdI
            hrepL hls
          have hnz := IxVM.Refinement.Levels.levelIsNotZero_step ev_nz _ rfl (substLevel l' ls) hrepInst
          have hnz_b : Ix.Kernel.Level.isNeverZero (substLevel l' ls) = true := by
            cases h : Ix.Kernel.Level.isNeverZero (substLevel l' ls)
            · rw [h] at hnz; exact absurd (Value.field.inj hnz.1) one_ne_zero
            · rfl
          refine ⟨l, .srt d l, Or.inl ⟨hr, fun φ => ?_⟩⟩
          have hpos : (substLevel l' ls).eval φ ≠ 0 :=
            IxVM.Refinement.KernelLevels.isNeverZero_eval_ne_zero hnz_b φ
          have hev : (substLevel l ls).eval φ = (substLevel l' ls).eval φ :=
            (SubstAux.lvEq_subst (LvEq.refl l) (LvEqList.refl ls) φ).symm.trans
              (SubstAux.lvEq_subst hlEq (LvEqList.refl ls) φ)
          omega
        | .Srt_n0_other_n1 (m_ggprzhbz := mG) (cs_fmwzbmlc := csI) (m_myfdxupx := mN)
            (cs_nlhntdye := csN) (m_xbkfsguv := mZ)
            (ld_bolbylmd := ld) (hv_nnibqruc := hv) (ev_sxlthtfw := ev_inst)
            (ev_svpvjrxo := ev_nz) (hm_zhnaghbn := hmZ) (ev_ekppoezm := ev_pw)
            (he_prgyeswj := hr) (hc_zihctbar := hc) .. =>
          have hn0 : n = 0 := nat_eq_of_field_eq_wide_p hn (by decide) (by simpa using Value.field.inj hv)
          subst hn0
          obtain ⟨l, rfl, l', hrepL, hlEq⟩ := hE.sort_of_load ld
          have hbdI : Bounded csI := bounded_sub (fun _ hcl => by rw [hc]; simp [hcl]) hbd
          obtain ⟨-, hrepInst, -⟩ := IxVM.Refinement.Levels.levelInstParams_obs ev_inst hbdI
            hrepL hls
          have extZ : Heap.Extends mG mZ := by
            rw [hmZ]; exact ev_nz.heap_extends.trans (Heap.Extends.snoc _ _)
          have hrepZero : RepKLevel mZ .zero (.ptr (.enum KernelLevels.klevelEnum) mN.length) := by
            rw [hmZ]; exact .zero (by simp)
          have hpw : (substLevel l' ls).zeronessOf = Level.zero.zeronessOf :=
            Decl.pw_eq_one (hrepInst.mono extZ) hrepZero ev_pw
          refine ⟨l, .srt d l, Or.inr ⟨hr, fun φ => ?_⟩⟩
          have hhold := congrArg (fun p => p.holds φ) hpw
          rw [Ix.Kernel.PropWhen.zeronessOf_sound, Ix.Kernel.PropWhen.zeronessOf_sound] at hhold
          simp only [Ix.Kernel.Level.eval, beq_self_eq_true, beq_iff_eq] at hhold
          have hev : (substLevel l ls).eval φ = (substLevel l' ls).eval φ :=
            (SubstAux.lvEq_subst (LvEq.refl l) (LvEqList.refl ls) φ).symm.trans
              (SubstAux.lvEq_subst hlEq (LvEqList.refl ls) φ)
          rw [hev, hhold]
        | .Let (cs_qmfqshoo := csR) (cs_yqrxeseo := csI) (ld_bolbylmd := ld)
            (ev_gemvpjgn := ev_inst) (ev_uapejewl := ev_rec) (hc_qubwlzze := hc) .. =>
          obtain ⟨T, V, B, rfl, -, hV, hB⟩ := hE.letE_of_load ld
          have hbdI : Bounded csI := bounded_sub (fun _ hcl => by rw [hc]; simp [hcl]) hbd
          have hbdR : Bounded csR := bounded_sub (fun _ hcl => by rw [hc]; simp [hcl]) hbd
          have hinst : Tm κ d zeroGhost _ 0 (B.instantiate1 V 0) _ :=
            SubstAux.gall κ .expr_inst1 _ _ _ _ _ ev_inst _ _ (0 : F) rfl hbdI d zeroGhost B V
              hB hV
          rw [← instShift_eq_instantiate1 (Tm.looseBVarsBounded hV)] at hinst
          have hlt : csR.length < cs.length := by
            rw [hc]; simp only [List.length_cons, List.length_append]; omega
          obtain ⟨l, hsz, hfix⟩ := ih _ _ _ _ _ _ hlt ev_rec rfl hr12 hbdR _ pls n d _ ls rfl hn
            hinst (hls.mono ev_inst.heap_extends)
          exact ⟨l, hsz, hfix⟩)
  intro args h h' r cs ev hr12 hbd pe pls n d E ls hargs hn hE hls
  exact hmain _ _ _ _ _ _ ev rfl hr12 hbd pe pls n d E ls hargs hn hE hls

/-! ## Section 4: Constructor record extraction and reserved-basis exclusion -/

private theorem defnValShape_ne_ctor (d : Ixon.Definition) (a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 : SourceValue F)
    (h : Ingress.defnValShape d b1 b2 b3 = .construct Core.kciEnum "Ctor" [a1, a2, a3, a4, a5, a6, a7, a8]) :
    False := by
  unfold Ingress.defnValShape at h
  cases hk : d.kind with
  | defn => rw [hk] at h; simp at h
  | opaq => rw [hk] at h; simp at h
  | thm => rw [hk] at h; simp at h

/-- **Constructor record extraction from `Ingress::get_ci`**: mirrors `Ingress.inductRecord_raw_of_get_ci`
when the returned `KConstantInfo` cell is `Ctor`. -/
theorem ctorRecord_raw_of_get_ci {addr ptr : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {a : Bytes.Address}
    {nl ty blk idx cidx np nf u : SourceValue F}
    (ev : ObsFn Obs.W "Ingress::get_ci" [addr] h ptr h' cs)
    (hbounded : Bounded cs)
    (ha : Bytes.RepAddressRef addrTy h a addr)
    (hld_ctor : loadValue h' ptr =
      .ok (.construct kciEnum "Ctor" [nl, ty, blk, idx, cidx, np, nf, u])) :
    ∃ (rawBytes blkBytes : ByteArray) (cm cb : Ixon.Constant)
      (xs : Array Ixon.MutConst) (ind : Ixon.Inductive) (ct : Ixon.Constructor)
      (b : Bytes.Address) (i j : F),
      Hashed cs rawBytes ∧
      Address.blake3Pure rawBytes = ixAddr a ∧
      Ixon.deConstantExact rawBytes = .ok cm ∧
      Ixon.deConstant rawBytes = .ok cm ∧
      Hashed cs blkBytes ∧
      Address.blake3Pure blkBytes = ixAddr b ∧
      Ixon.deConstantExact blkBytes = .ok cb ∧
      Ixon.deConstant blkBytes = .ok cb ∧
      Bytes.RepAddressRef addrTy h' b blk ∧
      idx = .field i ∧ cidx = .field (ct.cidx.toNat : F) ∧
      ZMod.val i < 2 ^ 56 ∧ ZMod.val j < 2 ^ 56 ∧
      cm.info = .cPrj ⟨(ZMod.val i).toUInt64, (ZMod.val j).toUInt64, ixAddr b⟩ ∧
      cb.info = .muts xs ∧
      xs[ZMod.val i]? = some (.indc ind) ∧
      ind.ctors[ZMod.val j]? = some ct := by
  obtain ⟨_, rawBytes, cm, _, hhA, haA, hexA, hdeA, _, _, hres⟩ :=
    Ingress.get_ci_spec hbounded ha ev
  unfold Ingress.GetCIRawResult at hres
  cases hinfo : cm.info with
  | defn d =>
    rw [hinfo] at hres
    obtain ⟨_, hld, _, _, _, _, rfl, _, _⟩ := hres
    exact absurd (Except.ok.inj (hld.symm.trans hld_ctor))
      (defnValShape_ne_ctor d _ _ _ _ _ _ _ _ _ _ _)
  | axio _ =>
    rw [hinfo] at hres
    obtain ⟨_, hld, _, _, rfl, _⟩ := hres
    have heq := Except.ok.inj (hld.symm.trans hld_ctor); simp at heq
  | quot _ =>
    rw [hinfo] at hres
    obtain ⟨_, hld, _, _, rfl, _⟩ := hres
    have heq := Except.ok.inj (hld.symm.trans hld_ctor); simp at heq
  | recr _ =>
    rw [hinfo] at hres
    obtain ⟨_, hld, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := hres
    have heq := Except.ok.inj (hld.symm.trans hld_ctor); simp at heq
  | dPrj _ =>
    rw [hinfo] at hres
    obtain ⟨_, _, _, _, d, _, _, _, _, _, _, _, hld, _, _, _, _, rfl, _, _⟩ := hres
    exact absurd (Except.ok.inj (hld.symm.trans hld_ctor))
      (defnValShape_ne_ctor d _ _ _ _ _ _ _ _ _ _ _)
  | iPrj _ =>
    rw [hinfo] at hres
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hld, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hres
    have heq := Except.ok.inj (hld.symm.trans hld_ctor); simp at heq
  | rPrj _ =>
    rw [hinfo] at hres
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hld,
      _, _, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := hres
    have heq := Except.ok.inj (hld.symm.trans hld_ctor); simp at heq
  | muts _ =>
    rw [hinfo] at hres; exact hres.elim
  | cPrj p =>
    rw [hinfo] at hres
    obtain ⟨hidx56, hcidx56, blkBytes, cb, xs, ind, ct, _,
      hhB, haB, hexB, hdeB, hcb, hxs, hct, hld,
      -, -, -, -, -, _, _, b, hb_eq, hb_rep, rfl, -⟩ := hres
    have hv := Except.ok.inj (hld.symm.trans hld_ctor)
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
    rcases hv with ⟨-, -, -, -, hblk_eq, hidx_eq, hcidx_eq, -, -, -⟩
    subst hblk_eq
    let i : F := (p.idx.toNat : F)
    let j : F := (p.cidx.toNat : F)
    have hval_i : ZMod.val i = p.idx.toNat := val_natCast_wide_p (by omega)
    have hval_j : ZMod.val j = p.cidx.toNat := val_natCast_wide_p (by omega)
    have hu64_i : (ZMod.val i).toUInt64 = p.idx := by
      rw [hval_i]; exact UInt64.toNat_inj.mp (UInt64.toNat_ofNat_of_lt p.idx.toNat_lt)
    have hu64_j : (ZMod.val j).toUInt64 = p.cidx := by
      rw [hval_j]; exact UInt64.toNat_inj.mp (UInt64.toNat_ofNat_of_lt p.cidx.toNat_lt)
    have hp_eq : p = ⟨(ZMod.val i).toUInt64, (ZMod.val j).toUInt64, ixAddr b⟩ := by
      rcases p with ⟨pi, pj, pb⟩
      dsimp only at hu64_i hu64_j hb_eq
      rw [hu64_i, hu64_j, hb_eq]
    have hpow56 : (72057594037927936 : Nat) = 2 ^ 56 := by decide
    refine ⟨rawBytes, blkBytes, cm, cb, xs, ind, ct, b, i, j,
      hhA, haA, hexA, hdeA, hhB, ?_, hexB, hdeB, hb_rep,
      hidx_eq.symm, hcidx_eq.symm,
      by rw [hval_i, ← hpow56]; exact hidx56,
      by rw [hval_j, ← hpow56]; exact hcidx56,
      ?_, hcb, ?_, ?_⟩
    · rw [hb_eq]; exact haB
    · rw [← hp_eq]; exact hinfo
    · rw [hval_i]; simpa only [Array.getElem?_toList] using hxs
    · rw [hval_j]; simpa only [Array.getElem?_toList] using hct

/-- Helper: every entry of `Ix.Kernel.reservedBasisNames` is pinned by some `BasisKind.declsA`. -/
private theorem mem_basisKind_of_reserved {k : KKey}
    (hk : Ix.Kernel.reservedBasisNames.contains k = true) :
    ∃ (bk : Ix.Kernel.BasisKind) (ci : ConstantInfo .anon),
      ci ∈ (bk.declsA : List (ConstantInfo .anon)) ∧ ci.name = k := by
  have hmem : k ∈ (Ix.Kernel.reservedBasisNames : List KKey) := by simpa using hk
  simp only [Ix.Kernel.reservedBasisNames, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.eqK, Ix.Kernel.eqA, List.mem_cons_self, rfl⟩
  · exact ⟨.eqK, Ix.Kernel.eqReflA, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · exact ⟨.eqK, Ix.Kernel.eqRecA, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩
  · exact ⟨.natK, Ix.Kernel.natA, List.mem_cons_self, rfl⟩
  · exact ⟨.natK, Ix.Kernel.natZeroA, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · exact ⟨.natK, Ix.Kernel.natSuccA, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩
  · exact ⟨.natK, Ix.Kernel.natRecA, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), rfl⟩
  · exact ⟨.punitK, Ix.Kernel.punitA, List.mem_cons_self, rfl⟩
  · exact ⟨.punitK, Ix.Kernel.punitUnitA, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · exact ⟨.punitK, Ix.Kernel.punitRecA, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩
  · exact ⟨.emptyK, Ix.Kernel.emptyA, List.mem_cons_self, rfl⟩
  · exact ⟨.emptyK, Ix.Kernel.emptyRecA, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · exact ⟨.falseK, Ix.Kernel.falseA, List.mem_cons_self, rfl⟩
  · exact ⟨.falseK, Ix.Kernel.falseRecA, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · exact ⟨.quotK, Ix.Kernel.quotA, List.mem_cons_self, rfl⟩
  · exact ⟨.quotK, Ix.Kernel.quotMkA, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · exact ⟨.quotK, Ix.Kernel.quotLiftA, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩
  · exact ⟨.quotK, Ix.Kernel.quotIndA, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), rfl⟩
  · exact ⟨.quotK, Ix.Kernel.quotSoundA, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))), rfl⟩

/-- An inductive stored in `env` whose type strips `n ≥ 1` Pis into a never-zero sort cannot be a
reserved basis constant (`eqA` has sort `0`, while `natA`/`punitA`/`emptyA`/`falseA` have `0` Pis). -/
theorem not_reserved_ind_of_neverZero_arity {t : Ix.Kernel.RoleTable} {G : Nat → Prop}
    {R : Ixon.Env} {envT env : Ix.Kernel.Env .anon}
    (hshape : TableShape.{u} t G R envT)
    (hext : ∀ ci ∈ envT.consts, ci ∈ env.consts) (hnd : (env.consts.map (·.name)).Nodup)
    {k : KKey} {cv : ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon}
    {n : Nat} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {u : KLevel}
    (hfind : env.find? k = some (.indInfo cv caps))
    (hn : 0 < n) (hstrip : (Core.posOf cv.levelParams cv.type).stripPis n = some (bs, .sort u))
    (hpos : ∀ φ, u.eval φ > 0) :
    Ix.Kernel.reservedBasisNames.contains k = false := by
  cases h : Ix.Kernel.reservedBasisNames.contains k with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨bk, ci, hci, hname⟩ := mem_basisKind_of_reserved h
    have hfind_ci : env.find? k = some ci := by
      rw [← hname]; exact find_of_mem_nodup hnd (hext ci (hshape.pins bk ci hci))
    have heq : ConstantInfo.indInfo cv caps = ci := Option.some.inj (hfind.symm.trans hfind_ci)
    have hall : ∀ (bk' : Ix.Kernel.BasisKind) (ci' : ConstantInfo .anon),
        ci' ∈ (bk'.declsA : List (ConstantInfo .anon)) →
        match ci' with
        | .indInfo cv' _ =>
          (cv'.type.piArity = 0) ∨
          (∃ l, cv'.type.resultSort = some l ∧
            (Level.subst cv'.levelParams (Core.posLevels cv'.levelParams) l).eval (fun _ => 0) = 0)
        | _ => True := by
      intro bk' ci' hmem'
      cases bk' with
      | eqK =>
        simp only [Ix.Kernel.BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hmem'
        rcases hmem' with rfl | rfl | rfl
        · exact Or.inr ⟨.zero, rfl, rfl⟩
        · exact trivial
        · exact trivial
      | natK =>
        simp only [Ix.Kernel.BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact trivial
        · exact trivial
        · exact trivial
      | punitK =>
        simp only [Ix.Kernel.BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hmem'
        rcases hmem' with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact trivial
        · exact trivial
      | emptyK =>
        simp only [Ix.Kernel.BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hmem'
        rcases hmem' with rfl | rfl
        · exact Or.inl rfl
        · exact trivial
      | falseK =>
        simp only [Ix.Kernel.BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hmem'
        rcases hmem' with rfl | rfl
        · exact Or.inl rfl
        · exact trivial
      | quotK =>
        simp only [Ix.Kernel.BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl
        · exact Or.inr ⟨.param Ix.Kernel.uN, rfl, rfl⟩
        · exact trivial
        · exact trivial
        · exact trivial
        · exact trivial
    have hprop := hall bk ci hci
    rw [← heq] at hprop
    have hpa : cv.type.piArity = n := by
      have h1 : (Core.posOf cv.levelParams cv.type).piArity = n := by
        have aux : ∀ (m : Nat) (e : KExpr) (bs' : List (KExpr × Ix.Kernel.BinderMeta)) (l : KLevel),
            e.stripPis m = some (bs', .sort l) → e.piArity = m := by
          intro m; induction m with
          | zero =>
            intro e bs' l hs; injection hs with hp; injection hp with _ hr; subst hr; rfl
          | succ m ihm =>
            intro e bs' l hs
            cases e with
            | forallE ty b bm =>
              simp only [Expr.stripPis] at hs
              cases hsb : b.stripPis m with
              | none => simp [hsb] at hs
              | some p =>
                rcases p with ⟨bs₀, rem₀⟩
                rw [hsb] at hs; injection hs with hp; injection hp with _ hr
                dsimp only at hr; rw [hr] at hsb
                simp [Expr.piArity, ihm b bs₀ l hsb]
            | _ => nomatch hs
        exact aux n _ bs u hstrip
      have h2 : ∀ (e : KExpr) (ks : List LevelParam) (us : List KLevel),
          (e.instantiateLevelParams ks us).piArity = e.piArity := by
        intro e ks us; induction e with
        | forallE _ b _ _ ihb => simp [Expr.instantiateLevelParams, Expr.piArity, ihb]
        | _ => rfl
      rw [Core.posOf, h2] at h1; exact h1
    rcases hprop with h0 | ⟨l₀, hl₀, hev0⟩
    · omega
    · have hrs : ∀ (m : Nat) (e : KExpr) (bs' : List (KExpr × Ix.Kernel.BinderMeta)) (l : KLevel),
          e.stripPis m = some (bs', .sort l) → e.resultSort = some l := by
        intro m; induction m with
        | zero =>
          intro e bs' l hs; injection hs with hp; injection hp with _ hr; subst hr; rfl
        | succ m ihm =>
          intro e bs' l hs
          cases e with
          | forallE ty b bm =>
            simp only [Expr.stripPis] at hs
            cases hsb : b.stripPis m with
            | none => simp [hsb] at hs
            | some p =>
              rcases p with ⟨bs₀, rem₀⟩
              rw [hsb] at hs; injection hs with hp; injection hp with _ hr
              dsimp only at hr; rw [hr] at hsb
              exact ihm b bs₀ l hsb
          | _ => nomatch hs
      have hpos_rs : ∀ (e : KExpr) (ks : List LevelParam) (us : List KLevel) (l : KLevel),
          e.resultSort = some l →
          (e.instantiateLevelParams ks us).resultSort = some (Level.subst ks us l) := by
        intro e ks us l; induction e with
        | sort u0 => intro h; injection h with h; subst h; rfl
        | forallE _ b _ _ ihb => intro h; exact ihb h
        | _ => intro h; cases h
      have h1 := hrs n _ bs u hstrip
      have h2 := hpos_rs cv.type cv.levelParams (Core.posLevels cv.levelParams) l₀ hl₀
      have hu0 : u = Level.subst cv.levelParams (Core.posLevels cv.levelParams) l₀ :=
        Option.some.inj (h1.symm.trans h2)
      rw [hu0] at hpos
      have hgt := hpos (fun _ => 0)
      omega

private def quotMkIsQuotCheck (tbl : Ix.Kernel.RoleTable)
    (rows : List (_root_.Address × Ixon.Constant)) : Bool :=
  match tbl.addressOf? .quotMk with
  | none => false
  | some a =>
    match rows.find? (fun p => p.1 == a) with
    | some (_, c) => match c.info with | .quot _ => true | _ => false
    | none => false

private theorem quotMkIsQuotCheck_elim (tbl : Ix.Kernel.RoleTable)
    (rows : List (_root_.Address × Ixon.Constant)) (h : quotMkIsQuotCheck tbl rows = true) :
    ∃ a p q, tbl.addressOf? .quotMk = some a ∧ p ∈ rows ∧ p.1 = a ∧ p.2.info = .quot q := by
  unfold quotMkIsQuotCheck at h
  cases ha : tbl.addressOf? .quotMk with
  | none => rw [ha] at h; cases h
  | some a =>
    rw [ha] at h; dsimp only at h
    cases hf : rows.find? (fun p => p.1 == a) with
    | none => rw [hf] at h; cases h
    | some p =>
      rw [hf] at h; dsimp only at h
      have hmem := List.mem_of_find?_eq_some hf
      have haddr : p.1 = a := beq_iff_eq.mp (by simpa using List.find?_some hf)
      cases hi : p.2.info with
      | quot q => exact ⟨a, p, q, rfl, hmem, haddr, hi⟩
      | defn _ | axio _ | recr _ | dPrj _ | iPrj _ | cPrj _ | rPrj _ | muts _ =>
        rw [hi] at h; cases h

set_option maxRecDepth 100000 in
private theorem quotMkIsQuotCheck_ok :
    quotMkIsQuotCheck RoleVal.committedDefaultRoleTable RoleVal.committedPreludeList = true := by
  decide +kernel

/-- A constructor stored in `env` with `nP > 0` whose record is a `.cPrj` is either `Eq.refl`
(`nF = 0`) or not a reserved basis name (`Quot.mk` has a `.quot` record, not `.cPrj`). -/
theorem not_reserved_ctor_of_nP_pos_or_eqRefl {t : Ix.Kernel.RoleTable} {G : Nat → Prop}
    {R E : Ixon.Env} {envT env : Ix.Kernel.Env .anon}
    (htwf : t.wf = true) (hshape : TableShape.{u} t G R envT)
    (hPre : ∀ e ∈ RoleVal.committedPreludeList, Ix.Cert.recordAt E e.1 = some e.2)
    (hext : ∀ ci ∈ envT.consts, ci ∈ env.consts) (hnd : (env.consts.map (·.name)).Nodup)
    {C : _root_.Address} {cm : Ixon.Constant} {cp : Ixon.ConstructorProj}
    {cv : ConstantVal .anon} {nP nF : Nat}
    (hrecC : Ix.Cert.recordAt E C = some cm) (hinfoC : cm.info = .cPrj cp)
    (hfind : env.find? (Core.keyOf t C) = some (.ctorInfo cv nP nF)) (hnP : 0 < nP) :
    (Core.keyOf t C = Ix.Kernel.eqReflName ∧ nF = 0) ∨
      Ix.Kernel.reservedBasisNames.contains (Core.keyOf t C) = false := by
  cases h : Ix.Kernel.reservedBasisNames.contains (Core.keyOf t C) with
  | false => exact Or.inr rfl
  | true =>
    obtain ⟨bk, ci, hci, hname⟩ := mem_basisKind_of_reserved h
    have hfind_ci : env.find? (Core.keyOf t C) = some ci := by
      rw [← hname]; exact find_of_mem_nodup hnd (hext ci (hshape.pins bk ci hci))
    have heq : ConstantInfo.ctorInfo cv nP nF = ci := Option.some.inj (hfind.symm.trans hfind_ci)
    have hall : ∀ (bk' : Ix.Kernel.BasisKind) (ci' : ConstantInfo .anon),
        ci' ∈ (bk'.declsA : List (ConstantInfo .anon)) →
        match ci' with
        | .ctorInfo cv' nP' nF' =>
          nP' = 0 ∨ (cv'.name = Ix.Kernel.eqReflName ∧ nF' = 0) ∨ cv'.name = Ix.Kernel.quotMkName
        | _ => True := by
      intro bk' ci' hmem'
      cases bk' with
      | eqK =>
        simp only [Ix.Kernel.BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hmem'
        rcases hmem' with rfl | rfl | rfl
        · exact trivial
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact trivial
      | natK =>
        simp only [Ix.Kernel.BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl
        · exact trivial
        · exact Or.inl rfl
        · exact Or.inl rfl
        · exact trivial
      | punitK =>
        simp only [Ix.Kernel.BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hmem'
        rcases hmem' with rfl | rfl | rfl
        · exact trivial
        · exact Or.inl rfl
        · exact trivial
      | emptyK =>
        simp only [Ix.Kernel.BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hmem'
        rcases hmem' with rfl | rfl <;> exact trivial
      | falseK =>
        simp only [Ix.Kernel.BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hmem'
        rcases hmem' with rfl | rfl <;> exact trivial
      | quotK =>
        simp only [Ix.Kernel.BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl
        · exact trivial
        · exact Or.inr (Or.inr rfl)
        · exact trivial
        · exact trivial
        · exact trivial
    have hprop := hall bk ci hci
    rw [← heq] at hprop
    have hkname : cv.name = Core.keyOf t C := Ix.Kernel.Semantics.Env.find?_name hfind
    rcases hprop with h0 | ⟨heqR, hnf0⟩ | hqmk
    · omega
    · exact Or.inl ⟨hkname.symm.trans heqR, hnf0⟩
    · exfalso
      have hk_qmk : Core.keyOf t C = Ix.Kernel.quotMkName := hkname.symm.trans hqmk
      have ha_t : t.addressOf? .quotMk = some C := Core.addressOf_of_keyOf htwf hk_qmk
      obtain ⟨b₀, t₀, hdef₀, hadm₀, hpre₀⟩ := hshape.prelude
      have ht₀ : t₀ = RoleVal.committedDefaultRoleTable :=
        RoleVal.admitBinding_committedDefault hdef₀ hadm₀
      subst ht₀
      have hdef : RoleVal.committedDefaultRoleTable.addressOf? .quotMk = some C :=
        (hpre₀ .quotMk (by decide)).symm.trans ha_t
      obtain ⟨a, p, q, ha, hpmem, hpaddr, hpinfo⟩ :=
        quotMkIsQuotCheck_elim _ _ quotMkIsQuotCheck_ok
      have haC : a = C := Option.some.inj (ha.symm.trans hdef)
      subst haC
      have hrecP : Ix.Cert.recordAt E a = some p.2 := by rw [← hpaddr]; exact hPre p hpmem
      have hcm_eq : cm = p.2 := Option.some.inj (hrecC.symm.trans hrecP)
      rw [← hcm_eq, hinfoC] at hpinfo; cases hpinfo

private def preludeBlockLe1 (rows : List (_root_.Address × Ixon.Constant))
    (blk : _root_.Address) (idx : Nat) : Bool :=
  match rows.find? (fun p => p.1 == blk) with
  | some (_, cb) =>
    match cb.info with
    | .muts ms =>
      match ms[idx]? with
      | some (.indc ind) => decide (ind.ctors.size ≤ 1)
      | _ => false
    | _ => false
  | none => false

private def preludeEntryOk (rows : List (_root_.Address × Ixon.Constant))
    (r : Ix.Kernel.Role) (c : Ixon.Constant) : Bool :=
  match c.info with
  | .iPrj ip => (r == .nat) || preludeBlockLe1 rows ip.block ip.idx.toNat
  | .cPrj cp => (r == .natZero || r == .natSucc) || preludeBlockLe1 rows cp.block cp.idx.toNat
  | _ => true

private def reservedPreludeCheck (tbl : Ix.Kernel.RoleTable)
    (rows : List (_root_.Address × Ixon.Constant)) : Ix.Kernel.Key .anon → Bool
  | .role r =>
    decide (r ∈ preludeRoles) &&
    match tbl.addressOf? r with
    | none => false
    | some a =>
      match rows.find? (fun p => p.1 == a) with
      | none => false
      | some (_, c) => preludeEntryOk rows r c
  | _ => false

private def natCtorBlockCheck (tbl : Ix.Kernel.RoleTable)
    (rows : List (_root_.Address × Ixon.Constant)) : Bool :=
  match tbl.addressOf? .nat with
  | none => false
  | some aNat =>
    match tbl.addressOf? .natZero with
    | none => false
    | some aZ =>
      match tbl.addressOf? .natSucc with
      | none => false
      | some aS =>
        match rows.find? (fun p => p.1 == aNat) with
        | none => false
        | some (_, cNat) =>
          match rows.find? (fun p => p.1 == aZ) with
          | none => false
          | some (_, cZ) =>
            match rows.find? (fun p => p.1 == aS) with
            | none => false
            | some (_, cS) =>
              match cNat.info with
              | .iPrj ipN =>
                match cZ.info with
                | .cPrj cpZ =>
                  match cS.info with
                  | .cPrj cpS =>
                    ipN.idx == 0 && cpZ.block == ipN.block && cpS.block == ipN.block &&
                    cNat.sharing.isEmpty && cNat.refs.isEmpty && cNat.univs.isEmpty && cNat.binders.isEmpty
                  | _ => false
                | _ => false
              | _ => false

set_option maxRecDepth 100000 in
private theorem reservedBasisNames_prelude_ok :
    (Ix.Kernel.reservedBasisNames : List KKey).all
      (reservedPreludeCheck RoleVal.committedDefaultRoleTable RoleVal.committedPreludeList) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem natCtorBlockCheck_ok :
    natCtorBlockCheck RoleVal.committedDefaultRoleTable RoleVal.committedPreludeList = true := by
  decide +kernel

private theorem preludeBlockLe1_elim (rows : List (_root_.Address × Ixon.Constant))
    {blk : _root_.Address} {idx : Nat} (h : preludeBlockLe1 rows blk idx = true) :
    ∃ q ms ind, q ∈ rows ∧ q.1 = blk ∧ q.2.info = .muts ms ∧
      ms[idx]? = some (.indc ind) ∧ ind.ctors.size ≤ 1 := by
  unfold preludeBlockLe1 at h
  cases hf : rows.find? (fun p => p.1 == blk) with
  | none => rw [hf] at h; cases h
  | some q =>
    rw [hf] at h; dsimp only at h
    have hmem := List.mem_of_find?_eq_some hf
    have haddr : q.1 = blk := beq_iff_eq.mp (by simpa using List.find?_some hf)
    cases hi : q.2.info with
    | muts ms =>
      rw [hi] at h; dsimp only at h
      cases hm : ms[idx]? with
      | none => rw [hm] at h; cases h
      | some mc =>
        rw [hm] at h
        cases mc with
        | indc ind => exact ⟨q, ms, ind, hmem, haddr, hi, hm, decide_eq_true_eq.mp h⟩
        | defn _ | recr _ => cases h
    | defn _ | axio _ | quot _ | recr _ | dPrj _ | iPrj _ | cPrj _ | rPrj _ =>
      rw [hi] at h; cases h

private theorem reservedPreludeCheck_elim (tbl : Ix.Kernel.RoleTable)
    (rows : List (_root_.Address × Ixon.Constant)) {r : Ix.Kernel.Role}
    (h : reservedPreludeCheck tbl rows (.role r) = true) :
    r ∈ preludeRoles ∧
    ∃ a p, tbl.addressOf? r = some a ∧ p ∈ rows ∧ p.1 = a ∧ preludeEntryOk rows r p.2 = true := by
  unfold reservedPreludeCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hr, h2⟩ := h
  cases ha : tbl.addressOf? r with
  | none => rw [ha] at h2; cases h2
  | some a =>
    rw [ha] at h2; dsimp only at h2
    cases hf : rows.find? (fun p => p.1 == a) with
    | none => rw [hf] at h2; cases h2
    | some p =>
      rw [hf] at h2; dsimp only at h2
      have haddr : p.1 = a := beq_iff_eq.mp (by simpa using List.find?_some hf)
      exact ⟨hr, a, p, rfl, List.mem_of_find?_eq_some hf, haddr, h2⟩

private theorem natCtorBlockCheck_elim (tbl : Ix.Kernel.RoleTable)
    (rows : List (_root_.Address × Ixon.Constant)) (h : natCtorBlockCheck tbl rows = true) :
    ∃ aNat aZ aS qN qZ qS ipN cpZ cpS,
      tbl.addressOf? .nat = some aNat ∧ tbl.addressOf? .natZero = some aZ ∧
      tbl.addressOf? .natSucc = some aS ∧
      qN ∈ rows ∧ qN.1 = aNat ∧ qZ ∈ rows ∧ qZ.1 = aZ ∧ qS ∈ rows ∧ qS.1 = aS ∧
      qN.2.info = .iPrj ipN ∧ qZ.2.info = .cPrj cpZ ∧ qS.2.info = .cPrj cpS ∧
      ipN.idx = 0 ∧ cpZ.block = ipN.block ∧ cpS.block = ipN.block ∧
      qN.2.sharing.isEmpty = true ∧ qN.2.refs.isEmpty = true ∧
      qN.2.univs.isEmpty = true ∧ qN.2.binders.isEmpty = true := by
  unfold natCtorBlockCheck at h
  cases hn : tbl.addressOf? .nat with
  | none => rw [hn] at h; cases h
  | some aNat =>
    rw [hn] at h; dsimp only at h
    cases hz : tbl.addressOf? .natZero with
    | none => rw [hz] at h; cases h
    | some aZ =>
      rw [hz] at h; dsimp only at h
      cases hs : tbl.addressOf? .natSucc with
      | none => rw [hs] at h; cases h
      | some aS =>
        rw [hs] at h; dsimp only at h
        cases hfn : rows.find? (fun p => p.1 == aNat) with
        | none => rw [hfn] at h; cases h
        | some qN =>
          rw [hfn] at h; dsimp only at h
          cases hfz : rows.find? (fun p => p.1 == aZ) with
          | none => rw [hfz] at h; cases h
          | some qZ =>
            rw [hfz] at h; dsimp only at h
            cases hfs : rows.find? (fun p => p.1 == aS) with
            | none => rw [hfs] at h; cases h
            | some qS =>
              rw [hfs] at h; dsimp only at h
              have hN1 : qN.1 = aNat := beq_iff_eq.mp (by simpa using List.find?_some hfn)
              have hZ1 : qZ.1 = aZ := beq_iff_eq.mp (by simpa using List.find?_some hfz)
              have hS1 : qS.1 = aS := beq_iff_eq.mp (by simpa using List.find?_some hfs)
              cases hiN : qN.2.info with
              | iPrj ipN =>
                rw [hiN] at h; dsimp only at h
                cases hiZ : qZ.2.info with
                | cPrj cpZ =>
                  rw [hiZ] at h; dsimp only at h
                  cases hiS : qS.2.info with
                  | cPrj cpS =>
                    rw [hiS] at h; dsimp only at h
                    simp only [Bool.and_eq_true, beq_iff_eq] at h
                    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
                    exact ⟨aNat, aZ, aS, qN, qZ, qS, ipN, cpZ, cpS, rfl, rfl, rfl,
                      List.mem_of_find?_eq_some hfn, hN1,
                      List.mem_of_find?_eq_some hfz, hZ1,
                      List.mem_of_find?_eq_some hfs, hS1,
                      hiN, hiZ, hiS, h1, h2, h3, h4, h5, h6, h7⟩
                  | defn _ | axio _ | quot _ | recr _ | dPrj _ | iPrj _ | rPrj _ | muts _ =>
                    rw [hiS] at h; cases h
                | defn _ | axio _ | quot _ | recr _ | dPrj _ | iPrj _ | rPrj _ | muts _ =>
                  rw [hiZ] at h; cases h
              | defn _ | axio _ | quot _ | recr _ | dPrj _ | cPrj _ | rPrj _ | muts _ =>
                rw [hiN] at h; cases h

private theorem preludeEntryOk_iPrj (rows : List (_root_.Address × Ixon.Constant))
    {r : Ix.Kernel.Role} {c : Ixon.Constant} {ip : Ixon.InductiveProj}
    (h : preludeEntryOk rows r c = true) (hi : c.info = .iPrj ip) :
    r = .nat ∨ preludeBlockLe1 rows ip.block ip.idx.toNat = true := by
  unfold preludeEntryOk at h; rw [hi] at h; dsimp only at h
  rcases Bool.or_eq_true _ _ |>.mp h with h1 | h2
  · exact Or.inl (beq_iff_eq.mp h1)
  · exact Or.inr h2

private theorem preludeEntryOk_cPrj (rows : List (_root_.Address × Ixon.Constant))
    {r : Ix.Kernel.Role} {c : Ixon.Constant} {cp : Ixon.ConstructorProj}
    (h : preludeEntryOk rows r c = true) (hi : c.info = .cPrj cp) :
    (r = .natZero ∨ r = .natSucc) ∨ preludeBlockLe1 rows cp.block cp.idx.toNat = true := by
  unfold preludeEntryOk at h; rw [hi] at h; dsimp only at h
  rcases Bool.or_eq_true _ _ |>.mp h with h1 | h2
  · rcases Bool.or_eq_true _ _ |>.mp h1 with h1a | h1b
    · exact Or.inl (Or.inl (beq_iff_eq.mp h1a))
    · exact Or.inl (Or.inr (beq_iff_eq.mp h1b))
  · exact Or.inr h2

private theorem preludeBlockLe1_false_of_gt1 {E : Ixon.Env}
    (rows : List (_root_.Address × Ixon.Constant))
    (hPre : ∀ e ∈ rows, Ix.Cert.recordAt E e.1 = some e.2)
    {tagBlk : _root_.Address} {idx : Nat} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {ind : Ixon.Inductive}
    (hrecB : Ix.Cert.recordAt E tagBlk = some cb) (hmuts : cb.info = .muts ms)
    (hms0 : ms[idx]? = some (.indc ind)) (hnc : 1 < ind.ctors.size)
    (hle1 : preludeBlockLe1 rows tagBlk idx = true) : False := by
  obtain ⟨q, ms', ind', hq_mem, hq_addr, hq_muts, hq_ms0, hle⟩ := preludeBlockLe1_elim rows hle1
  have hrecQ : Ix.Cert.recordAt E tagBlk = some q.2 := by rw [← hq_addr]; exact hPre q hq_mem
  have hcb_eq : cb = q.2 := Option.some.inj (hrecB.symm.trans hrecQ)
  rw [← hcb_eq, hmuts] at hq_muts
  obtain rfl := Ixon.ConstantInfo.muts.inj hq_muts
  rw [hms0] at hq_ms0
  obtain rfl := Ixon.MutConst.indc.inj (Option.some.inj hq_ms0)
  omega

private theorem not_reserved_tag_ind_aux (tbl : Ix.Kernel.RoleTable)
    (rows : List (_root_.Address × Ixon.Constant))
    (hcheck : (Ix.Kernel.reservedBasisNames : List KKey).all (reservedPreludeCheck tbl rows) = true)
    {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    (htwf : t.wf = true)
    (hpin : ∀ r ∈ preludeRoles, t.addressOf? r = tbl.addressOf? r)
    (hPre : ∀ e ∈ rows, Ix.Cert.recordAt E e.1 = some e.2)
    {tagBlk addrI : _root_.Address} {cb cm : Ixon.Constant} {ms : Array Ixon.MutConst}
    {ind : Ixon.Inductive}
    (hrecB : Ix.Cert.recordAt E tagBlk = some cb) (hmuts : cb.info = .muts ms)
    (hms0 : ms[0]? = some (.indc ind)) (hnc : 1 < ind.ctors.size)
    (hneNat : Core.keyOf t addrI ≠ Ix.Kernel.natName)
    (hrecI : Ix.Cert.recordAt E addrI = some cm)
    (hinfoI : cm.info = .iPrj ⟨0, tagBlk⟩) :
    Ix.Kernel.reservedBasisNames.contains (Core.keyOf t addrI) = false := by
  cases h : Ix.Kernel.reservedBasisNames.contains (Core.keyOf t addrI) with
  | false => rfl
  | true =>
    exfalso
    have hok := List.all_eq_true.mp hcheck _ (by simpa using h)
    cases hk : Core.keyOf t addrI with
    | id _ | aux _ _ => rw [hk] at hok; cases hok
    | role r =>
      rw [hk] at hok hneNat
      obtain ⟨hr_pre, a, p, ha_def, hp_mem, hp_addr, hentry⟩ := reservedPreludeCheck_elim tbl rows hok
      have ha_t : t.addressOf? r = some addrI := Core.addressOf_of_keyOf htwf hk
      have hdef : tbl.addressOf? r = some addrI := (hpin r hr_pre).symm.trans ha_t
      have ha_eq : a = addrI := Option.some.inj (ha_def.symm.trans hdef)
      have hrecP : Ix.Cert.recordAt E addrI = some p.2 := by
        rw [← ha_eq, ← hp_addr]; exact hPre p hp_mem
      have hcm_eq : cm = p.2 := Option.some.inj (hrecI.symm.trans hrecP)
      rcases preludeEntryOk_iPrj rows hentry (by rw [← hcm_eq]; exact hinfoI) with hrnat | hle1
      · exact hneNat (congrArg Ix.Kernel.Key.role hrnat)
      · exact preludeBlockLe1_false_of_gt1 rows hPre hrecB hmuts (by simpa using hms0) hnc hle1

/-- Neither a tag inductive (at `(tag_blk, 0)` with `tlnc > 1` and `≠ natName`) nor any of its
constructors (`cPrj ⟨0, cidx, tag_blk⟩`) can be a reserved basis constant. -/
theorem not_reserved_tag_ind {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {E : Ixon.Env}
    (htwf : t.wf = true) (hshape : TableShape.{u} t G R envT)
    (hPre : ∀ e ∈ RoleVal.committedPreludeList, Ix.Cert.recordAt E e.1 = some e.2)
    {tagBlk : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {ind : Ixon.Inductive}
    (hrecB : Ix.Cert.recordAt E tagBlk = some cb) (hmuts : cb.info = .muts ms)
    (hms0 : ms[0]? = some (.indc ind)) (hnc : 1 < ind.ctors.size)
    (hneNat : Core.keyOf t (Core.iprjAddr tagBlk 0) ≠ Ix.Kernel.natName)
    {cm : Ixon.Constant} (hrecI : Ix.Cert.recordAt E (Core.iprjAddr tagBlk 0) = some cm)
    (hinfoI : cm.info = .iPrj ⟨0, tagBlk⟩) :
    Ix.Kernel.reservedBasisNames.contains (Core.keyOf t (Core.iprjAddr tagBlk 0)) = false := by
  obtain ⟨b₀, t₀, hdef₀, hadm₀, hpre₀⟩ := hshape.prelude
  have ht₀ : t₀ = RoleVal.committedDefaultRoleTable :=
    RoleVal.admitBinding_committedDefault hdef₀ hadm₀
  have hpin : ∀ r ∈ preludeRoles, t.addressOf? r = RoleVal.committedDefaultRoleTable.addressOf? r :=
    fun r hr => by rw [← ht₀]; exact hpre₀ r hr
  exact not_reserved_tag_ind_aux RoleVal.committedDefaultRoleTable RoleVal.committedPreludeList
    reservedBasisNames_prelude_ok htwf hpin hPre hrecB hmuts hms0 hnc hneNat hrecI hinfoI

private theorem not_reserved_tag_ctor_aux (tbl : Ix.Kernel.RoleTable)
    (rows : List (_root_.Address × Ixon.Constant))
    (hcheck : (Ix.Kernel.reservedBasisNames : List KKey).all (reservedPreludeCheck tbl rows) = true)
    (hnatChk : natCtorBlockCheck tbl rows = true)
    (hhash : ∀ q ∈ rows, Address.blake3Pure (Ixon.serConstant q.2) = q.1)
    {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    (htwf : t.wf = true)
    (hpin : ∀ r ∈ preludeRoles, t.addressOf? r = tbl.addressOf? r)
    (hPre : ∀ e ∈ rows, Ix.Cert.recordAt E e.1 = some e.2)
    {tagBlk C : _root_.Address} {cb cm : Ixon.Constant} {ms : Array Ixon.MutConst}
    {ind : Ixon.Inductive} {cidx : UInt64}
    (hrecB : Ix.Cert.recordAt E tagBlk = some cb) (hmuts : cb.info = .muts ms)
    (hms0 : ms[0]? = some (.indc ind)) (hnc : 1 < ind.ctors.size)
    (hneNat : Core.keyOf t (Core.iprjAddr tagBlk 0) ≠ Ix.Kernel.natName)
    (hrecC : Ix.Cert.recordAt E C = some cm) (hinfoC : cm.info = .cPrj ⟨0, cidx, tagBlk⟩) :
    Ix.Kernel.reservedBasisNames.contains (Core.keyOf t C) = false := by
  cases h : Ix.Kernel.reservedBasisNames.contains (Core.keyOf t C) with
  | false => rfl
  | true =>
    exfalso
    have hok := List.all_eq_true.mp hcheck _ (by simpa using h)
    cases hk : Core.keyOf t C with
    | id _ | aux _ _ => rw [hk] at hok; cases hok
    | role r =>
      rw [hk] at hok
      obtain ⟨hr_pre, a, p, ha_def, hp_mem, hp_addr, hentry⟩ := reservedPreludeCheck_elim tbl rows hok
      have ha_t : t.addressOf? r = some C := Core.addressOf_of_keyOf htwf hk
      have hdef : tbl.addressOf? r = some C := (hpin r hr_pre).symm.trans ha_t
      have ha_eq : a = C := Option.some.inj (ha_def.symm.trans hdef)
      have hrecP : Ix.Cert.recordAt E C = some p.2 := by
        rw [← ha_eq, ← hp_addr]; exact hPre p hp_mem
      have hcm_eq : cm = p.2 := Option.some.inj (hrecC.symm.trans hrecP)
      rcases preludeEntryOk_cPrj rows hentry (by rw [← hcm_eq]; exact hinfoC) with hnatC | hle1
      · obtain ⟨aNat, aZ, aS, qN, qZ, qS, ipN, cpZ, cpS,
          hdn, hdz, hds, hqN_mem, hqN_addr, hqZ_mem, hqZ_addr, hqS_mem, hqS_addr,
          hqN_info, hqZ_info, hqS_info, hipN_idx, hcpZ_blk, hcpS_blk,
          hsh, hrf, huv, hnh⟩ := natCtorBlockCheck_elim tbl rows hnatChk
        have htaNat : t.addressOf? .nat = some aNat := (hpin .nat (by decide)).trans hdn
        have hnatKey : Core.keyOf t aNat = Ix.Kernel.natName :=
          Core.keyOf_of_addressOf htwf htaNat
        have hqN_hash : Address.blake3Pure (Ixon.serConstant qN.2) = aNat := by
          rw [← hqN_addr]; exact hhash qN hqN_mem
        have hblk_eq : ipN.block = tagBlk := by
          rcases hnatC with rfl | rfl
          · have hCZ : aZ = C := Option.some.inj (hdz.symm.trans hdef)
            have hrecZ : Ix.Cert.recordAt E C = some qZ.2 := by
              rw [← hCZ, ← hqZ_addr]; exact hPre qZ hqZ_mem
            have hcmZ : cm = qZ.2 := Option.some.inj (hrecC.symm.trans hrecZ)
            rw [← hcmZ, hinfoC] at hqZ_info
            obtain rfl := Ixon.ConstantInfo.cPrj.inj hqZ_info
            exact hcpZ_blk.symm
          · have hCS : aS = C := Option.some.inj (hds.symm.trans hdef)
            have hrecS : Ix.Cert.recordAt E C = some qS.2 := by
              rw [← hCS, ← hqS_addr]; exact hPre qS hqS_mem
            have hcmS : cm = qS.2 := Option.some.inj (hrecC.symm.trans hrecS)
            rw [← hcmS, hinfoC] at hqS_info
            obtain rfl := Ixon.ConstantInfo.cPrj.inj hqS_info
            exact hcpS_blk.symm
        have hqN_eq : qN.2 = ⟨.iPrj ⟨(0 : Nat).toUInt64, tagBlk⟩, #[], #[], #[], #[]⟩ := by
          rcases qN with ⟨_, ⟨info', sh', rf', uv', nh'⟩⟩
          dsimp only at hqN_info hsh hrf huv hnh
          rcases ipN with ⟨ii, ib⟩; dsimp only at hipN_idx hblk_eq; subst hipN_idx hblk_eq
          rw [hqN_info, Array.isEmpty_iff.mp hsh, Array.isEmpty_iff.mp hrf,
            Array.isEmpty_iff.mp huv, Array.isEmpty_iff.mp hnh]; rfl
        have haN_eq : Core.iprjAddr tagBlk 0 = aNat :=
          (congrArg (fun c => Address.blake3Pure (Ixon.serConstant c)) hqN_eq.symm).trans hqN_hash
        rw [haN_eq] at hneNat; exact hneNat hnatKey
      · exact preludeBlockLe1_false_of_gt1 rows hPre hrecB hmuts (by simpa using hms0) hnc hle1

theorem not_reserved_tag_ctor {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {E : Ixon.Env}
    (htwf : t.wf = true) (hshape : TableShape.{u} t G R envT)
    (hPre : ∀ e ∈ RoleVal.committedPreludeList, Ix.Cert.recordAt E e.1 = some e.2)
    {tagBlk C : _root_.Address} {cb cm : Ixon.Constant} {ms : Array Ixon.MutConst}
    {ind : Ixon.Inductive} {cidx : UInt64}
    (hrecB : Ix.Cert.recordAt E tagBlk = some cb) (hmuts : cb.info = .muts ms)
    (hms0 : ms[0]? = some (.indc ind)) (hnc : 1 < ind.ctors.size)
    (hneNat : Core.keyOf t (Core.iprjAddr tagBlk 0) ≠ Ix.Kernel.natName)
    (hrecC : Ix.Cert.recordAt E C = some cm) (hinfoC : cm.info = .cPrj ⟨0, cidx, tagBlk⟩) :
    Ix.Kernel.reservedBasisNames.contains (Core.keyOf t C) = false := by
  obtain ⟨b₀, t₀, hdef₀, hadm₀, hpre₀⟩ := hshape.prelude
  have ht₀ : t₀ = RoleVal.committedDefaultRoleTable :=
    RoleVal.admitBinding_committedDefault hdef₀ hadm₀
  have hpin : ∀ r ∈ preludeRoles, t.addressOf? r = RoleVal.committedDefaultRoleTable.addressOf? r :=
    fun r hr => by rw [← ht₀]; exact hpre₀ r hr
  have hhash : ∀ q ∈ RoleVal.committedPreludeList,
      Address.blake3Pure (Ixon.serConstant q.2) = q.1 :=
    fun q hq => ClosedFacts.committedRows_hashed (q.1, Ixon.serConstant q.2)
      (ClosedFacts.committedPrelude_rows q hq).1
  exact not_reserved_tag_ctor_aux RoleVal.committedDefaultRoleTable RoleVal.committedPreludeList
    reservedBasisNames_prelude_ok natCtorBlockCheck_ok hhash htwf hpin hPre hrecB hmuts hms0 hnc
    hneNat hrecC hinfoC


end IxVM.Refinement.Typing.FamilyAlias
