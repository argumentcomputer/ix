import IxVMRefinement.Decl.ModeledTele
import IxVMRefinement.Decl.ModeledSound
import IxVMRefinement.Decl.Value
import IxVMRefinement.L1.ByteStream
import IxVMRefinement.L1.Stream
import IxVMRefinement.Core.Specs.Callees
import IxVMRefinement.Obs.KernelClaim
/-! # Modeled Recursor Rule Verification (`check_iota_rule`, `check_rules_go`, `check_rules`)

The direct inversion of `check_iota_rule` and the refinements of the rule loops are parked
(`Parked/IxVMRefinement/Decl/ModeledRules.lean`, outside every library): the program now types
the rules on their renaming to the model. What stays: the helpers and the rule records
(`RawIotaRuleVmRun`, `RawIotaRulesVmRun`) other modules use.

Refinement of `IxonDeserialize::get_address`, `KernelModeled::check_iota_rule` (via direct
expression-level inversion over `ObsFn`), `KernelModeled::check_rules_go`, and
`KernelModeled::check_rules` against `IotaRulesVmRunJ posRulesJ` and `IxVM.Consistency.RuleStored`.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open Ix.Kernel (ConstantInfo ConstantVal Declaration RecRule RecRuleFire LevelParam Level Expr
  auxKey eqName eqA isEqHead recRuleBits openPisAtFvars)
open Ix.Kernel.Rules (Annot Infer DefEq Red)
open Ix.Kernel.Semantics (Judgements DefEqListJ TypedListJ IotaRuleRunJ IotaRulesRunJ)
open Ix.Kernel.Model (rulesJ)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Subcall containment helpers -/

/-- Sublist membership relation keeping parent call lists unexpanded during long sequential
inversions. -/
def SubCalls (cs sub : List (Call F)) : Prop :=
  ∀ x ∈ sub, x ∈ cs

theorem SubCalls.refl (cs : List (Call F)) : SubCalls cs cs :=
  fun _ hx => hx

theorem SubCalls.trans {a b c : List (Call F)} (h₁ : SubCalls a b) (h₂ : SubCalls b c) :
    SubCalls a c :=
  fun x hx => h₁ x (h₂ x hx)

theorem SubCalls.append_left {cs c₁ c₂ : List (Call F)} (h : SubCalls cs (c₁ ++ c₂)) :
    SubCalls cs c₁ :=
  fun x hx => h x (List.mem_append_left _ hx)

theorem SubCalls.append_right {cs c₁ c₂ : List (Call F)} (h : SubCalls cs (c₁ ++ c₂)) :
    SubCalls cs c₂ :=
  fun x hx => h x (List.mem_append_right _ hx)

theorem SubCalls.cons_head {cs : List (Call F)} {hd : Call F} {tl : List (Call F)}
    (h : SubCalls cs (hd :: tl)) : hd ∈ cs :=
  h hd (List.mem_cons_self ..)

theorem SubCalls.cons_tail {cs : List (Call F)} {hd : Call F} {tl : List (Call F)}
    (h : SubCalls cs (hd :: tl)) : SubCalls cs tl :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

/-! ## Exact loader, callees, and `Eq` role-address companions -/

/-- Universal soundness of the `Specs.Callees` specification family (`projection_addr_ctor`,
`check_recursor_canonical_at`, etc.) under `CoreFacts c`. -/
def CalleesSpec : Prop :=
  ∀ (c : Ctx), CoreFacts c →
    ∀ (f : Specs.Callees.Fn) (args : List (SourceValue F))
      (h : Heap F) (r : SourceValue F) (h' : Heap F) (calls : List (Call F)),
      ObsFn W f.name args h r h' calls → f.spec (ScopedCtx.unrestricted c) args h r h' calls

/-- Callee specifications at an actual selected-call context. -/
def ScopedCalleesSpec : Prop :=
  ∀ (c : ScopedCtx), ScopedCoreFacts c →
    ∀ (f : Specs.Callees.Fn) (args : List (SourceValue F))
      (h : Heap F) (r : SourceValue F) (h' : Heap F) (calls : List (Call F)),
      ObsFn W f.name args h r h' calls → f.spec c args h r h' calls

/-- Strengthening of `LoadFacts.getCI` for non-recursor/non-quotient records yielding
`CIPtrRepExact` (exact `RepKLevel` / `RepKLevelList` on freshly loaded constant records, before
level reduction), plus canonical `.range` level parameters on theorem records. -/
def ExactGetCI (c : Ctx) : Prop :=
  ∀ (a : Bytes.Address) (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs →
    Good c cs →
    Bytes.RepAddressRef addrTy h a addr →
    (∀ tag xs, (tag = "Rec" ∨ tag = "Quot") → loadValue h' ptr ≠ .ok (.construct kciEnum tag xs)) →
    ∃ ci, c.env.find? (c.κ (ixAddr a)) = some ci ∧
      (isNonRecInfo ci = true → ci.toConstantVal.levelParams = List.range ci.toConstantVal.levelParams.length) ∧
      (∀ cv v, ci = .thmInfo cv v → cv.levelParams = List.range cv.levelParams.length) ∧
      CIPtrRepExact c.κ h' ptr ci

theorem ExactGetCI.mono_envExt {c : Ctx} {env' : Ix.Kernel.Env .anon}
    (hext : ∀ k ci, c.env.find? k = some ci → env'.find? k = some ci)
    (hget : ExactGetCI c) :
    ExactGetCI { c with env := env' } := by
  intro a addr ptr h h' cs ev hgood hadr hnot
  obtain ⟨ci, hfind, hnr, hthm, hrep⟩ := hget a addr ptr h h' cs ev hgood hadr hnot
  exact ⟨ci, hext _ _ hfind, hnr, hthm, hrep⟩

theorem not_rec_or_quot_of_load {h : Heap F} {ptr : SourceValue F} {tag₀ : String} {xs₀ : List (SourceValue F)}
    (hld : loadValue h ptr = .ok (.construct kciEnum tag₀ xs₀))
    (hne_rec : tag₀ ≠ "Rec") (hne_quot : tag₀ ≠ "Quot") :
    ∀ tag xs, (tag = "Rec" ∨ tag = "Quot") → loadValue h ptr ≠ .ok (.construct kciEnum tag xs) := by
  rintro tag xs (rfl | rfl) hld' <;> rw [hld] at hld' <;> injection hld' with h1 <;> injection h1 with _ htag _
  · exact hne_rec htag
  · exact hne_quot htag

/-- Convert `RulesRepExact` to `RepList krrListEnum` for generic `Lists::length` reasoning. -/
private theorem rulesRepExact_to_repList {κ : _root_.Address → KKey} {h : Heap F}
    {ps : List LevelParam} :
    ∀ {j : Nat} {p : SourceValue F} {rls : List (RecRule .anon)},
      RulesRepExact κ h ps j p rls →
      RepList krrListEnum (fun _ _ _ => True) h rls p
  | _, _, [], .nil cell => .nil cell
  | _, _, _ :: _, .cons cell _ rs => .cons cell trivial (rulesRepExact_to_repList rs)

/-- `Lists::length<KernelTypes::KRecRule>` on a `RulesRepExact` list returns `(rls.length : F)`
and bounds `rls.length < 2 ^ 39` under `Bounded`. -/
theorem rulesRepExact_length {κ : _root_.Address → KKey} {h h' : Heap F} {ps : List LevelParam}
    {j : Nat} {p r : SourceValue F} {rls : List (RecRule .anon)}
    {calls cs : List (Call F)}
    (bd : IxVM.Consistency.Bounded calls)
    (hcall : (⟨Obs.Names.«Lists::length<KernelTypes::KRecRule>», [p], h⟩ : Call F) ∈ calls)
    (ev : ObsFn W Obs.Names.«Lists::length<KernelTypes::KRecRule>» [p] h r h' cs)
    (hr : RulesRepExact κ h ps j p rls) :
    r = .field (rls.length : F) ∧ rls.length < 2 ^ 39 ∧ h' = h := by
  have hrep := rulesRepExact_to_repList hr
  have hlt : rls.length < 2 ^ 39 :=
    IxVM.Refinement.RomBound.bounded_length_lt bd hcall (by simp) hrep
  have hspec := Lib.Lists.length_spec (t := .named "KernelTypes::KRecRule" [])
    (by rw [Obs.Names.«Lists::length<KernelTypes::KRecRule>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<KernelTypes::KRecRule>».symbol]; exact hrep)
  exact ⟨hspec.1, hlt, hspec.2⟩

/-- Resolving `Bytes::address_eq(eqa, KernelRoles::role_addr(rc, KernelRoleSpec::role_eq())) = 1`
identifies `c.κ (ixAddr a_eq) = Ix.Kernel.eqName`. -/
theorem eq_addr_key_spec {c : Ctx} {rc eqa v_role v_raddr : SourceValue F} {a_eq : Bytes.Address}
    {h₀ h₁ h₂ h₃ : Heap F} {cs_role cs_raddr cs_eq : List (Call F)}
    (hroles : RolesSpec) (hwf : c.t.wf = true)
    (hg_raddr : Good c cs_raddr)
    (hrc : RCRep c.t c.lim h₁ rc)
    (ha_eq : Bytes.RepAddressRef addrTy h₂ a_eq eqa)
    (ev_role : ObsFn W "KernelRoleSpec::role_eq" [] h₀ v_role h₁ cs_role)
    (ev_raddr : ObsFn W "KernelRoles::role_addr" [rc, v_role] h₁ v_raddr h₂ cs_raddr)
    (ev_eq : ObsFn W "Bytes::address_eq" [eqa, v_raddr] h₂ (.field 1) h₃ cs_eq) :
    c.κ (ixAddr a_eq) = Ix.Kernel.eqName ∧ h₃ = h₂ := by
  obtain ⟨hv_role, _, _⟩ := Obs.«KernelRoleSpec::role_eq».obs ev_role
  rw [hv_role] at ev_raddr
  have hnum : (8 : F) = roleNum .eq := rfl
  rw [hnum] at ev_raddr
  have hra_fn : Specs.Roles.role_addr (ScopedCtx.unrestricted c)
      [rc, .field (roleNum .eq)] h₁ v_raddr h₂ cs_raddr :=
    hroles c hwf .role_addr _ _ _ _ _ ev_raddr
  obtain ⟨a_tbl, ha_tbl, haddr_of, _⟩ := hra_fn rc .eq rfl (CoreGood.unrestricted hg_raddr) hrc
  obtain ⟨heq_f, hh₃⟩ := Lib.address_eq_spec ev_eq ha_eq ha_tbl
  have ha_same : a_eq = a_tbl := by
    by_cases h : a_eq = a_tbl
    · exact h
    · rw [ite_eq_right h] at heq_f
      injection heq_f with hf
      exact absurd hf one_ne_zero
  subst ha_same
  exact ⟨keyOf_of_addressOf hwf haddr_of, hh₃⟩

/-! ## `IxonDeserialize::get_address` over `L1.Stream` -/

/-- The 32 byte variable names `b0` … `b31` bound by `IxonDeserialize::get_address`. -/
private def gaNames : List String :=
  ["b0", "b1", "b2", "b3", "b4", "b5", "b6", "b7",
   "b8", "b9", "b10", "b11", "b12", "b13", "b14", "b15",
   "b16", "b17", "b18", "b19", "b20", "b21", "b22", "b23",
   "b24", "b25", "b26", "b27", "b28", "b29", "b30", "b31"]

private def gaEnd : Aiur.Generic.Expr F :=
  .tuple [.store (.array (gaNames.map .var)), .var "s"]

private def gaFrom : List String → String → Aiur.Generic.Expr F
  | [], _ => gaEnd
  | b :: bs, scr => .letValue (L1.consPat b "s") (.load (.var scr)) (gaFrom bs "s")

private theorem get_address_body :
    IxVM.IxonDeserialize.get_address.body = gaFrom gaNames "stream" := rfl

private theorem s_notMem_gaNames : "s" ∉ gaNames := by
  decide

private theorem gaNames_nodup : gaNames.Nodup := by
  decide

private theorem gaVars_inv {locals : Environment F Nat} :
    ∀ (names : List String) (xs : List UInt8),
      L1.Bound locals names xs →
      ∀ {before after : Heap F} {vs : List (SourceValue F)} {cs : List (Call F)},
        ObsArgs W [] locals (names.map .var) before vs after cs →
        vs = xs.map (fun b => .field (b.toNat : F)) ∧ after = before ∧ cs = []
  | [], xs, hb, before, after, vs, cs, ev => by
    cases hb
    obtain ⟨rfl, rfl, rfl⟩ := ev.nil_inv
    exact ⟨rfl, rfl, rfl⟩
  | n :: ns, xs, hb, before, after, vs, cs, ev => by
    cases hb with
    | @cons _ x _ xs' hn hrest =>
      obtain ⟨v, vs', m₁, c₁, c₂, rfl, dv, av, rfl⟩ := ev.cons_inv
      obtain ⟨l₁, rfl, rfl⟩ := dv.var_inv
      rw [hn] at l₁
      injection l₁ with l₁; injection l₁ with _ hv
      subst hv
      obtain ⟨hvs, rfl, rfl⟩ := gaVars_inv ns xs' hrest av
      have hbv : L1.bv x = .field (x.toNat : F) := rfl
      rw [hbv, hvs]
      exact ⟨rfl, rfl, rfl⟩

private theorem gaEnd_inv {locals : Environment F Nat} {xs : List UInt8}
    (hxlen : xs.length = 32)
    (hb : L1.Bound locals gaNames xs)
    {s_ptr : SourceValue F}
    (hs : locals.find? (·.1 == "s") = some ("s", s_ptr))
    {h h' : Heap F} {r : SourceValue F} {cs : List (Call F)}
    (ev : ObsExpr W [] locals gaEnd h r h' cs) :
    ∃ (a : Bytes.Address) (x_t : SourceValue F),
      a.toList = xs ∧
      r = .tuple [x_t, s_ptr] ∧
      Bytes.RepAddressRef addrTy h' a x_t ∧
      Heap.Extends h h' ∧ cs = [] := by
  dsimp only [gaEnd] at ev
  obtain ⟨tvals, atup, rfl⟩ := ev.tuple_inv
  obtain ⟨x_t, vs₁, m₁, c₁, c₂, rfl, dt, atail, hc_top⟩ := atup.cons_inv
  obtain ⟨arr_v, m_arr, darr, rfl, hm₁⟩ := dt.store_inv
  obtain ⟨bvals, dvars, rfl⟩ := darr.array_inv
  obtain ⟨hbvals, hm_arr, hcs_vars⟩ := gaVars_inv gaNames xs hb dvars
  obtain ⟨x_s, vs₂, m₂, c₃, c₄, rfl, ds, anil, hc_tail⟩ := atail.cons_inv
  obtain ⟨ls, hm₂, hc₃⟩ := ds.var_inv
  rw [hs] at ls
  injection ls with ls; injection ls with _ hxs
  subst hxs
  obtain ⟨rfl, hh', hc₄⟩ := anil.nil_inv
  let bfn : UInt8 → SourceValue F := fun b => .field (b.toNat : F)
  have hbvals' : bvals = xs.map bfn := hbvals
  have hh'_eq : h' = h ++ [.tuple (xs.map bfn)] := by
    rw [hh', hm₂, hm₁, hm_arr, hbvals']
  have hcs_eq : cs = [] := by
    rw [hc_top, hc_tail, hcs_vars, hc₃, hc₄]; rfl
  let a : Bytes.Address := ⟨xs.toArray, by simp [hxlen]⟩
  have halist : a.toList = xs := by simp [a, Vector.toList]
  have hty : (Value.tuple (xs.map bfn) : SourceValue F).type = addrTy := by
    have hrep : ((xs.map bfn).map (fun v : SourceValue F => v.type)) =
        List.replicate 32 .field := by
      apply List.ext_getElem (by simp [hxlen])
      intro k hk₁ hk₂
      rw [List.getElem_map, List.getElem_map, List.getElem_replicate]
      simp [bfn, Value.type]
    simp only [Value.type, addrTy]
    exact congrArg Aiur.Ty.tuple hrep
  rw [hh'_eq, hm_arr, hbvals']
  refine ⟨a, .ptr (Value.tuple (xs.map bfn) : SourceValue F).type h.length,
    halist, rfl, ?_, Heap.Extends.snoc h _, hcs_eq⟩
  rw [hty]
  exact ⟨h.length, Value.tuple (xs.map bfn), rfl, by simp,
    L1.repAddress_iff.mpr (by simp [L1.digestV, L1.bv, bfn, halist])⟩

private theorem gaFrom_inv :
    ∀ (bs pre : List String) (ys : List UInt8)
      {locals : Environment F Nat} {scr : String} {ptr : SourceValue F}
      {bytes : List UInt8} {h h' : Heap F} {r : SourceValue F} {cs : List (Call F)},
      pre.reverse ++ bs = gaNames →
      L1.Bound locals pre ys →
      (bs = [] → locals.find? (·.1 == "s") = some ("s", ptr)) →
      (bs ≠ [] → locals.find? (·.1 == scr) = some (scr, ptr)) →
      L1.Stream h bytes ptr →
      ObsExpr W [] locals (gaFrom bs scr) h r h' cs →
      ∃ (a : Bytes.Address) (xs rem : List UInt8) (x_t x_s2 : SourceValue F),
        xs.length = bs.length ∧
        bytes = xs ++ rem ∧
        a.toList = ys.reverse ++ xs ∧
        r = .tuple [x_t, x_s2] ∧
        Bytes.RepAddressRef addrTy h' a x_t ∧
        L1.Stream h' rem x_s2 ∧
        Heap.Extends h h' ∧ cs = []
  | [], pre, ys, locals, _, ptr, bytes, h, h', r, cs, hga, hb, hs0, _, hstr, ev => by
    rw [List.append_nil] at hga
    have hb_rev : L1.Bound locals gaNames ys.reverse :=
      hga ▸ List.forall₂_reverse_iff.mpr hb
    have hylen : ys.reverse.length = 32 := hb_rev.length_eq.symm
    obtain ⟨a, x_t, halist, hr, hrep, ext, hcs⟩ := gaEnd_inv hylen hb_rev (hs0 rfl) ev
    exact ⟨a, [], bytes, x_t, ptr, rfl, rfl, by simpa using halist, hr, hrep, hstr.mono ext, ext, hcs⟩
  | b :: bs, pre, ys, locals, scr, ptr, bytes, h, h', r, cs, hga, hb, _, hscr, hstr, ev => by
    simp only [gaFrom] at ev
    obtain ⟨v, m₁, bnd, c₁, c₂, dx, mt, db, rfl⟩ := ev.letValue_inv
    obtain ⟨p, dp, ld⟩ := dx.load_inv
    obtain ⟨lp, rfl, rfl⟩ := dp.var_inv
    rw [hscr (by simp)] at lp
    injection lp with lp; injection lp with _ hp
    subst hp
    rcases L1.stream_inv hstr ld with ⟨rfl, rfl⟩ | ⟨x, rem0, tail, rfl, rfl, htail⟩
    · rw [L1.consPat, L1.match_cons_nil] at mt; cases mt
    · rw [L1.consPat, L1.match_cons_cons] at mt
      injection mt with mt; injection mt with hbnd
      subst hbnd
      have hnd : (pre.reverse ++ b :: bs).Nodup := hga ▸ gaNames_nodup
      have hb_not_pre : b ∉ pre := by
        intro hm
        exact (List.nodup_append.mp hnd).2.2 b (List.mem_reverse.mpr hm) b
          (List.mem_cons_self ..) rfl
      have hb_in_ga : b ∈ gaNames := by rw [← hga]; simp
      have hs_ne_b : "s" ≠ b := fun heq => s_notMem_gaNames (heq ▸ hb_in_ga)
      have hs_not_pre : "s" ∉ pre := by
        intro hm
        apply s_notMem_gaNames
        rw [← hga]
        exact List.mem_append_left _ (List.mem_reverse.mpr hm)
      have hb_next : L1.Bound ([(b, L1.bv x), ("s", tail)] ++ locals) (b :: pre) (x :: ys) := by
        refine .cons (by simp [List.find?_cons]) (L1.bound_skip _ ?_ hb)
        intro n hn e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · intro heq; simp only at heq; exact hb_not_pre (heq ▸ hn)
        · intro heq; simp only at heq; exact hs_not_pre (heq ▸ hn)
      have hs_find : ([(b, L1.bv x), ("s", tail)] ++ locals).find? (·.1 == "s") = some ("s", tail) := by
        have hbn : (b == "s") = false := beq_false_of_ne hs_ne_b.symm
        simp [List.find?_cons, hbn]
      have hga' : (b :: pre).reverse ++ bs = gaNames := by
        rw [List.reverse_cons, List.append_assoc, List.singleton_append]
        exact hga
      obtain ⟨a, xs', rem, x_t, x_s2, hxslen, hrem_eq, halist, hr, hrep, hstr', ext, hcs⟩ :=
        gaFrom_inv bs (b :: pre) (x :: ys) hga' hb_next (fun _ => hs_find) (fun _ => hs_find) htail db
      exact ⟨a, x :: xs', rem, x_t, x_s2, by simp [hxslen], by simp [hrem_eq],
        by simpa using halist, hr, hrep, hstr', ext, by simp [hcs]⟩

/-- **`IxonDeserialize::get_address`** peels 32 bytes off an `L1.Stream`, allocates their
`Bytes.RepAddressRef`, and returns `(addr_ptr, rest_stream)`. -/
theorem get_address_spec {s_ptr r : SourceValue F} {bytes : List UInt8}
    {h h' : Heap F} {cs : List (Call F)}
    (hs : L1.Stream h bytes s_ptr)
    (ev : ObsFn W "IxonDeserialize::get_address" [s_ptr] h r h' cs) :
    ∃ (a : Bytes.Address) (rem : List UInt8) (x_t x_s2 : SourceValue F),
      bytes = a.toList ++ rem ∧
      r = .tuple [x_t, x_s2] ∧
      Bytes.RepAddressRef addrTy h' a x_t ∧
      L1.Stream h' rem x_s2 ∧
      Heap.Extends h h' ∧
      cs = [] := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.IxonDeserialize.get_address.lookup
    (by first | rfl | decide | simp [IxVM.IxonDeserialize.get_address, ControlLower.hasControl]) ev
  rw [get_address_body] at d0
  obtain ⟨a, xs, rem, x_t, x_s2, _, hbytes, halist, hr, hrep, hstr', ext, hcs⟩ :=
    gaFrom_inv gaNames [] [] rfl .nil (fun h => nomatch h)
      (fun _ => rfl) hs d0
  simp only [List.reverse_nil, List.nil_append] at halist
  exact ⟨a, rem, x_t, x_s2, by rw [halist]; exact hbytes, hr, hrep, hstr', ext, hcs⟩

/-! ## Widened `< 4611686018427387904` (`2 ^ 62`) telescope wrappers -/

private theorem peel_n_lams_collect_go_wide (rem : Nat) :
    ∀ {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat} {E : KExpr}
      {e acc r_e r_acc : SourceValue F} {n peeled d_out : F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n = rem →
      ZMod.val peeled + rem < 4611686018427387904 →
      ZMod.val d_out = ZMod.val peeled + rem →
      ObsFn W "KernelCheck::peel_n_lams_collect" [e, .field n, .field peeled, acc]
        h (.tuple [r_e, .field d_out, r_acc]) h' cs →
      TmExact κ 0 Γ h k E e →
      (E.stripLams rem).isSome = true := by
  induction rem with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rfl
  | succ rem ih =>
    intro κ Γ k E e acc r_e r_acc n peeled d_out h h' cs hn hlt hd ev hE
    have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
    have hval1 : ZMod.val (1 : F) = 1 := rfl
    match Obs.«KernelCheck::peel_n_lams_collect».obs ev with
    | .n0 (hv14 := hv) .. =>
      injection hv with h0; subst h0; simp at hn
    | .other_Lam (x_dom := x_dom) (hne44 := hne) (ld59 := ld) (op113 := op_sub)
        (op128 := op_add) (hm139 := rfl) (ev88 := ev_rec) .. =>
      obtain rfl := Lib.sub_one_inv op_sub
      have hpred := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e]))
      rw [SubstAux.add_ok op_add] at ev_rec
      have hp1 : ZMod.val (peeled + 1) = ZMod.val peeled + 1 := SubstAux.val_add (by omega)
      obtain ⟨_, B, _, rfl, _, hb, _⟩ := hE.lam_of_load ld
      have ext := Heap.Extends.snoc h
        (.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Cons" [x_dom, acc])
      have hstrip := ih (n := n - 1) (peeled := peeled + 1) (d_out := d_out)
        (by omega) (by omega) (by omega) ev_rec (hb.mono ext)
      simp [Expr.stripLams, hstrip]
    | .other_other (he169 := he_tup) .. =>
      injection he_tup with h1; injection h1 with _ h2; injection h2 with h2 _
      injection h2 with hpeel; subst hpeel; omega

theorem peel_n_lams_collect_spec_wide {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {e acc r_e r_acc : SourceValue F} {d : F} {h h' : Heap F} {cs : List (Call F)} {E : KExpr}
    (hd : ZMod.val d < 4611686018427387904)
    (ev : ObsFn W "KernelCheck::peel_n_lams_collect" [e, .field d, .field 0, acc]
      h (.tuple [r_e, .field d, r_acc]) h' cs)
    (hE : TmExact κ 0 Γ h 0 E e) :
    (E.stripLams (ZMod.val d)).isSome = true ∧
      ∀ i, ∃ fvs rem, IxVM.Refinement.Decl.openLamsAtFvars (ZMod.val d) E i = some (fvs, rem) := by
  have hs := peel_n_lams_collect_go_wide (ZMod.val d) rfl (by simpa using hd) (by simp) ev hE
  exact ⟨hs, fun i => openLamsAtFvars_of_stripLams (ZMod.val d) E i hs⟩

private theorem assert_index_vars_go_wide (rem : Nat) :
    ∀ {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat} {As : List KExpr}
      {args_ptr r : SourceValue F} {ni idx : F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val ni = ZMod.val idx + rem →
      ZMod.val ni < 4611686018427387904 →
      As.length = rem →
      ObsFn W "KernelModeled::assert_index_vars" [args_ptr, .field ni, .field idx] h r h' cs →
      RepList kexprListEnum (fun h E p => TmExact κ 0 Γ h k E p) h As args_ptr →
      As = ((List.range rem).map fun m => .bvar (ZMod.val ni - 1 - (ZMod.val idx + m))) ∧ h' = h := by
  induction rem with
  | zero =>
    intro κ Γ k As args_ptr r ni idx h h' cs hrem _ hlen ev _
    have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
    match Obs.«KernelModeled::assert_index_vars».obs ev with
    | .n0 (he27 := hh) .. =>
      exact ⟨List.eq_nil_of_length_eq_zero hlen, hh⟩
    | .other (op17 := op17) (hne29 := hne) .. =>
      rw [SubstAux.sub_ok op17] at hne
      have hv : ZMod.val (ni - idx) = 0 := by rw [SubstAux.val_sub (by omega)]; omega
      have hcz : ni - idx = 0 := ZMod.val_injective _ (by simpa using hv)
      exact absurd (congrArg Value.field hcz) hne
  | succ rem ih =>
    intro κ Γ k As args_ptr r ni idx h h' cs hrem hni hlen ev hAs
    have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
    have hval1 : ZMod.val (1 : F) = 1 := rfl
    match Obs.«KernelModeled::assert_index_vars».obs ev with
    | .n0 (op17 := op17) .. =>
      have hsub := SubstAux.sub_ok op17
      injection hsub with h0
      have hv : ZMod.val (ni - idx) = rem + 1 := by rw [SubstAux.val_sub (by omega)]; omega
      rw [← h0, ZMod.val_zero] at hv; omega
    | .other (ld43 := ld_cons) (ld69 := ld_bv) (op123 := op_ni1) (op115 := op_sub)
        (heq126 := heq_j) (op163 := op_inc) (ev132 := ev_rec) .. =>
      obtain ⟨A, As', hcons_eq, hA, hAs'⟩ := Lib.rep_cons_of_load hAs ld_cons
      subst hcons_eq
      obtain ⟨j, hj_eq, _, hbc⟩ := hA.bvar_of_load ld_bv
      subst hj_eq
      rw [SubstAux.sub_ok op_ni1] at op_sub
      rw [SubstAux.sub_ok op_sub] at heq_j
      injection heq_j with hj_val
      rw [SubstAux.add_ok op_inc] at ev_rec
      have hni1 : ZMod.val (ni - 1) = ZMod.val ni - 1 := SubstAux.val_sub (by omega)
      have hj_nat : ZMod.val j = ZMod.val ni - 1 - ZMod.val idx := by
        rw [hj_val, SubstAux.val_sub (by omega), hni1]
      have hA_eq : A = .bvar (ZMod.val ni - 1 - ZMod.val idx) := by
        rcases hbc with ⟨_, rfl⟩ | ⟨_, hd, _⟩
        · rw [hj_nat]
        · exact nomatch hd
      have hi1 : ZMod.val (idx + 1) = ZMod.val idx + 1 := SubstAux.val_add (by omega)
      obtain ⟨htail, hh⟩ := ih (ni := ni) (idx := idx + 1)
        (by omega) hni (by simp at hlen; omega) ev_rec hAs'
      refine ⟨?_, hh⟩
      rw [hA_eq, htail, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero, List.cons.injEq, true_and]
      apply List.map_congr_left
      intro m _; simp only [Function.comp_apply, hi1]; congr 1; omega

theorem assert_index_vars_spec_wide {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat}
    {As : List KExpr} {args_ptr r : SourceValue F} {ni : F} {h h' : Heap F} {cs : List (Call F)}
    (hni : ZMod.val ni < 4611686018427387904) (hlen : As.length = ZMod.val ni)
    (ev : ObsFn W "KernelModeled::assert_index_vars" [args_ptr, .field ni, .field 0] h r h' cs)
    (hAs : RepList kexprListEnum (fun h E p => TmExact κ 0 Γ h k E p) h As args_ptr) :
    As = ((List.range (ZMod.val ni)).map fun m => .bvar (ZMod.val ni - 1 - m)) ∧ h' = h := by
  simpa [ZMod.val_zero] using assert_index_vars_go_wide (ZMod.val ni) (ni := ni) (idx := 0)
    (by simp) hni hlen ev hAs

theorem rec_major_pins_spec_wide {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {E : KExpr}
    {ty_ptr r : SourceValue F} {rp ni : F} {h h' : Heap F} {cs : List (Call F)}
    (bd : IxVM.Consistency.Bounded cs)
    (hrp : ZMod.val rp < 288230376151711744)
    (hni : ZMod.val ni < 288230376151711744)
    (ev : ObsFn W "KernelModeled::rec_major_pins" [ty_ptr, .field rp, .field ni] h r h' cs)
    (hE : TmExact κ 0 Γ h 0 E ty_ptr) :
    ∃ iaddr ilvls_ptr pins_ptr a_ind, ∃ (inp : F), ∃ bs dom body m_maj lvls_pos As,
      r = .tuple [iaddr, ilvls_ptr, pins_ptr] ∧
      Bytes.RepAddressRef addrTy h' a_ind iaddr ∧
      RepKLevelList h' lvls_pos ilvls_ptr ∧
      E.stripPis (ZMod.val rp + ZMod.val ni) = some (bs, .forallE dom body m_maj) ∧
      dom.getAppFn = .const (κ (ixAddr a_ind)) lvls_pos ∧
      dom.getAppArgs = As ∧
      ZMod.val inp ≤ As.length ∧
      (As.length : F) = inp + ni ∧
      As.drop (ZMod.val inp) =
        ((List.range (ZMod.val ni)).map fun m => .bvar (ZMod.val ni - 1 - m)) ∧
      (∀ P ∈ As.take (ZMod.val inp), noLooseIn 0 (ZMod.val ni) P = true) ∧
      RepList kexprListEnum (fun h P p => TmExact κ 0 Γ h (ZMod.val rp) P p) h'
        ((As.take (ZMod.val inp)).map (Expr.lowerBVars (ZMod.val ni) 0)) pins_ptr ∧
      As.length = ZMod.val inp + ZMod.val ni := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  match Obs.«KernelModeled::rec_major_pins».obs ev with
  | .run (x_args := x_args) (x_iaddr := iaddr) (x_ilvls := ilvls_ptr) (m141 := m141)
      (x_inp := x_inp) (v358 := pins_ptr)
      (op37 := op_mi) (ev14 := ev_peel) (ld51 := ld_fa) (ev89 := ev_sp) (ld122 := ld_c)
      (ev157 := ev_ci) (ld151 := _) (heq245 := heq_ini) (ev270 := ev_len)
      (op292 := op_add_inp) (heq295 := heq_len) (ev324 := ev_drop) (ev309 := ev_idx)
      (he359 := hr) (ev399 := ev_take) (ev385 := ev_low) (he423 := hh) (hc424 := hc) .. =>
    subst hc hr hh heq_ini
    rw [SubstAux.add_ok op_mi] at ev_peel
    have hmi_val : ZMod.val (rp + ni) = ZMod.val rp + ZMod.val ni := SubstAux.val_add (by omega)
    obtain ⟨bs, rem, hstrip, hrem, rfl⟩ :=
      peel_n_foralls_exact (ZMod.val rp + ZMod.val ni) hmi_val ev_peel hE
    rw [Nat.zero_add] at hrem
    obtain ⟨dom, body, ℓ_maj, rfl, hdom, _, _⟩ := hrem.forallE_of_load ld_fa
    obtain ⟨hd, sp, H, As, htup, hH, hAs, hdom_eq⟩ := collect_spine_exact ev_sp hdom
    injection htup with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    obtain ⟨a_ind, lvls_pos, rfl, ra_ind, rlvls⟩ := hH.const_of_load ld_c
    have hfn_dom : dom.getAppFn = .const (κ (ixAddr a_ind)) lvls_pos := by
      rw [hdom_eq, getAppFn_mkAppN]; rfl
    have hargs_dom : dom.getAppArgs = As := by
      rw [hdom_eq, getAppArgs_mkAppN]; rfl
    cases x_inp with
    | field inp =>
      rw [SubstAux.add_ok op_add_inp] at heq_len
      have ext_ci := ev_ci.heap_extends
      have hAs1 := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext_ci hAs
      have hAs_lt : As.length < 2 ^ 39 :=
        IxVM.Refinement.RomBound.bounded_length_lt bd
          (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_args], m141⟩)
          (by simp) (by simp) hAs1
      obtain ⟨hv257, rfl⟩ := tele_klength ev_len hAs1
      rw [hv257] at heq_len
      injection heq_len with hlen_f
      obtain ⟨hinp_le, hdrop, rfl⟩ := tele_kdrop ev_drop hAs1
      have hAs_len : As.length = ZMod.val inp + ZMod.val ni := by
        have hv := congrArg ZMod.val hlen_f
        rw [SubstAux.val_natCast (by omega), SubstAux.val_add (by omega)] at hv
        exact hv
      obtain ⟨hdrop_eq, rfl⟩ :=
        assert_index_vars_spec_wide (by omega) (by simp [hAs_len]) ev_idx hdrop
      obtain ⟨_, htake⟩ := tele_ktake (fun _ _ _ _ e x => x.mono e) ev_take hAs1
      obtain ⟨hno_take, hpins⟩ := lower_pins_spec (rp := ZMod.val rp)
        (bounded_sub (fun _ hx => by simp [hx]) bd) hni ev_low htake
      have ext_sp_end := ext_ci.trans (ev_take.heap_extends.trans ev_low.heap_extends)
      exact ⟨iaddr, ilvls_ptr, pins_ptr, a_ind, inp, bs, dom, body, bmeta ℓ_maj, lvls_pos, As,
        rfl,
        Bytes.repAddressRef_heapMono₂ addrTy ext_sp_end ra_ind,
        rlvls.mono ext_sp_end,
        hstrip, hfn_dom, hargs_dom, hinp_le, hlen_f, hdrop_eq, hno_take, hpins, hAs_len⟩
    | tuple _ | ptr _ _ | construct _ _ _ => cases op_add_inp

private theorem bvars_desc_go_wide (rem : Nat) :
    ∀ {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
      {top cnt : F} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val cnt = rem →
      rem ≤ ZMod.val top →
      ZMod.val top ≤ d →
      d < 4611686018427387904 →
      ObsFn W "KernelModeled::bvars_desc" [.field top, .field cnt] h r h' cs →
      RepList kexprListEnum (fun h E p => TmExact κ d Γ h 0 E p) h'
        ((List.range rem).map fun m => .fvar (d - ZMod.val top + m) (Γ (d - ZMod.val top + m))) r := by
  induction rem with
  | zero =>
    intro κ d Γ top cnt r h h' cs hrem _ _ _ ev
    match Obs.«KernelModeled::bvars_desc».obs ev with
    | .n0 (he19 := hr) (hm18 := hh) .. =>
      subst hr hh; exact .nil (by simp)
    | .other (hne24 := hne) .. =>
      have := Lib.val_sub_one (fun (e : cnt = 0) => hne (by rw [e])); omega
  | succ rem ih =>
    intro κ d Γ top cnt r h h' cs hrem hle_top htop_d hd_lt ev
    have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
    match Obs.«KernelModeled::bvars_desc».obs ev with
    | .n0 (hv14 := hv) .. => injection hv with h0; subst h0; simp at hrem
    | .other (m39 := m39) (hne24 := hne)
        (he32 := hr) (hm31 := hh) (hm47 := hm39) (op65 := op_t1) (op94 := op_t2)
        (op109 := op_c1) (ev78 := ev_rec) .. =>
      subst hr hh hm39
      obtain rfl := Lib.sub_one_inv op_t1
      obtain rfl := Lib.sub_one_inv op_t2
      obtain rfl := Lib.sub_one_inv op_c1
      have hcnt1 := Lib.val_sub_one (fun (e : cnt = 0) => hne (by rw [e]))
      have htop_ne : top ≠ 0 := by intro e; subst e; simp at hle_top
      have htop1 := Lib.val_sub_one htop_ne
      have hhead0 : TmExact κ d Γ (h ++ [.construct kexprEnum "BVar" [.field (top - 1)]]) 0
          (.fvar (fvIdx d 0 (ZMod.val (top - 1))) (Γ (fvIdx d 0 (ZMod.val (top - 1)))))
          (.ptr (.enum kexprEnum) h.length) :=
        .bvarFree (by simp) (by omega) (by omega) (by omega)
      have hfv_eq : fvIdx d 0 (ZMod.val (top - 1)) = d - ZMod.val top := by
        unfold fvIdx; omega
      have hhead : TmExact κ d Γ (h ++ [.construct kexprEnum "BVar" [.field (top - 1)]]) 0
          (.fvar (d - ZMod.val top) (Γ (d - ZMod.val top)))
          (.ptr (.enum kexprEnum) h.length) := by
        rwa [hfv_eq] at hhead0
      have htail := ih (κ := κ) (Γ := Γ) (top := top - 1) (cnt := cnt - 1)
        (by omega) (by omega) (by omega) hd_lt ev_rec
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
      have htail_eq :
          ((List.range rem).map
            ((fun m => Expr.fvar (d - ZMod.val top + m) (Γ (d - ZMod.val top + m))) ∘ (· + 1))) =
          (List.range rem).map
            (fun m => .fvar (d - ZMod.val (top - 1) + m) (Γ (d - ZMod.val (top - 1) + m))) := by
        apply List.map_congr_left
        intro m _; simp only [Function.comp_apply]
        have heq_idx : d - ZMod.val top + (m + 1) = d - ZMod.val (top - 1) + m := by omega
        rw [heq_idx]
      rw [htail_eq]
      exact Lib.rep_store_cons (fun _ _ _ _ e x => x.mono e) (hhead.mono ev_rec.heap_extends) htail

theorem bvars_desc_exact_wide {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {top cnt : F} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hle_top : ZMod.val cnt ≤ ZMod.val top) (htop_d : ZMod.val top ≤ d)
    (hd_lt : d < 4611686018427387904)
    (ev : ObsFn W "KernelModeled::bvars_desc" [.field top, .field cnt] h r h' cs) :
    RepList kexprListEnum (fun h E p => TmExact κ d Γ h 0 E p) h'
      ((List.range (ZMod.val cnt)).map fun m =>
        .fvar (d - ZMod.val top + m) (Γ (d - ZMod.val top + m))) r :=
  bvars_desc_go_wide (ZMod.val cnt) rfl hle_top htop_d hd_lt ev

/-! ## Expression and inference algebra for `check_iota_rule` -/

/-- From `Infer env g d e ty` and `e.getAppFn = .const k us`, extract the stored constant `ci` and
its level-parameter arity `us.length = ci.toConstantVal.levelParams.length`. -/
theorem infer_getAppFn_const {env : Ix.Kernel.Env .anon} {g : Ix.Kernel.Rules.Grade}
    {d : Nat} {e ty : KExpr} {k : KKey} {us : List KLevel}
    (hinf : Infer env g d e ty) (hfn : e.getAppFn = .const k us) :
    ∃ ci, env.find? k = some ci ∧ us.length = ci.toConstantVal.levelParams.length := by
  induction e generalizing g ty with
  | const n ls =>
    injection hfn with hk hls
    subst hk hls
    cases hinf with
    | const hfind _ hlen => exact ⟨_, hfind, hlen⟩
  | app f a ihf _ =>
    change f.getAppFn = .const k us at hfn
    cases hinf with
    | app hf _ _ _ => exact ihf hf hfn
    | appSkip hf _ _ => exact ihf hf hfn
  | bvar _ | fvar _ _ | sort _ | lam _ _ _ | forallE _ _ _ | letE _ _ _ _ | lit _ | proj _ _ _ =>
    exact nomatch hfn

private theorem stripPis_forall_instantiate1 (v : KExpr) (k : KKey) (us : List KLevel) :
    ∀ (m : Nat) (e : KExpr) (c : Nat) {bs : List (KExpr × Ix.Kernel.BinderMeta)}
      {dom body : KExpr} {mb : Ix.Kernel.BinderMeta},
      e.stripPis m = some (bs, .forallE dom body mb) →
      dom.getAppFn = .const k us →
      ∃ bs' dom' body',
        (e.instantiate1 v c).stripPis m = some (bs', .forallE dom' body' mb) ∧
        dom'.getAppFn = .const k us
  | 0, e, c, bs, dom, body, mb, hs, hfn => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨[], dom.instantiate1 v c, body.instantiate1 v (c + 1), rfl, ?_⟩
    rw [mkAppN_getAppFn_getAppArgs dom, instantiate1_mkAppN, hfn]
    change (Expr.mkAppN (.const k us) (dom.getAppArgs.map (·.instantiate1 v c))).getAppFn = .const k us
    rw [getAppFn_mkAppN]; rfl
  | m + 1, .forallE ty b mb₀, c, bs, dom, body, mb, hs, hfn => by
    simp only [Expr.stripPis] at hs
    cases hsb : b.stripPis m with
    | none => simp [hsb] at hs
    | some p =>
      rw [hsb] at hs
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, hp2⟩ := hs
      rcases p with ⟨bs₁, rem₁⟩
      subst hp2
      obtain ⟨bs', dom', body', ihs, ihfn⟩ :=
        stripPis_forall_instantiate1 v k us m b (c + 1) hsb hfn
      exact ⟨(ty.instantiate1 v c, mb₀) :: bs', dom', body',
        by simp [Expr.instantiate1, Expr.stripPis, ihs], ihfn⟩
  | _ + 1, .bvar _, _, _, _, _, _, hs, _
  | _ + 1, .fvar _ _, _, _, _, _, _, hs, _
  | _ + 1, .sort _, _, _, _, _, _, hs, _
  | _ + 1, .const _ _, _, _, _, _, _, hs, _
  | _ + 1, .app _ _, _, _, _, _, _, hs, _
  | _ + 1, .lam _ _ _, _, _, _, _, _, hs, _
  | _ + 1, .letE _ _ _ _, _, _, _, _, _, hs, _
  | _ + 1, .lit _, _, _, _, _, _, hs, _
  | _ + 1, .proj _ _ _, _, _, _, _, _, hs, _ => nomatch hs

/-- From `Infer env .full d E ty`, `E.stripPis m = some (bs, .forallE dom body mb)`, and
`dom.getAppFn = .const k us`, extract `us.length = ci.toConstantVal.levelParams.length`. -/
theorem infer_stripPis_dom_const_lvls :
    ∀ (m : Nat) {env : Ix.Kernel.Env .anon} {d : Nat} {E ty dom body : KExpr}
      {bs : List (KExpr × Ix.Kernel.BinderMeta)} {mb : Ix.Kernel.BinderMeta}
      {k : KKey} {us : List KLevel},
      Infer env .full d E ty →
      E.stripPis m = some (bs, .forallE dom body mb) →
      dom.getAppFn = .const k us →
      ∃ ci, env.find? k = some ci ∧ us.length = ci.toConstantVal.levelParams.length := by
  intro m
  induction m with
  | zero =>
    intro env d E ty dom body bs mb k us hinf hs hfn
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨_, rfl⟩ := hs
    cases hinf with
    | forallE hdom _ _ _ _ => exact infer_getAppFn_const hdom hfn
  | succ m ih =>
    intro env d E ty dom body bs mb k us hinf hs hfn
    cases E with
    | forallE tyB b mb₀ =>
      simp only [Expr.stripPis] at hs
      cases hsb : b.stripPis m with
      | none => simp [hsb] at hs
      | some p =>
        rw [hsb] at hs
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        rcases p with ⟨bs₁, rem₁⟩
        obtain ⟨_, rfl⟩ := hs
        cases hinf with
        | forallE _ _ hb _ _ =>
          obtain ⟨bs', dom', body', hs', hfn'⟩ :=
            stripPis_forall_instantiate1 (.fvar d tyB) k us m b 0 hsb hfn
          exact ih hb hs' hfn'
    | _ => exact nomatch hs

theorem noLooseIn_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) (n : Nat) :
    ∀ (e : KExpr) (lo : Nat),
      noLooseIn lo n (e.instantiateLevelParams ks us) = noLooseIn lo n e := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ | fvar _ _ => intro _; rfl
  | app f a ihf iha => intro lo; simp [Expr.instantiateLevelParams, noLooseIn, ihf lo, iha lo]
  | lam t b _ iht ihb | forallE t b _ iht ihb =>
    intro lo; simp [Expr.instantiateLevelParams, noLooseIn, iht lo, ihb (lo + 1)]
  | letE t v b _ iht ihv ihb =>
    intro lo; simp [Expr.instantiateLevelParams, noLooseIn, iht lo, ihv lo, ihb (lo + 1)]
  | proj _ _ x ih => intro lo; simp [Expr.instantiateLevelParams, noLooseIn, ih lo]

theorem getAppFn_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ e : KExpr,
      (e.instantiateLevelParams ks us).getAppFn = (e.getAppFn).instantiateLevelParams ks us
  | .app f _ => getAppFn_instantiateLevelParams ks us f
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lam _ _ _ | .forallE _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

theorem getAppArgs_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ e : KExpr,
      (e.instantiateLevelParams ks us).getAppArgs =
        e.getAppArgs.map (·.instantiateLevelParams ks us)
  | .app f a => by
    have hargs : ∀ x : KExpr, (Expr.app f a).getAppArgs = f.getAppArgs ++ [a] :=
      fun _ => getAppArgs_mkAppN [a] f
    have hargs' :
        (Expr.app (f.instantiateLevelParams ks us) (a.instantiateLevelParams ks us)).getAppArgs =
          (f.instantiateLevelParams ks us).getAppArgs ++ [a.instantiateLevelParams ks us] :=
      getAppArgs_mkAppN [a.instantiateLevelParams ks us] (f.instantiateLevelParams ks us)
    change (Expr.app (f.instantiateLevelParams ks us) (a.instantiateLevelParams ks us)).getAppArgs = _
    rw [hargs', getAppArgs_instantiateLevelParams ks us f, hargs a, List.map_append, List.map_singleton]
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lam _ _ _ | .forallE _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

theorem mkAppN_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ (args : List KExpr) (f : KExpr),
      (Expr.mkAppN f args).instantiateLevelParams ks us =
        Expr.mkAppN (f.instantiateLevelParams ks us) (args.map (·.instantiateLevelParams ks us))
  | [], _ => rfl
  | a :: args, f => mkAppN_instantiateLevelParams ks us args (.app f a)

private theorem instantiate1_eq_self_of_bounded (v : KExpr) :
    ∀ {e : KExpr} {k c : Nat}, e.looseBVarsBounded k = true → k ≤ c → e.instantiate1 v c = e := by
  intro e
  induction e with
  | bvar i =>
    intro k c hb hle
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    have hlt : i < c := Nat.lt_of_lt_of_le hb hle
    have hne : ¬ (i == c) = true := by simp [Nat.ne_of_lt hlt]
    have hn : ¬ (i > c) := by omega
    simp [Expr.instantiate1, Nat.ne_of_lt hlt, hn]
  | fvar _ _ | sort _ | const _ _ | lit _ => intro _ _ _ _; rfl
  | app f a ihf iha =>
    intro k c hb hle; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.instantiate1, ihf hb.1 hle, iha hb.2 hle]
  | lam t b _ iht ihb | forallE t b _ iht ihb =>
    intro k c hb hle; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.instantiate1, iht hb.1 hle, ihb (c := c + 1) hb.2 (by omega)]
  | letE t val b _ iht ihv ihb =>
    intro k c hb hle; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp [Expr.instantiate1, iht hb.1.1 hle, ihv hb.1.2 hle, ihb (c := c + 1) hb.2 (by omega)]
  | proj _ _ x ih =>
    intro k c hb hle; simp only [Expr.looseBVarsBounded] at hb
    simp [Expr.instantiate1, ih hb hle]

private theorem instSpine_closed_eq_self :
    ∀ (xs : List KExpr) (t : Nat) {e : KExpr},
      e.looseBVarsBounded 0 = true → Expr.instSpine xs t e = e
  | [], _, _, _ => rfl
  | a :: as, t, e, hb => by
    simp only [Expr.instSpine, instantiate1_eq_self_of_bounded a hb (Nat.zero_le t)]
    exact instSpine_closed_eq_self as (t - 1) hb

theorem instSpine_bvar_getElem :
    ∀ (xs : List KExpr) (k : Nat) (hk : k < xs.length),
      (∀ x ∈ xs, x.looseBVarsBounded 0 = true) →
      Expr.instSpine xs (xs.length - 1) (.bvar (xs.length - 1 - k)) = xs[k]
  | [], _, hk, _ => nomatch hk
  | a :: as, 0, _, hcl => by
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, Expr.instSpine,
      List.getElem_cons_zero]
    have hbvar : (Expr.bvar as.length).instantiate1 a as.length = a := by
      simp [Expr.instantiate1]
    rw [hbvar]
    exact instSpine_closed_eq_self as (as.length - 1) (hcl a (List.mem_cons_self ..))
  | a :: as, k + 1, hk, hcl => by
    have hk' : k < as.length := Nat.lt_of_succ_lt_succ hk
    simp only [List.length_cons, Nat.add_sub_cancel, Expr.instSpine, List.getElem_cons_succ]
    have hidx : as.length - (k + 1) = as.length - 1 - k := by omega
    rw [hidx]
    have hlt : as.length - 1 - k < as.length := by omega
    have hbvar : (Expr.bvar (as.length - 1 - k)).instantiate1 a as.length =
        .bvar (as.length - 1 - k) := by
      have hn : ¬ (as.length - 1 - k > as.length) := by omega
      simp [Expr.instantiate1, Nat.ne_of_lt hlt, hn]
    rw [hbvar]
    exact instSpine_bvar_getElem as k hk' (fun x hx => hcl x (List.mem_cons_of_mem _ hx))

theorem map_instSpine_bvar_range_eq_take {xs : List KExpr} {cnP rP : Nat}
    (hlen : xs.length = rP) (hle : cnP ≤ rP)
    (hcl : ∀ x ∈ xs, x.looseBVarsBounded 0 = true) :
    ((List.range cnP).map (fun k => Expr.bvar (rP - 1 - k))).map
        (fun p => Expr.instSpine xs (rP - 1) p) = xs.take cnP := by
  rw [List.map_map]
  apply List.ext_getElem (by simp [hlen, hle])
  intro k hk₁ hk₂
  simp only [List.length_map, List.length_range] at hk₁
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, List.getElem_take]
  subst hlen
  exact instSpine_bvar_getElem xs k (by omega) hcl

theorem openPisAtFvars_fvars_closed :
    ∀ (m : Nat) {e : KExpr} {i : Nat} {fvs : List KExpr} {rem : KExpr},
      e.looseBVarsBounded 0 = true →
      openPisAtFvars m e i = some (fvs, rem) →
      rem.looseBVarsBounded 0 = true ∧
        (∀ x ∈ fvs, x.looseBVarsBounded 0 = true) ∧
        (∀ k (hk : k < fvs.length), ∃ ty, fvs[k] = .fvar (i + k) ty) := by
  intro m
  induction m with
  | zero =>
    intro e i fvs rem hb hop
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨hb, fun _ hm => absurd hm List.not_mem_nil, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro e i fvs rem hb hop
    cases e with
    | forallE ty body _ =>
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      simp only [openPisAtFvars] at hop
      cases hop' : openPisAtFvars m (body.instantiate1 (.fvar i ty)) (i + 1) with
      | none => simp [hop'] at hop
      | some p =>
        rw [hop'] at hop
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        rcases p with ⟨fvs', rem'⟩
        obtain ⟨rfl, rfl⟩ := hop
        have hb_open : (body.instantiate1 (.fvar i ty)).looseBVarsBounded 0 = true :=
          Expr.looseBVarsBounded_instantiate1_gen (a := .fvar i ty) rfl hb.2
        obtain ⟨hrem, hfvs', hshape⟩ := ih hb_open hop'
        refine ⟨hrem, fun x hx => ?_, fun k hk => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx'
          · rfl
          · exact hfvs' x hx'
        · cases k with
          | zero => exact ⟨ty, by simp⟩
          | succ k' =>
            have hk' : k' < fvs'.length := Nat.lt_of_succ_lt_succ hk
            obtain ⟨ty', hty'⟩ := hshape k' hk'
            exact ⟨ty', by simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hty'⟩
    | _ => exact nomatch hop

/-- Instantiating `e` at its own level parameter list `ps.map .param` is the identity. -/
theorem instantiateLevelParams_self_eq {ps : List LevelParam} {e : KExpr} :
    e.instantiateLevelParams ps (ps.map .param) = e :=
  instantiateLevelParams_self ps e

/-- Convert `TypedListJ posRulesJ` on opened free variables `.fvar idx ty` into `DefEqListJ posRulesJ`
on their `.fvarTypeD` annotations via `Infer.fvar` inversion. -/
theorem typedListJ_fvars_to_defEqListJ {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ {xs doms : List KExpr},
      (∀ x ∈ xs, ∃ idx ty, x = .fvar idx ty) →
      TypedListJ posRulesJ env d xs doms →
      DefEqListJ posRulesJ env d (xs.map Expr.fvarTypeD) doms
  | [], [], _, _ => trivial
  | x :: xs, dom :: doms, hfvs, ⟨⟨ty_inf, hinf, hde⟩, hrest⟩ => by
    obtain ⟨idx, ty_x, rfl⟩ := hfvs x (List.mem_cons_self ..)
    obtain ⟨ps, hperm, hinf_pos⟩ := hinf
    change Infer env .full d (.fvar idx (posOf ps ty_x)) (posOf ps ty_inf) at hinf_pos
    generalize hin : (Expr.fvar idx (posOf ps ty_x) : KExpr) = e_in at hinf_pos
    generalize hout : posOf ps ty_inf = out_ty at hinf_pos
    cases hinf_pos with
    | fvar =>
      injection hin with _ hty_pos
      have hty_eq : ty_inf = ty_x := posOf_inj hperm (hout.trans hty_pos.symm)
      subst hty_eq
      exact ⟨hde, typedListJ_fvars_to_defEqListJ
        (fun y hy => hfvs y (List.mem_cons_of_mem _ hy)) hrest⟩
    | _ => exact nomatch hin

private theorem stripPis_wellFormed :
    ∀ (m : Nat) {e : KExpr} {c : Nat} {env : Ix.Kernel.Env .anon} {lps : List LevelParam}
      {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem : KExpr},
      e.hasFvar = false →
      e.looseBVarsBounded c = true →
      e.constsResolve env = true →
      e.allLevelParamsDefined lps = true →
      e.stripPis m = some (bs, rem) →
      rem.hasFvar = false ∧
      rem.looseBVarsBounded (c + m) = true ∧
      rem.constsResolve env = true ∧
      rem.allLevelParamsDefined lps = true := by
  intro m
  induction m with
  | zero =>
    intro e c env lps bs rem hfv hb hcr hlps hs
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨_, rfl⟩ := hs
    exact ⟨hfv, by simpa using hb, hcr, hlps⟩
  | succ m ih =>
    intro e c env lps bs rem hfv hb hcr hlps hs
    cases e with
    | forallE t b _ =>
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hlps
      simp only [Expr.stripPis] at hs
      cases hsb : b.stripPis m with
      | none => simp [hsb] at hs
      | some p =>
        rw [hsb] at hs
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        rcases p with ⟨_, rem'⟩
        obtain ⟨_, rfl⟩ := hs
        have res := ih hfv.2 hb.2 hcr.2 hlps.1.2 hsb
        rw [show c + 1 + m = c + (m + 1) by omega] at res
        exact res
    | _ => exact nomatch hs

private theorem getAppFn_wellFormed {lps : List LevelParam} :
    ∀ {e : KExpr}, e.allLevelParamsDefined lps = true →
      (e.getAppFn).allLevelParamsDefined lps = true
  | .app f _, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    exact getAppFn_wellFormed (e := f) h.1
  | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .lam _ _ _, h
  | .forallE _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h => h

private theorem getAppArgs_wellFormed {c : Nat} {env : Ix.Kernel.Env .anon} {lps : List LevelParam} :
    ∀ {e : KExpr},
      e.hasFvar = false →
      e.looseBVarsBounded c = true →
      e.constsResolve env = true →
      e.allLevelParamsDefined lps = true →
      ∀ a ∈ e.getAppArgs,
        a.hasFvar = false ∧
        a.looseBVarsBounded c = true ∧
        a.constsResolve env = true ∧
        a.allLevelParamsDefined lps = true := by
  intro e
  induction e with
  | app f x ihf _ =>
    intro hfv hb hcr hlps a ha
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hlps
    have hargs : (Expr.app f x).getAppArgs = f.getAppArgs ++ [x] := getAppArgs_mkAppN [x] f
    rw [hargs] at ha
    rcases List.mem_append.mp ha with ha' | ha'
    · exact ihf hfv.1 hb.1 hcr.1 hlps.1 a ha'
    · obtain rfl := List.mem_singleton.mp ha'
      exact ⟨hfv.2, hb.2, hcr.2, hlps.2⟩
  | _ =>
    intro _ _ _ _ _ ha
    exact nomatch ha

/-- Assemble `Ix.Kernel.nestedRuleShape` from the major-premise domain decomposition proved by
`rec_major_pins_spec_wide` together with well-formedness of `tyA` in `envSelf`. -/
theorem nestedRuleShape_of_major_pins {env' envSelf : Ix.Kernel.Env .anon}
    {cvName indKey : KKey} {lps : List LevelParam} {tyA dom body : KExpr}
    {bs : List (KExpr × Ix.Kernel.BinderMeta)} {mb : Ix.Kernel.BinderMeta}
    {mI rP cnP j : Nat} {lvls : List KLevel} {cvt : ConstantVal .anon}
    (hcvt : env'.findCV? (auxKey (auxKey cvName .model) (.iota j)) = some cvt)
    (hle : rP ≤ mI)
    (hstrip : tyA.stripPis mI = some (bs, .forallE dom body mb))
    (hfn : dom.getAppFn = .const indKey lvls)
    (hlen : dom.getAppArgs.length = cnP + (mI - rP))
    (hno : ∀ p ∈ dom.getAppArgs.take cnP, noLooseIn 0 (mI - rP) p = true)
    (hdrop : dom.getAppArgs.drop cnP =
      (List.range (mI - rP)).map (fun i => Expr.bvar (mI - rP - 1 - i)))
    (hty_nfv : tyA.hasFvar = false)
    (hty_bvs : tyA.looseBVarsBounded 0 = true)
    (hty_cr : tyA.constsResolve envSelf = true)
    (hty_lps : tyA.allLevelParamsDefined lps = true) :
    Ix.Kernel.nestedRuleShape env' envSelf cvName lps tyA mI rP cnP j =
      some (lvls, (dom.getAppArgs.take cnP).map (Expr.lowerBVars (mI - rP) 0)) := by
  obtain ⟨hrem_nfv, hrem_bvs, hrem_cr, hrem_lps⟩ :=
    stripPis_wellFormed mI hty_nfv hty_bvs hty_cr hty_lps hstrip
  simp only [Nat.zero_add, Expr.hasFvar, Bool.or_eq_false_iff] at hrem_nfv
  simp only [Nat.zero_add, Expr.looseBVarsBounded, Bool.and_eq_true] at hrem_bvs
  simp only [Expr.constsResolve, Bool.and_eq_true] at hrem_cr
  simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hrem_lps
  have hfn_lps : lvls.all (Level.allParamsDefined lps) = true := by
    have h := getAppFn_wellFormed hrem_lps.1.1
    rw [hfn] at h
    exact h
  have hargs_wf := getAppArgs_wellFormed hrem_nfv.1 hrem_bvs.1 hrem_cr.1 hrem_lps.1.1
  have hlift_eq :
      ((dom.getAppArgs.take cnP).map (Expr.lowerBVars (mI - rP) 0)).map
        (Expr.liftLooseBVars (mI - rP) 0) = dom.getAppArgs.take cnP := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id (dom.getAppArgs.take cnP)]
    apply List.map_congr_left
    intro p hp
    exact liftLooseBVars_lowerBVars_of_noLooseIn (hno p hp)
  have hpins_all :
      ((dom.getAppArgs.take cnP).map (Expr.lowerBVars (mI - rP) 0)).all
        (fun p => !p.hasFvar && p.looseBVarsBounded rP &&
          p.constsResolve envSelf && p.allLevelParamsDefined lps) = true := by
    rw [List.all_map, List.all_eq_true]
    intro a ha
    obtain ⟨ha_fv, ha_bvs, ha_cr, ha_lps⟩ := hargs_wf a (List.mem_of_mem_take ha)
    have ha_bvs' : a.looseBVarsBounded (rP + 0 + (mI - rP)) = true := by
      rw [show rP + 0 + (mI - rP) = mI by omega]; exact ha_bvs
    have hp_fv : (a.lowerBVars (mI - rP) 0).hasFvar = false :=
      (hasFvar_lowerBVars (mI - rP) a 0).trans ha_fv
    have hp_bvs : (a.lowerBVars (mI - rP) 0).looseBVarsBounded rP = true := by
      simpa using looseBVarsBounded_lowerBVars (hno a ha) ha_bvs'
    have hp_cr : (a.lowerBVars (mI - rP) 0).constsResolve envSelf = true :=
      (constsResolve_lowerBVars envSelf (mI - rP) a 0).trans ha_cr
    have hp_lps : (a.lowerBVars (mI - rP) 0).allLevelParamsDefined lps = true :=
      (allLevelParamsDefined_lowerBVars (mI - rP) lps a 0).trans ha_lps
    simp [hp_fv, hp_bvs, hp_cr, hp_lps]
  unfold Ix.Kernel.nestedRuleShape
  rw [hcvt, hstrip]
  simp only [Option.isSome_some, true_and, hle]
  rw [ite_eq_left trivial, hfn]
  have hcond :
      dom.getAppArgs.length = cnP + (mI - rP) ∧
      (dom.getAppArgs.take cnP ==
        ((dom.getAppArgs.take cnP).map (Expr.lowerBVars (mI - rP) 0)).map
          (Expr.liftLooseBVars (mI - rP) 0)) = true ∧
      (dom.getAppArgs.drop cnP ==
        (List.range (mI - rP)).map (fun i => Expr.bvar (mI - rP - 1 - i))) = true ∧
      ((dom.getAppArgs.take cnP).map (Expr.lowerBVars (mI - rP) 0)).all
        (fun p => !p.hasFvar && p.looseBVarsBounded rP &&
          p.constsResolve envSelf && p.allLevelParamsDefined lps) = true ∧
      lvls.all (Level.allParamsDefined lps) = true :=
    ⟨hlen, beq_iff_eq.mpr hlift_eq.symm, beq_iff_eq.mpr hdrop, hpins_all, hfn_lps⟩
  exact ite_eq_left hcond

/-- Extract `lvls = cjLps.levelParams.map .param`, `cnP ≤ rP`, and
`pins = (List.range cnP).map (fun k => .bvar (rP - 1 - k))` when `Expr.recRulePlain = true`. -/
theorem recRulePlain_pins_lvls {tyA dom body : KExpr}
    {bs : List (KExpr × Ix.Kernel.BinderMeta)} {mb : Ix.Kernel.BinderMeta}
    {indKey : KKey} {lvls : List KLevel} {mI rP cnP : Nat} {cjLps : List LevelParam}
    (hstrip : tyA.stripPis mI = some (bs, .forallE dom body mb))
    (hfn : dom.getAppFn = .const indKey lvls)
    (hplain : Expr.recRulePlain tyA mI rP cnP cjLps = true) :
    cnP ≤ rP ∧ lvls = cjLps.map .param ∧
      (dom.getAppArgs.take cnP).map (Expr.lowerBVars (mI - rP) 0) =
        (List.range cnP).map (fun k => Expr.bvar (rP - 1 - k)) := by
  unfold Expr.recRulePlain at hplain
  rw [hstrip] at hplain
  dsimp only at hplain
  rw [hfn] at hplain
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hplain
  obtain ⟨⟨hcnp_le, hrp_le⟩, hlvls, htake⟩ := hplain
  refine ⟨hcnp_le, hlvls, ?_⟩
  rw [htake, List.map_map]
  apply List.map_congr_left
  intro k hk
  simp only [List.mem_range] at hk
  simp only [Function.comp_apply, Expr.lowerBVars, Nat.zero_add]
  have hge : mI - 1 - k ≥ mI - rP := by omega
  rw [ite_eq_left hge]
  congr 1; omega

/-! ## `Expr.renameConsts` commutation helpers for `AdviceKeyBridge` -/

theorem openPisAtFvars_renameConsts (π : KKey → KKey) :
    ∀ (m : Nat) (e : KExpr) (i : Nat),
      openPisAtFvars m (e.renameConsts π) i =
        (openPisAtFvars m e i).map (fun p => (p.1.map (·.renameConsts π), p.2.renameConsts π))
  | 0, _, _ => rfl
  | m + 1, .forallE ty body _, i => by
    simp only [Expr.renameConsts, openPisAtFvars]
    have hinst : (body.renameConsts π).instantiate1 (.fvar i (ty.renameConsts π)) =
        (body.instantiate1 (.fvar i ty)).renameConsts π :=
      (Ix.Kernel.Expr.renameConsts_instantiate1 π body 0).symm
    rw [hinst, openPisAtFvars_renameConsts π m _ (i + 1)]
    cases openPisAtFvars m (body.instantiate1 (.fvar i ty)) (i + 1) <;> rfl
  | _ + 1, .bvar _, _ | _ + 1, .fvar _ _, _ | _ + 1, .sort _, _ | _ + 1, .const _ _, _
  | _ + 1, .app _ _, _ | _ + 1, .lam _ _ _, _ | _ + 1, .letE _ _ _ _, _
  | _ + 1, .lit _, _ | _ + 1, .proj _ _ _, _ => rfl

theorem instPisAt_renameConsts (π : KKey → KKey) :
    ∀ (xs : List KExpr) (e : KExpr),
      Expr.instPisAt (xs.map (·.renameConsts π)) (e.renameConsts π) =
        (Expr.instPisAt xs e).map (fun p => (p.1.map (·.renameConsts π), p.2.renameConsts π))
  | [], _ => rfl
  | x :: xs, .forallE ty body _ => by
    simp only [List.map_cons, Expr.renameConsts, Expr.instPisAt]
    have hinst : (body.renameConsts π).instantiate1 (x.renameConsts π) =
        (body.instantiate1 x).renameConsts π :=
      (Ix.Kernel.Expr.renameConsts_instantiate1_gen π body 0).symm
    rw [hinst, instPisAt_renameConsts π xs (body.instantiate1 x)]
    cases Expr.instPisAt xs (body.instantiate1 x) <;> rfl
  | _ :: _, .bvar _ | _ :: _, .fvar _ _ | _ :: _, .sort _ | _ :: _, .const _ _
  | _ :: _, .app _ _ | _ :: _, .lam _ _ _ | _ :: _, .letE _ _ _ _
  | _ :: _, .lit _ | _ :: _, .proj _ _ _ => rfl

theorem instSpine_renameConsts (π : KKey → KKey) :
    ∀ (xs : List KExpr) (t : Nat) (e : KExpr),
      Expr.instSpine (xs.map (·.renameConsts π)) t (e.renameConsts π) =
        (Expr.instSpine xs t e).renameConsts π
  | [], _, _ => rfl
  | x :: xs, t, e => by
    simp only [List.map_cons, Expr.instSpine]
    rw [← Ix.Kernel.Expr.renameConsts_instantiate1_gen]
    exact instSpine_renameConsts π xs (t - 1) (e.instantiate1 x t)

theorem mkAppN_renameConsts (π : KKey → KKey) :
    ∀ (xs : List KExpr) (f : KExpr),
      (Expr.mkAppN f xs).renameConsts π =
        Expr.mkAppN (f.renameConsts π) (xs.map (·.renameConsts π))
  | [], _ => rfl
  | x :: xs, f => mkAppN_renameConsts π xs (.app f x)

theorem getAppFn_renameConsts (π : KKey → KKey) :
    ∀ e : KExpr, (e.renameConsts π).getAppFn = (e.getAppFn).renameConsts π
  | .app f _ => getAppFn_renameConsts π f
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lam _ _ _ | .forallE _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

theorem getAppArgs_renameConsts (π : KKey → KKey) :
    ∀ e : KExpr, (e.renameConsts π).getAppArgs = e.getAppArgs.map (·.renameConsts π)
  | .app f a => by
    have h₁ : (Expr.app f a).getAppArgs = f.getAppArgs ++ [a] := getAppArgs_mkAppN [a] f
    have h₂ : (Expr.app (f.renameConsts π) (a.renameConsts π)).getAppArgs =
        (f.renameConsts π).getAppArgs ++ [a.renameConsts π] :=
      getAppArgs_mkAppN [a.renameConsts π] (f.renameConsts π)
    change (Expr.app (f.renameConsts π) (a.renameConsts π)).getAppArgs = _
    rw [h₂, getAppArgs_renameConsts π f, h₁, List.map_append, List.map_singleton]
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lam _ _ _ | .forallE _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

theorem fvarTypeD_renameConsts (π : KKey → KKey) :
    ∀ e : KExpr, (e.renameConsts π).fvarTypeD = e.fvarTypeD.renameConsts π
  | .fvar _ _ => rfl
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ | .forallE _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

theorem renameConsts_comp_eq_of_constsResolve {env : Ix.Kernel.Env .anon}
    {f₁ f₂ π : KKey → KKey}
    (hagree : ∀ k, (env.find? k).isSome = true → π (f₁ k) = f₂ k) :
    ∀ {e : KExpr}, e.constsResolve env = true →
      (e.renameConsts f₁).renameConsts π = e.renameConsts f₂ := by
  intro e
  induction e with
  | bvar _ | sort _ | lit _ => intro _; rfl
  | fvar i ty ih =>
    intro h; simp only [Expr.constsResolve] at h
    exact congrArg (Expr.fvar i) (ih h)
  | const k us =>
    intro h; simp only [Expr.constsResolve] at h
    exact congrArg (Expr.const · us) (hagree k h)
  | app f a ihf iha =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact congrArg₂ Expr.app (ihf h.1) (iha h.2)
  | lam t b m iht ihb =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp [Expr.renameConsts, iht h.1, ihb h.2]
  | forallE t b m iht ihb =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp [Expr.renameConsts, iht h.1, ihb h.2]
  | letE t v b m iht ihv ihb =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp [Expr.renameConsts, iht h.1.1, ihv h.1.2, ihb h.2]
  | proj s i x ih =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact congrArg (Expr.proj s i) (ih h.2)

/-! ## Algebraic & address-set helpers for `check_iota_rule_vm_spec` -/

/-- `KernelClaim::addr_set_member(t_addr, aset) = 1` over an `AddrMapAll` tree yields membership
in the underlying `advSet` predicate via `RolesSpec.rbtree_map_lookup_or_default_field`. -/
theorem addr_set_member_one {c : Ctx} {advSet : Bytes.Address → Prop} {a : Bytes.Address}
    {t_addr aset : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hroles : RolesSpec) (hwf : c.t.wf = true)
    (ha : Bytes.RepAddressRef addrTy h a t_addr)
    (haset : AddrMapAll addrMapEnum (fun _ k _ => advSet k) h aset)
    (ev : ObsFn W "KernelClaim::addr_set_member" [t_addr, aset] h (.field 1) h' cs) :
    advSet a := by
  obtain ⟨cs4, ev_lkp, _⟩ := Obs.«KernelClaim::addr_set_member».obs ev
  have hfn : Specs.Roles.rbtree_map_lookup_or_default_field (ScopedCtx.unrestricted c)
      [t_addr, aset, .field 0] h (.field 1) h' cs4 :=
    hroles c hwf .rbtree_map_lookup_or_default_field _ _ _ _ _ ev_lkp
  rcases hfn t_addr aset (.field 0) rfl a ha (fun _ k _ => advSet k) haset with h01 | hadv
  · injection h01 with hf
    exact absurd hf one_ne_zero
  · exact hadv

private theorem stripPis_constHead_of_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ (m : Nat) (e : KExpr) {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem : KExpr}
      {Dc : KKey} {usc : List KLevel},
      (e.instantiateLevelParams ks us).stripPis m = some (bs, rem) →
      rem.getAppFn = .const Dc usc →
      ∃ bs₀ rem₀ usc₀, e.stripPis m = some (bs₀, rem₀) ∧ rem₀.getAppFn = .const Dc usc₀ ∧
        Expr.ctorTeleOk e m = true := by
  intro m
  induction m with
  | zero =>
    intro e _ rem Dc usc hs hfn
    injection hs with hp; injection hp with _ hrem; subst hrem
    rw [getAppFn_instantiateLevelParams] at hfn
    cases hgf : e.getAppFn with
    | const Dc₀ usc₀ =>
      rw [hgf] at hfn
      simp only [Expr.instantiateLevelParams, Expr.const.injEq] at hfn
      obtain ⟨rfl, _⟩ := hfn
      exact ⟨[], e, usc₀, rfl, hgf, by simp [Expr.ctorTeleOk, Expr.stripPis, hgf]⟩
    | _ =>
      rw [hgf] at hfn; simp [Expr.instantiateLevelParams] at hfn
  | succ m ih =>
    intro e _ _ Dc usc hs hfn
    cases e with
    | forallE dom body bm =>
      simp only [Expr.instantiateLevelParams, Expr.stripPis] at hs
      cases hsb : (body.instantiateLevelParams ks us).stripPis m with
      | none => simp [hsb] at hs
      | some p =>
        rw [hsb] at hs; injection hs with hp; injection hp with _ hrem; subst hrem
        obtain ⟨bs₀, rem₀, usc₀, hbs₀, hfn₀, _⟩ := ih body hsb hfn
        refine ⟨(dom, bm) :: bs₀, rem₀, usc₀, by simp [Expr.stripPis, hbs₀], hfn₀, ?_⟩
        simp [Expr.ctorTeleOk, Expr.stripPis, hbs₀, hfn₀]
    | _ => simp [Expr.instantiateLevelParams, Expr.stripPis] at hs

private theorem stripPis_renameConsts (π : KKey → KKey) :
    ∀ (m : Nat) (e : KExpr) {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem : KExpr},
      e.stripPis m = some (bs, rem) →
      (e.renameConsts π).stripPis m =
        some (bs.map (fun p => (p.1.renameConsts π, p.2)), rem.renameConsts π) := by
  intro m
  induction m with
  | zero =>
    intro _ _ _ hs
    injection hs with hp; injection hp with h1 h2; subst h1 h2; rfl
  | succ m ih =>
    intro e _ _ hs
    cases e with
    | forallE dom body bm =>
      simp only [Expr.stripPis] at hs
      cases hsb : body.stripPis m with
      | none => simp [hsb] at hs
      | some p =>
        rw [hsb] at hs; injection hs with hp; injection hp with h1 h2; subst h1 h2
        simp [Expr.renameConsts, Expr.stripPis, ih body hsb]
    | _ => nomatch hs

private theorem noProjIn_stripPis {bad : List KKey} :
    ∀ (m : Nat) {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem : KExpr},
      NoProjIn bad e = true → e.stripPis m = some (bs, rem) → NoProjIn bad rem = true := by
  intro m
  induction m with
  | zero =>
    intro _ _ _ hnp hs
    injection hs with hp; injection hp with _ h2; subst h2; exact hnp
  | succ m ih =>
    intro e _ _ hnp hs
    cases e with
    | forallE _ body _ =>
      simp only [NoProjIn, Bool.and_eq_true] at hnp
      simp only [Expr.stripPis] at hs
      cases hsb : body.stripPis m with
      | none => simp [hsb] at hs
      | some p =>
        rw [hsb] at hs; injection hs with hp; injection hp with _ h2; subst h2
        exact ih hnp.2 hsb
    | _ => nomatch hs

private theorem noProjIn_getAppArgs {bad : List KKey} :
    ∀ {e : KExpr}, NoProjIn bad e = true → ∀ a ∈ e.getAppArgs, NoProjIn bad a = true
  | .app f x, hnp, a, ha => by
    simp only [NoProjIn, Bool.and_eq_true] at hnp
    rw [show (Expr.app f x).getAppArgs = f.getAppArgs ++ [x] from getAppArgs_mkAppN [x] f] at ha
    rcases List.mem_append.mp ha with ha' | ha'
    · exact noProjIn_getAppArgs hnp.1 a ha'
    · obtain rfl := List.mem_singleton.mp ha'; exact hnp.2
  | .bvar _, _, _, ha | .fvar _ _, _, _, ha | .sort _, _, _, ha | .const _ _, _, _, ha
  | .lam _ _ _, _, _, ha | .forallE _ _ _, _, _, ha | .letE _ _ _ _, _, _, ha
  | .lit _, _, _, ha | .proj _ _ _, _, _, ha => nomatch ha

private theorem noProjIn_lowerBVars (bad : List KKey) (s : Nat) :
    ∀ (e : KExpr) (c : Nat), NoProjIn bad (e.lowerBVars s c) = NoProjIn bad e
  | .bvar i, c => by simp only [Expr.lowerBVars]; split <;> rfl
  | .fvar _ ty, c => by simp [Expr.lowerBVars, NoProjIn, noProjIn_lowerBVars bad s ty c]
  | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, c => by
    simp [Expr.lowerBVars, NoProjIn, noProjIn_lowerBVars bad s f c, noProjIn_lowerBVars bad s a c]
  | .lam t b _, c | .forallE t b _, c => by
    simp [Expr.lowerBVars, NoProjIn, noProjIn_lowerBVars bad s t c,
      noProjIn_lowerBVars bad s b (c + 1)]
  | .letE t v b _, c => by
    simp [Expr.lowerBVars, NoProjIn, noProjIn_lowerBVars bad s t c,
      noProjIn_lowerBVars bad s v c, noProjIn_lowerBVars bad s b (c + 1)]
  | .proj _ _ x, c => by
    simp [Expr.lowerBVars, NoProjIn, noProjIn_lowerBVars bad s x c]

private theorem lowerBVars_instantiateLevelParams (ks : List LevelParam) (us : List KLevel)
    (s : Nat) :
    ∀ (e : KExpr) (c : Nat),
      (e.instantiateLevelParams ks us).lowerBVars s c =
        (e.lowerBVars s c).instantiateLevelParams ks us
  | .bvar i, c => by simp only [Expr.instantiateLevelParams, Expr.lowerBVars]; split <;> rfl
  | .fvar i ty, c => by
    simp [Expr.instantiateLevelParams, Expr.lowerBVars,
      lowerBVars_instantiateLevelParams ks us s ty c]
  | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, c => by
    simp [Expr.instantiateLevelParams, Expr.lowerBVars,
      lowerBVars_instantiateLevelParams ks us s f c,
      lowerBVars_instantiateLevelParams ks us s a c]
  | .lam t b _, c | .forallE t b _, c => by
    simp [Expr.instantiateLevelParams, Expr.lowerBVars,
      lowerBVars_instantiateLevelParams ks us s t c,
      lowerBVars_instantiateLevelParams ks us s b (c + 1)]
  | .letE t v b _, c => by
    simp [Expr.instantiateLevelParams, Expr.lowerBVars,
      lowerBVars_instantiateLevelParams ks us s t c,
      lowerBVars_instantiateLevelParams ks us s v c,
      lowerBVars_instantiateLevelParams ks us s b (c + 1)]
  | .proj _ _ x, c => by
    simp [Expr.instantiateLevelParams, Expr.lowerBVars,
      lowerBVars_instantiateLevelParams ks us s x c]

private theorem getLastD_eq_of_getElem? {α : Type} :
    ∀ (xs : List α) (n : Nat) (x d : α),
      xs.length = n + 1 → xs[n]? = some x → xs.getLastD d = x
  | [], _, _, _, hlen, _ => nomatch hlen
  | [y], 0, x, _, _, hget => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget; rfl
  | _ :: y :: ys, n + 1, x, d, hlen, hget => by
    have hlen' : (y :: ys).length = n + 1 := Nat.succ.inj hlen
    simp only [List.getElem?_cons_succ] at hget
    exact getLastD_eq_of_getElem? (y :: ys) n x d hlen' hget

private theorem list_find?_name_eq :
    ∀ (cs : List (ConstantInfo .anon)) {k : KKey} {ci : ConstantInfo .anon},
      cs.find? (fun x => x.name == k) = some ci → ci.name = k
  | [], _, _, hf => nomatch hf
  | c :: cs, k, ci, hf => by
    simp only [List.find?_cons] at hf
    cases h : (c.name == k)
    · rw [h] at hf; exact list_find?_name_eq cs hf
    · rw [h] at hf; injection hf with hci; subst hci; exact beq_iff_eq.mp h

private theorem env_find?_name_eq {env : Ix.Kernel.Env .anon} {k : KKey} {ci : ConstantInfo .anon}
    (hf : env.find? k = some ci) : ci.name = k :=
  list_find?_name_eq env.consts hf

/-! ## Unified VM rule judgement records (`RawIotaRuleVmRun`, `RawIotaRulesVmRun`) -/

/-- Unified per-rule output of `KernelModeled::check_iota_rule` across public (`c_pub`), rule-RHS
(`c_rhs`), and advice (`c_adv`) contexts, capturing both canonical and nested rule shapes together
with the advice theorem's universe sort check so `ModeledAux` can construct the `.aux` model
environment and lift directly to `IotaRulesVmRunJ`. -/
structure RawIotaRuleVmRun
    (c_pub c_rhs c_adv : Ctx)
    (blockNames : List KKey) (f_id : KKey → KKey) (advSet : Bytes.Address → Prop)
    (cvName : KKey) (lps : List LevelParam) (tyA : KExpr) (mI rP : Nat)
    (lvls_lps : List KLevel) (pins_lps : List KExpr)
    (j : Nat) (r : RecRule .anon) where
  a_t : Bytes.Address
  hadv_t : advSet a_t
  cvt : ConstantVal .anon
  vt : KExpr
  hfind_t : c_adv.env.find? (c_adv.κ (ixAddr a_t)) = some (.thmInfo cvt vt)
  ht_lps : cvt.levelParams = List.range lps.length
  cvj : ConstantVal .anon
  cnP : Nat
  cnF : Nat
  hfind_ctor : c_pub.env.find? r.ctor = some (.ctorInfo cvj cnP cnF)
  hlvls_len : lvls_lps.length = cvj.levelParams.length
  hpins_len : pins_lps.length = cnP
  hnfields : r.nfields = cnF
  hrhs_bvars : r.rhs.looseBVarsBounded 0 = true
  hrhs_nofvar : r.rhs.hasFvar = false
  hrhs_lvls : r.rhs.allLevelParamsDefined lps = true
  hrhs_lams : (r.rhs.stripLams (rP + cnF)).isSome = true
  hrhs_noproj : NoProjIn blockNames r.rhs = true
  hrhs_cr : r.rhs.constsResolve c_rhs.env = true
  hrhs_typed : ∃ t', posRulesJ.infer c_rhs.env 0 r.rhs t'
  hctor_tele : Expr.ctorTeleOk cvj.type (cnP + cnF) = true
  hctor_head : ∃ cbinders cbody0 Dc usc,
    cvj.type.stripPis (cnP + cnF) = some (cbinders, cbody0) ∧ cbody0.getAppFn = .const Dc usc
  ell_lps : KLevel
  fvs : List KExpr
  tbody : KExpr
  hopen_t : openPisAtFvars (rP + cnF) (invPosOf lps cvt.type) 0 = some (fvs, tbody)
  heq_head : tbody.getAppFn = .const eqName [ell_lps]
  htargs_len : tbody.getAppArgs.length = 3
  hlhs_fn : (tbody.getAppArgs.getD 1 (.bvar 0)).getAppFn = .const (f_id cvName) (lps.map .param)
  hlargs_len : (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs.length = mI + 1
  hlargs_pre : (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs.take rP = fvs.take rP
  hmajor_eq : (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs.getLastD (.bvar 0) =
    Expr.mkAppN (.const (f_id r.ctor) lvls_lps)
      ((pins_lps.map fun p => Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f_id)) ++
        fvs.drop rP)
  cdoms : List KExpr
  cres : KExpr
  hinst_c : Expr.instPisAt
    ((pins_lps.map fun p => Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f_id)) ++
      fvs.drop rP)
    ((cvj.type.instantiateLevelParams cvj.levelParams lvls_lps).renameConsts f_id) =
    some (cdoms, cres)
  hcres_len : cres.getAppArgs.length = cnP + (mI - rP)
  rdoms : List KExpr
  lrest : KExpr
  hinst_r : Expr.instPisAt (fvs.take rP) (tyA.renameConsts f_id) = some (rdoms, lrest)
  fvsP : List KExpr
  crest2 : KExpr
  hopen_p : openPisAtFvars rP tyA 0 = some (fvsP, crest2)
  cdomsP : List KExpr
  crestP : KExpr
  hinst_p : Expr.instPisAt
    (pins_lps.map fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p)
    (cvj.type.instantiateLevelParams cvj.levelParams lvls_lps) = some (cdomsP, crestP)
  xFvsP : List KExpr
  ldoms : KExpr
  hopen_cf : openPisAtFvars cnF crestP rP = some (xFvsP, ldoms)
  hldoms_len : ldoms.getAppArgs.length = cnP + (mI - rP)
  hlam_walk : LamTeleWalkJ posRulesJ c_pub.env rP cnF tyA
    (cvj.type.instantiateLevelParams cvj.levelParams lvls_lps)
    (fun pre => pins_lps.map fun p => Expr.instSpine pre (rP - 1) p) r.rhs
  hpins_typed : TypedListJ posRulesJ c_pub.env (rP + cnF)
    (pins_lps.map fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p) cdomsP
  hruns : IotaRunsVmJ posRulesJ c_adv.env (rP + cnF)
    (((tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs.drop rP).take (mI - rP))
    (cres.getAppArgs.drop cnP)
    ((fvs.drop rP).map Expr.fvarTypeD)
    (cdoms.drop cnP)
    ((fvs.take rP).map Expr.fvarTypeD)
    rdoms
    (tbody.getAppArgs.getD 2 (.bvar 0))
    (Expr.mkAppN (r.rhs.renameConsts f_id) fvs)
    (tbody.getAppArgs.getD 0 (.bvar 0))
    (tbody.getAppArgs.getD 1 (.bvar 0))
  halpha_sort : ∃ ta,
    posRulesJ.infer c_adv.env (rP + cnF) (tbody.getAppArgs.getD 0 (.bvar 0)) ta ∧
    posRulesJ.defeq c_adv.env (rP + cnF) ta (.sort ell_lps)

/-- Rule-list fold of `RawIotaRuleVmRun` produced by `KernelModeled::check_rules_go`. -/
def RawIotaRulesVmRun
    (c_pub c_rhs c_adv : Ctx)
    (blockNames : List KKey) (f_id : KKey → KKey) (advSet : Bytes.Address → Prop)
    (cvName : KKey) (lps : List LevelParam) (tyA : KExpr) (mI rP : Nat)
    (lvls_lps : List KLevel) (pins_lps : List KExpr) :
    Nat → List (RecRule .anon) → Prop
  | _, [] => True
  | j, r :: rest =>
    Nonempty (RawIotaRuleVmRun c_pub c_rhs c_adv blockNames f_id advSet cvName lps tyA mI rP
      lvls_lps pins_lps j r) ∧
      RawIotaRulesVmRun c_pub c_rhs c_adv blockNames f_id advSet cvName lps tyA mI rP
        lvls_lps pins_lps (j + 1) rest

end IxVM.Refinement.Decl
