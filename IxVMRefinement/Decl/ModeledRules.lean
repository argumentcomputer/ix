import IxVMRefinement.Decl.ModeledTele
import IxVMRefinement.Decl.ModeledSound
import IxVMRefinement.Decl.Value
import IxVMRefinement.L1.ByteStream
import IxVMRefinement.L1.Stream
import IxVMRefinement.Core.Specs.Callees
import IxVMRefinement.Obs.KernelClaim0

/-! # Modeled Recursor Rule Verification (`check_iota_rule`, `check_rules_go`, `check_rules`)

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
`check_recursor_canonical_at`, etc.). -/
def CalleesSpec : Prop :=
  ∀ (c : Ctx) (f : Specs.Callees.Fn) (args : List (SourceValue F))
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
  have hra_fn : Specs.Roles.role_addr c [rc, .field (roleNum .eq)] h₁ v_raddr h₂ cs_raddr :=
    hroles c hwf .role_addr _ _ _ _ _ ev_raddr
  obtain ⟨a_tbl, ha_tbl, haddr_of, _⟩ := hra_fn rc .eq rfl hg_raddr hrc
  obtain ⟨heq_f, hh₃⟩ := Lib.address_eq_spec ev_eq ha_eq ha_tbl
  have ha_same : a_eq = a_tbl := by
    by_cases h : a_eq = a_tbl
    · exact h
    · rw [ite_eq_right h] at heq_f
      exact absurd heq_f.symm one_ne_zero
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
  obtain ⟨x_t, vs₁, m₁, c₁, c₂, rfl, dt, atail, rfl⟩ := atup.cons_inv
  obtain ⟨arr_v, m_arr, darr, rfl, hm₁⟩ := dt.store_inv
  obtain ⟨bvals, dvars, rfl⟩ := darr.array_inv
  obtain ⟨hbvals, hm_arr, hcs_vars⟩ := gaVars_inv gaNames xs hb dvars
  subst hm_arr hcs_vars
  obtain ⟨x_s, vs₂, m₂, c₃, c₄, rfl, ds, anil, rfl⟩ := atail.cons_inv
  obtain ⟨ls, rfl, rfl⟩ := ds.var_inv
  rw [hs] at ls
  injection ls with ls; injection ls with _ hxs
  subst hxs
  obtain ⟨rfl, rfl, rfl⟩ := anil.nil_inv
  subst hm₁ hbvals
  let bfn : UInt8 → SourceValue F := fun b => .field (b.toNat : F)
  let a : Bytes.Address := ⟨xs.toArray, by simp [hxlen]⟩
  have halist : a.toList = xs := by simp [a, Vector.toList]
  have hty : (Value.tuple (xs.map bfn) : SourceValue F).type = addrTy := by
    have hrep : ((xs.map bfn).map (fun v : SourceValue F => v.type)) =
        List.replicate 32 .field := by
      apply List.ext_getElem (by simp [hxlen])
      intro k hk₁ hk₂
      rw [List.getElem_map, List.getElem_map, List.getElem_replicate]
      rfl
    unfold Value.type addrTy
    exact congrArg Ty.tuple hrep
  refine ⟨a, .ptr (Value.tuple (xs.map bfn) : SourceValue F).type h.length,
    halist, rfl, ?_, Heap.Extends.snoc h _, rfl⟩
  rw [hty]
  exact ⟨h.length, Value.tuple (xs.map bfn), rfl, by simp, by rw [halist]⟩

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
      (fun _ => by first | rfl | simp [IxVM.IxonDeserialize.get_address]) hs d0
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
      have ext := Heap.Extends.snoc h _
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

/-! ## Direct inversion of `KernelModeled::check_iota_rule` -/

private theorem inv_var_find {locals : Environment F Nat} {name : String} {v expected : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hlkp : locals.find? (·.1 == name) = some (name, expected))
    (ev : ObsExpr W [] locals (.var name) h v h' cs) :
    expected = v ∧ h = h' ∧ cs = [] := by
  obtain ⟨l, hh, hc⟩ := ev.var_inv
  rw [hlkp] at l
  injection l with l; injection l with _ hv
  exact ⟨hv, hh.symm, hc⟩

private theorem inv_store_nil_kexpr {locals : Environment F Nat} {v : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsExpr W [] locals
      (.store (.construct "Lists::Node" (some [.ptr (.named "KernelTypes::KExprNode" [])]) "Nil" []))
      h v h' cs) :
    v = .ptr (.enum kexprListEnum) h.length ∧
      h' = h ++ [.construct kexprListEnum "Nil" []] ∧ cs = [] := by
  obtain ⟨inp, mid, d, rfl, rfl⟩ := ev.store_inv
  obtain ⟨vals, a, hres⟩ := d.construct_inv
  rw [kexprList_inst] at hres
  subst hres
  obtain ⟨rfl, rfl, rfl⟩ := a.nil_inv
  exact ⟨by simp [Value.type], rfl, rfl⟩

/-- Structured record of all intermediate heaps, values, call slices, and sub-derivations extracted
from `ObsFn W "KernelModeled::check_iota_rule"`. -/
structure CheckIotaRuleInv
    (rc rm nl ty_r rp ni rhs cprj cty cnp cnf ilvls pins t_addr src dst aset : SourceValue F)
    (h : Heap F) (calls : List (Call F)) where
  mi : SourceValue F
  d : SourceValue F
  op_mi : evalBinOp .add rp ni = .ok mi
  op_d : evalBinOp .add rp cnf = .ok d
  h_plen : Heap F
  cs_plen : List (Call F)
  call_plen : (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [pins], h⟩ : Call F) ∈ calls
  ev_plen : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [pins] h cnp h_plen cs_plen
  -- stored rule front-end
  v_sc : SourceValue F
  h_sc : Heap F
  cs_sc : List (Call F)
  ev_sc : ObsFn W "KernelCheck::validate_expr_well_scoped" [rhs, .field 0, nl] h_plen v_sc h_sc cs_sc
  sub_sc : SubCalls calls cs_sc
  r_peel_e : SourceValue F
  r_peel_acc : SourceValue F
  h_peel : Heap F
  cs_peel : List (Call F)
  ev_peel : ObsFn W "KernelCheck::peel_n_lams_collect"
    [rhs, d, .field 0, .ptr (.enum kexprListEnum) h_sc.length]
    (h_sc ++ [.construct kexprListEnum "Nil" []])
    (.tuple [r_peel_e, d, r_peel_acc]) h_peel cs_peel
  v_rhs_ty : SourceValue F
  h_rhs_inf : Heap F
  cs_rhs_inf : List (Call F)
  ev_rhs_inf : ObsFn W "KernelInfer::k_infer"
    [rc, rhs, .ptr (.enum kexprListEnum) h_peel.length]
    (h_peel ++ [.construct kexprListEnum "Nil" []]) v_rhs_ty h_rhs_inf cs_rhs_inf
  sub_rhs_inf : SubCalls calls cs_rhs_inf
  -- advice theorem lookup and opening
  h_aset : Heap F
  cs_aset : List (Call F)
  ev_aset : ObsFn W "KernelClaim::addr_set_member" [t_addr, aset] h_rhs_inf (.field 1) h_aset cs_aset
  sub_aset : SubCalls calls cs_aset
  p_tci : SourceValue F
  h_tci : Heap F
  cs_tci : List (Call F)
  ev_tci : ObsFn W "Ingress::get_ci" [t_addr] h_aset p_tci h_tci cs_tci
  sub_tci : SubCalls calls cs_tci
  tty : SourceValue F
  w_tval : SourceValue F
  ld_tci : loadValue h_tci p_tci = .ok (.construct kciEnum "Thm" [nl, tty, w_tval])
  tbody : SourceValue F
  ctx : SourceValue F
  h_open : Heap F
  cs_open : List (Call F)
  ev_open : ObsFn W "KernelModeled::peel_collect"
    [tty, d, .ptr (.enum kexprListEnum) h_tci.length]
    (h_tci ++ [.construct kexprListEnum "Nil" []]) (.tuple [tbody, ctx]) h_open cs_open
  -- equation spine
  eqh : SourceValue F
  targs : SourceValue F
  h_tsp : Heap F
  cs_tsp : List (Call F)
  ev_tsp : ObsFn W "KernelTypes::collect_spine" [tbody] h_open (.tuple [eqh, targs]) h_tsp cs_tsp
  eqa : SourceValue F
  eqls : SourceValue F
  ld_eqh : loadValue h_tsp eqh = .ok (.construct kexprEnum "Const" [eqa, eqls])
  v_req : SourceValue F
  h_req : Heap F
  cs_req : List (Call F)
  v_raddr : SourceValue F
  h_raddr : Heap F
  cs_raddr : List (Call F)
  h_eqa : Heap F
  cs_eqa : List (Call F)
  ev_req : ObsFn W "KernelRoleSpec::role_eq" [] h_tsp v_req h_req cs_req
  ev_raddr : ObsFn W "KernelRoles::role_addr" [rc, v_req] h_req v_raddr h_raddr cs_raddr
  sub_raddr : SubCalls calls cs_raddr
  ev_eqa : ObsFn W "Bytes::address_eq" [eqa, v_raddr] h_raddr (.field 1) h_eqa cs_eqa
  ell : SourceValue F
  eqrest : SourceValue F
  ld_eqls1 : loadValue h_eqa eqls = .ok (.construct klevelListEnum "Cons" [ell, eqrest])
  ld_eqls2 : loadValue h_eqa eqrest = .ok (.construct klevelListEnum "Nil" [])
  h_tlen : Heap F
  cs_tlen : List (Call F)
  call_tlen : (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [targs], h_eqa⟩ : Call F) ∈ calls
  ev_tlen : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [targs] h_eqa (.field 3) h_tlen cs_tlen
  alpha : SourceValue F
  lhs : SourceValue F
  rhs_s : SourceValue F
  h_a0 : Heap F
  cs_a0 : List (Call F)
  h_a1 : Heap F
  cs_a1 : List (Call F)
  h_a2 : Heap F
  cs_a2 : List (Call F)
  ev_a0 : ObsFn W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [targs, .field 0] h_tlen alpha h_a0 cs_a0
  ev_a1 : ObsFn W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [targs, .field 1] h_a0 lhs h_a1 cs_a1
  ev_a2 : ObsFn W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [targs, .field 2] h_a1 rhs_s h_a2 cs_a2
  -- lhs spine, head, prefix, and major
  lh : SourceValue F
  largs : SourceValue F
  h_lsp : Heap F
  cs_lsp : List (Call F)
  ev_lsp : ObsFn W "KernelTypes::collect_spine" [lhs] h_a2 (.tuple [lh, largs]) h_lsp cs_lsp
  v_plvls : SourceValue F
  h_plvls : Heap F
  cs_plvls : List (Call F)
  ev_plvls : ObsFn W "KernelCheck::build_param_lvls_range" [.field 0, nl, .field 0] h_lsp v_plvls h_plvls cs_plvls
  h_lheq : Heap F
  cs_lheq : List (Call F)
  ev_lheq : ObsFn W "KernelCheck::kexpr_struct_eq"
    [lh, .ptr (.enum kexprEnum) h_plvls.length]
    (h_plvls ++ [.construct kexprEnum "Const" [rm, v_plvls]]) (.field 1) h_lheq cs_lheq
  mi1 : SourceValue F
  op_mi1 : evalBinOp .add mi (.field 1) = .ok mi1
  h_llen : Heap F
  cs_llen : List (Call F)
  call_llen : (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [largs], h_lheq⟩ : Call F) ∈ calls
  ev_llen : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [largs] h_lheq mi1 h_llen cs_llen
  v_ltake : SourceValue F
  h_ltake : Heap F
  cs_ltake : List (Call F)
  v_bvd1 : SourceValue F
  h_bvd1 : Heap F
  cs_bvd1 : List (Call F)
  h_pref : Heap F
  cs_pref : List (Call F)
  ev_ltake : ObsFn W Obs.Names.«Lists::take<&KernelTypes::KExprNode>» [largs, rp] h_llen v_ltake h_ltake cs_ltake
  ev_bvd1 : ObsFn W "KernelModeled::bvars_desc" [d, rp] h_ltake v_bvd1 h_bvd1 cs_bvd1
  ev_pref : ObsFn W "KernelCheck::spec_params_ptr_eq" [v_ltake, v_bvd1] h_bvd1 (.field 1) h_pref cs_pref
  major : SourceValue F
  h_maj : Heap F
  cs_maj : List (Call F)
  ev_maj : ObsFn W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [largs, mi] h_pref major h_maj cs_maj
  cren : SourceValue F
  h_cren : Heap F
  cs_cren : List (Call F)
  ev_cren : ObsFn W "KernelModeled::rename_addr" [cprj, src, dst] h_maj cren h_cren cs_cren
  pins_ren : SourceValue F
  h_pren : Heap F
  cs_pren : List (Call F)
  ev_pren : ObsFn W "KernelModeled::rename_list" [pins, src, dst] h_cren pins_ren h_pren cs_pren
  pins_d : SourceValue F
  h_pd : Heap F
  cs_pd : List (Call F)
  ev_pd : ObsFn W "KernelModeled::lift_list" [pins_ren, cnf] h_pren pins_d h_pd cs_pd
  sub_pd : SubCalls calls cs_pd
  v_bvd2 : SourceValue F
  h_bvd2 : Heap F
  cs_bvd2 : List (Call F)
  v_cat : SourceValue F
  h_cat : Heap F
  cs_cat : List (Call F)
  expected : SourceValue F
  h_exp : Heap F
  cs_exp : List (Call F)
  h_majeq : Heap F
  cs_majeq : List (Call F)
  ev_bvd2 : ObsFn W "KernelModeled::bvars_desc" [cnf, cnf]
    (h_pd ++ [.construct kexprEnum "Const" [cren, ilvls]]) v_bvd2 h_bvd2 cs_bvd2
  ev_cat : ObsFn W Obs.Names.«Lists::concat<&KernelTypes::KExprNode>» [pins_d, v_bvd2] h_bvd2 v_cat h_cat cs_cat
  ev_exp : ObsFn W "KernelWhnf::apply_spine"
    [.ptr (.enum kexprEnum) h_pd.length, v_cat] h_cat expected h_exp cs_exp
  ev_majeq : ObsFn W "KernelCheck::kexpr_struct_eq" [major, expected] h_exp (.field 1) h_majeq cs_majeq
  -- constructor telescope and indices
  cty_l : SourceValue F
  h_ctyl : Heap F
  cs_ctyl : List (Call F)
  ev_ctyl : ObsFn W "KernelLevels::expr_inst_levels" [cty, ilvls] h_majeq cty_l h_ctyl cs_ctyl
  sub_ctyl : SubCalls calls cs_ctyl
  cnp_cnf : SourceValue F
  op_cnp_cnf : evalBinOp .add cnp cnf = .ok cnp_cnf
  v_peel0 : SourceValue F
  h_peel0 : Heap F
  cs_peel0 : List (Call F)
  chead0 : SourceValue F
  cargs0 : SourceValue F
  h_csp0 : Heap F
  cs_csp0 : List (Call F)
  ev_peel0 : ObsFn W "KernelCheck::peel_n_foralls" [cty_l, cnp_cnf] h_ctyl v_peel0 h_peel0 cs_peel0
  ev_csp0 : ObsFn W "KernelTypes::collect_spine" [v_peel0] h_peel0 (.tuple [chead0, cargs0]) h_csp0 cs_csp0
  sub_csp0 : SubCalls calls cs_csp0
  w_ch0a : SourceValue F
  w_ch0b : SourceValue F
  ld_chead0 : loadValue h_csp0 chead0 = .ok (.construct kexprEnum "Const" [w_ch0a, w_ch0b])
  v_cty_ren : SourceValue F
  h_cty_ren : Heap F
  cs_cty_ren : List (Call F)
  crest : SourceValue F
  h_crest : Heap F
  cs_crest : List (Call F)
  ev_cty_ren : ObsFn W "KernelModeled::rename" [cty_l, src, dst] h_csp0 v_cty_ren h_cty_ren cs_cty_ren
  ev_crest : ObsFn W "KernelModeled::inst_params" [v_cty_ren, pins_ren] h_cty_ren crest h_crest cs_crest
  sub_crest : SubCalls calls cs_crest
  cres : SourceValue F
  w_cctx : SourceValue F
  h_cres : Heap F
  cs_cres : List (Call F)
  ev_cres : ObsFn W "KernelModeled::peel_collect"
    [crest, cnf, .ptr (.enum kexprListEnum) h_crest.length]
    (h_crest ++ [.construct kexprListEnum "Nil" []]) (.tuple [cres, w_cctx]) h_cres cs_cres
  chead : SourceValue F
  cargs : SourceValue F
  h_csp : Heap F
  cs_csp : List (Call F)
  ev_csp : ObsFn W "KernelTypes::collect_spine" [cres] h_cres (.tuple [chead, cargs]) h_csp cs_csp
  sub_csp : SubCalls calls cs_csp
  w_cha : SourceValue F
  w_chb : SourceValue F
  ld_chead : loadValue h_csp chead = .ok (.construct kexprEnum "Const" [w_cha, w_chb])
  cnp_ni : SourceValue F
  op_cnp_ni : evalBinOp .add cnp ni = .ok cnp_ni
  h_clen : Heap F
  cs_clen : List (Call F)
  call_clen : (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [cargs], h_csp⟩ : Call F) ∈ calls
  ev_clen : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [cargs] h_csp cnp_ni h_clen cs_clen
  v_ldrop : SourceValue F
  h_ldrop : Heap F
  cs_ldrop : List (Call F)
  v_idxl : SourceValue F
  h_idxl : Heap F
  cs_idxl : List (Call F)
  v_idxr : SourceValue F
  h_idxr : Heap F
  cs_idxr : List (Call F)
  h_deidx : Heap F
  cs_deidx : List (Call F)
  ev_ldrop : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [largs, rp] h_clen v_ldrop h_ldrop cs_ldrop
  ev_idxl : ObsFn W Obs.Names.«Lists::take<&KernelTypes::KExprNode>» [v_ldrop, ni] h_ldrop v_idxl h_idxl cs_idxl
  ev_idxr : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [cargs, cnp] h_idxl v_idxr h_idxr cs_idxr
  ev_deidx : ObsFn W "KernelModeled::defeq_list_ok" [rc, v_idxl, v_idxr, ctx] h_idxr (.field 1) h_deidx cs_deidx
  sub_deidx : SubCalls calls cs_deidx
  -- statement domain telescopes
  v_tyr_ren : SourceValue F
  h_tyr_ren : Heap F
  cs_tyr_ren : List (Call F)
  v_dt1 : SourceValue F
  h_dt1 : Heap F
  cs_dt1 : List (Call F)
  ev_tyr_ren : ObsFn W "KernelModeled::rename" [ty_r, src, dst] h_deidx v_tyr_ren h_tyr_ren cs_tyr_ren
  ev_dt1 : ObsFn W "KernelModeled::defeq_tele"
    [rc, tty, v_tyr_ren, rp, .ptr (.enum kexprListEnum) h_tyr_ren.length]
    (h_tyr_ren ++ [.construct kexprListEnum "Nil" []]) v_dt1 h_dt1 cs_dt1
  sub_dt1 : SubCalls calls cs_dt1
  v_tty_rp : SourceValue F
  h_tty_rp : Heap F
  cs_tty_rp : List (Call F)
  v_ctx_rp : SourceValue F
  h_ctx_rp : Heap F
  cs_ctx_rp : List (Call F)
  v_dt2 : SourceValue F
  h_dt2 : Heap F
  cs_dt2 : List (Call F)
  ev_tty_rp : ObsFn W "KernelCheck::peel_n_foralls" [tty, rp] h_dt1 v_tty_rp h_tty_rp cs_tty_rp
  ev_ctx_rp : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [ctx, cnf] h_tty_rp v_ctx_rp h_ctx_rp cs_ctx_rp
  ev_dt2 : ObsFn W "KernelModeled::defeq_tele" [rc, v_tty_rp, crest, cnf, v_ctx_rp] h_ctx_rp v_dt2 h_dt2 cs_dt2
  sub_dt2 : SubCalls calls cs_dt2
  -- public parameter typing and λ-telescope walks
  w_pbody : SourceValue F
  ctx_p : SourceValue F
  h_ctxp : Heap F
  cs_ctxp : List (Call F)
  ev_ctxp : ObsFn W "KernelModeled::peel_collect"
    [ty_r, rp, .ptr (.enum kexprListEnum) h_dt2.length]
    (h_dt2 ++ [.construct kexprListEnum "Nil" []]) (.tuple [w_pbody, ctx_p]) h_ctxp cs_ctxp
  crest_p : SourceValue F
  h_crestp : Heap F
  cs_crestp : List (Call F)
  ev_crestp : ObsFn W "KernelModeled::inst_params_typed" [rc, cty_l, pins, ctx_p] h_ctxp crest_p h_crestp cs_crestp
  sub_crestp : SubCalls calls cs_crestp
  rhs_rp : SourceValue F
  lctx : SourceValue F
  h_lt1 : Heap F
  cs_lt1 : List (Call F)
  ev_lt1 : ObsFn W "KernelModeled::defeq_lam_tele"
    [rc, rhs, ty_r, rp, .ptr (.enum kexprListEnum) h_crestp.length]
    (h_crestp ++ [.construct kexprListEnum "Nil" []]) (.tuple [rhs_rp, lctx]) h_lt1 cs_lt1
  sub_lt1 : SubCalls calls cs_lt1
  w_lt2a : SourceValue F
  w_lt2b : SourceValue F
  h_lt2 : Heap F
  cs_lt2 : List (Call F)
  ev_lt2 : ObsFn W "KernelModeled::defeq_lam_tele" [rc, rhs_rp, crest_p, cnf, lctx] h_lt1 (.tuple [w_lt2a, w_lt2b]) h_lt2 cs_lt2
  sub_lt2 : SubCalls calls cs_lt2
  -- rhs application and defeq
  v_rhs_ren : SourceValue F
  h_rhs_ren : Heap F
  cs_rhs_ren : List (Call F)
  v_bvd3 : SourceValue F
  h_bvd3 : Heap F
  cs_bvd3 : List (Call F)
  rhs_app : SourceValue F
  h_rhsapp : Heap F
  cs_rhsapp : List (Call F)
  h_derhs : Heap F
  cs_derhs : List (Call F)
  ev_rhs_ren : ObsFn W "KernelModeled::rename" [rhs, src, dst] h_lt2 v_rhs_ren h_rhs_ren cs_rhs_ren
  ev_bvd3 : ObsFn W "KernelModeled::bvars_desc" [d, d] h_rhs_ren v_bvd3 h_bvd3 cs_bvd3
  ev_rhsapp : ObsFn W "KernelWhnf::apply_spine" [v_rhs_ren, v_bvd3] h_bvd3 rhs_app h_rhsapp cs_rhsapp
  ev_derhs : ObsFn W "KernelDefEq::k_is_def_eq" [rc, rhs_s, rhs_app, ctx] h_rhsapp (.field 1) h_derhs cs_derhs
  sub_derhs : SubCalls calls cs_derhs
  -- lhs, rhs, and alpha typing
  tl : SourceValue F
  h_tl : Heap F
  cs_tl : List (Call F)
  h_detl : Heap F
  cs_detl : List (Call F)
  tr : SourceValue F
  h_tr : Heap F
  cs_tr : List (Call F)
  h_detr : Heap F
  cs_detr : List (Call F)
  ta : SourceValue F
  h_ta : Heap F
  cs_ta : List (Call F)
  h_deta : Heap F
  cs_deta : List (Call F)
  ev_tl : ObsFn W "KernelInfer::k_infer" [rc, lhs, ctx] h_derhs tl h_tl cs_tl
  sub_tl : SubCalls calls cs_tl
  ev_detl : ObsFn W "KernelDefEq::k_is_def_eq" [rc, tl, alpha, ctx] h_tl (.field 1) h_detl cs_detl
  sub_detl : SubCalls calls cs_detl
  ev_tr : ObsFn W "KernelInfer::k_infer" [rc, rhs_s, ctx] h_detl tr h_tr cs_tr
  sub_tr : SubCalls calls cs_tr
  ev_detr : ObsFn W "KernelDefEq::k_is_def_eq" [rc, tr, alpha, ctx] h_tr (.field 1) h_detr cs_detr
  sub_detr : SubCalls calls cs_detr
  ev_ta : ObsFn W "KernelInfer::k_infer" [rc, alpha, ctx] h_detr ta h_ta cs_ta
  sub_ta : SubCalls calls cs_ta
  ev_deta : ObsFn W "KernelDefEq::k_is_def_eq"
    [rc, ta, .ptr (.enum kexprEnum) h_ta.length, ctx]
    (h_ta ++ [.construct kexprEnum "Srt" [ell]]) (.field 1) h_deta cs_deta
  sub_deta : SubCalls calls cs_deta

private theorem inv_args1 {locals : Environment F Nat} {e₁ : Aiur.Generic.Expr F}
    {h h' : Heap F} {vs : List (SourceValue F)} {cs : List (Call F)}
    (ev : ObsArgs W [] locals [e₁] h vs h' cs) :
    ∃ v₁, vs = [v₁] ∧ ObsExpr W [] locals e₁ h v₁ h' cs := by
  obtain ⟨v₁, _, m₁, c₁, c₂, rfl, d₁, an, rfl⟩ := ev.cons_inv
  obtain ⟨rfl, rfl, rfl⟩ := an.nil_inv
  exact ⟨v₁, rfl, by simpa using d₁⟩

private theorem inv_args2 {locals : Environment F Nat} {e₁ e₂ : Aiur.Generic.Expr F}
    {h h' : Heap F} {vs : List (SourceValue F)} {cs : List (Call F)}
    (ev : ObsArgs W [] locals [e₁, e₂] h vs h' cs) :
    ∃ v₁ v₂ m₁ c₁ c₂, vs = [v₁, v₂] ∧ cs = c₁ ++ c₂ ∧
      ObsExpr W [] locals e₁ h v₁ m₁ c₁ ∧ ObsExpr W [] locals e₂ m₁ v₂ h' c₂ := by
  obtain ⟨v₁, _, m₁, c₁, c₂, rfl, d₁, a₂, rfl⟩ := ev.cons_inv
  obtain ⟨v₂, rfl, d₂⟩ := inv_args1 a₂
  exact ⟨v₁, v₂, m₁, c₁, c₂, rfl, rfl, d₁, d₂⟩

private theorem inv_args3 {locals : Environment F Nat} {e₁ e₂ e₃ : Aiur.Generic.Expr F}
    {h h' : Heap F} {vs : List (SourceValue F)} {cs : List (Call F)}
    (ev : ObsArgs W [] locals [e₁, e₂, e₃] h vs h' cs) :
    ∃ v₁ v₂ v₃ m₁ m₂ c₁ c₂ c₃, vs = [v₁, v₂, v₃] ∧ cs = c₁ ++ (c₂ ++ c₃) ∧
      ObsExpr W [] locals e₁ h v₁ m₁ c₁ ∧ ObsExpr W [] locals e₂ m₁ v₂ m₂ c₂ ∧
      ObsExpr W [] locals e₃ m₂ v₃ h' c₃ := by
  obtain ⟨v₁, _, m₁, c₁, cr, rfl, d₁, ar, rfl⟩ := ev.cons_inv
  obtain ⟨v₂, v₃, m₂, c₂, c₃, rfl, rfl, d₂, d₃⟩ := inv_args2 ar
  exact ⟨v₁, v₂, v₃, m₁, m₂, c₁, c₂, c₃, rfl, rfl, d₁, d₂, d₃⟩

private theorem inv_args4 {locals : Environment F Nat} {e₁ e₂ e₃ e₄ : Aiur.Generic.Expr F}
    {h h' : Heap F} {vs : List (SourceValue F)} {cs : List (Call F)}
    (ev : ObsArgs W [] locals [e₁, e₂, e₃, e₄] h vs h' cs) :
    ∃ v₁ v₂ v₃ v₄ m₁ m₂ m₃ c₁ c₂ c₃ c₄, vs = [v₁, v₂, v₃, v₄] ∧
      cs = c₁ ++ (c₂ ++ (c₃ ++ c₄)) ∧
      ObsExpr W [] locals e₁ h v₁ m₁ c₁ ∧ ObsExpr W [] locals e₂ m₁ v₂ m₂ c₂ ∧
      ObsExpr W [] locals e₃ m₂ v₃ m₃ c₃ ∧ ObsExpr W [] locals e₄ m₃ v₄ h' c₄ := by
  obtain ⟨v₁, _, m₁, c₁, cr, rfl, d₁, ar, rfl⟩ := ev.cons_inv
  obtain ⟨v₂, v₃, v₄, m₂, m₃, c₂, c₃, c₄, rfl, rfl, d₂, d₃, d₄⟩ := inv_args3 ar
  exact ⟨v₁, v₂, v₃, v₄, m₁, m₂, m₃, c₁, c₂, c₃, c₄, rfl, rfl, d₁, d₂, d₃, d₄⟩

private theorem inv_args5 {locals : Environment F Nat} {e₁ e₂ e₃ e₄ e₅ : Aiur.Generic.Expr F}
    {h h' : Heap F} {vs : List (SourceValue F)} {cs : List (Call F)}
    (ev : ObsArgs W [] locals [e₁, e₂, e₃, e₄, e₅] h vs h' cs) :
    ∃ v₁ v₂ v₃ v₄ v₅ m₁ m₂ m₃ m₄ c₁ c₂ c₃ c₄ c₅, vs = [v₁, v₂, v₃, v₄, v₅] ∧
      cs = c₁ ++ (c₂ ++ (c₃ ++ (c₄ ++ c₅))) ∧
      ObsExpr W [] locals e₁ h v₁ m₁ c₁ ∧ ObsExpr W [] locals e₂ m₁ v₂ m₂ c₂ ∧
      ObsExpr W [] locals e₃ m₂ v₃ m₃ c₃ ∧ ObsExpr W [] locals e₄ m₃ v₄ m₄ c₄ ∧
      ObsExpr W [] locals e₅ m₄ v₅ h' c₅ := by
  obtain ⟨v₁, _, m₁, c₁, cr, rfl, d₁, ar, rfl⟩ := ev.cons_inv
  obtain ⟨v₂, v₃, v₄, v₅, m₂, m₃, m₄, c₂, c₃, c₄, c₅, rfl, rfl, d₂, d₃, d₄, d₅⟩ := inv_args4 ar
  exact ⟨v₁, v₂, v₃, v₄, v₅, m₁, m₂, m₃, m₄, c₁, c₂, c₃, c₄, c₅, rfl, rfl, d₁, d₂, d₃, d₄, d₅⟩

private theorem inv_match_kexpr_const_unit {locals : Environment F Nat} {scr : String}
    {ptr : SourceValue F} {rest : Aiur.Generic.Expr F} {h h' : Heap F}
    {r : SourceValue F} {cs : List (Call F)} {calls : List (Call F)}
    (hlkp : locals.find? (·.1 == scr) = some (scr, ptr))
    (sc : SubCalls calls cs)
    (ev : ObsExpr W [] locals
      (.letValue .wildcard
        (.matchValue (.load (.var scr))
          [(.construct (.named "KernelTypes::KExprNode" []) "Const" [.wildcard, .wildcard], .tuple [])])
        rest) h r h' cs) :
    ∃ w₁ w₂ cs_rest,
      loadValue h ptr = .ok (.construct kexprEnum "Const" [w₁, w₂]) ∧
      SubCalls calls cs_rest ∧
      ObsExpr W [] locals rest h r h' cs_rest := by
  obtain ⟨_, m₁, _, c₁, cs_rest, dm, mt_w, drest, hc⟩ := ev.letValue_inv
  rw [hc] at sc
  obtain rfl := matchPattern_wildcard_inv mt_w
  obtain ⟨_, m_ld, _, _, _, _, dld, sel, darm, _⟩ := dm.matchValue_inv
  obtain ⟨_, dv, ld⟩ := dld.load_inv
  obtain ⟨rfl, rfl, _⟩ := inv_var_find hlkp dv
  rcases selectArm_cons_inv sel with ⟨mt_c, rfl⟩ | ⟨nm_c, sel_nil⟩
  · obtain ⟨vs, hv, -, ml₁⟩ := matchPattern_construct_inv mt_c
    rw [kexpr_ctor] at hv; subst hv
    obtain ⟨w₁, _, _, _, rfl, mtw₁, ml₂, rfl⟩ := matchListWith_cons_inv ml₁
    obtain rfl := matchPattern_wildcard_inv mtw₁
    obtain ⟨w₂, _, _, _, rfl, mtw₂, ml₃, rfl⟩ := matchListWith_cons_inv ml₂
    obtain rfl := matchPattern_wildcard_inv mtw₂
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml₃
    obtain ⟨_, a_tup, rfl⟩ := darm.tuple_inv
    obtain ⟨rfl, rfl, _⟩ := a_tup.nil_inv
    exact ⟨w₁, w₂, cs_rest, ld, sc.append_right, drest⟩
  · exact (selectArm_nil_inv sel_nil).elim

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
/-- Direct expression-level inversion of `KernelModeled::check_iota_rule`. -/
theorem check_iota_rule_inv
    {rc rm nl ty_r rp ni rhs cprj cty cnp cnf ilvls pins t_addr src dst aset r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelModeled::check_iota_rule"
      [rc, rm, nl, ty_r, rp, ni, rhs, cprj, cty, cnp, cnf, ilvls, pins, t_addr, src, dst, aset]
      h r h' calls) :
    Nonempty (CheckIotaRuleInv rc rm nl ty_r rp ni rhs cprj cty cnp cnf ilvls pins t_addr src dst aset h calls) := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelModeled.check_iota_rule.lookup
    (by simp [IxVM.KernelModeled.check_iota_rule, ControlLower.hasControl]) ev
  simp only [IxVM.KernelModeled.check_iota_rule] at d0
  have hcalls₀ : ∃ calls₀, calls₀ = calls ∧ SubCalls calls₀ calls :=
    ⟨calls, rfl, SubCalls.refl calls⟩
  obtain ⟨calls₀, hcalls₀_eq, sc0⟩ := hcalls₀
  -- 1. `let mi = rp + ni`
  obtain ⟨mi, _, _, _, _, d1, mt1, rest1, hc1⟩ := d0.letValue_inv; clear d0
  rw [hc1] at sc0; have sc1 := sc0.append_right; clear sc0 hc1
  obtain ⟨_, _, _, _, _, dl1, dr1, op_mi, _⟩ := d1.binary_inv
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) dl1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) dr1
  obtain rfl := matchPattern_bind_inv mt1
  -- 2. `let d = rp + cnf`
  obtain ⟨d, _, _, _, _, d2, mt2, rest2, hc2⟩ := rest1.letValue_inv; clear rest1
  rw [hc2] at sc1; have sc2 := sc1.append_right; clear sc1 hc2
  obtain ⟨_, _, _, _, _, dl2, dr2, op_d, _⟩ := d2.binary_inv
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) dl2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) dr2
  obtain rfl := matchPattern_bind_inv mt2
  -- 3. `assert_eq!(Lists::length(pins), cnp)`
  obtain ⟨_, _, _, c3a, _, d3, mt3, rest3, hc3⟩ := rest2.letValue_inv; clear rest2
  rw [hc3] at sc2; have sc3_l := sc2.append_left; have sc3 := sc2.append_right; clear sc2 hc3
  obtain ⟨_, a3, ap3⟩ := d3.builtin_inv
  obtain ⟨v3_l, v3_r, h_plen, c3_l, c3_r, rfl, hc3_args, d3_l, d3_r⟩ := inv_args2 a3
  obtain ⟨_, _, _, cs_plen, a3_la, ev_plen, hc_plen⟩ := d3_l.call_inv
  rw [Obs.Names.n6682477127133607924] at ev_plen hc_plen
  obtain ⟨_, rfl, d3_lv⟩ := inv_args1 a3_la
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d3_lv
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d3_r
  obtain ⟨heq3, rfl⟩ := Builtin.assertEq_inv ap3; subst v3_l
  obtain rfl := matchPattern_wildcard_inv mt3
  rw [hc3_args, hc_plen] at sc3_l
  have call_plen := sc3_l.append_left.append_right.cons_head
  clear sc3_l hc3_args hc_plen
  -- 4. `KernelCheck::validate_expr_well_scoped(rhs, 0, nl)`
  obtain ⟨v_sc, h_sc, _, c4a, _, d4, mt4, rest4, hc4⟩ := rest3.letValue_inv; clear rest3
  rw [hc4] at sc3; have sc4_l := sc3.append_left; have sc4 := sc3.append_right; clear sc3 hc4
  obtain ⟨_, _, _, cs_sc, a4, ev_sc, hc_sc⟩ := d4.call_inv
  rw [instanceName_plain_some] at ev_sc hc_sc
  obtain ⟨_, _, _, _, _, _, _, _, rfl, hc4_args, d4_1, d4_2, d4_3⟩ := inv_args3 a4
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d4_1
  obtain ⟨rfl, rfl, rfl⟩ := d4_2.literal_inv
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d4_3
  obtain rfl := matchPattern_wildcard_inv mt4
  rw [hc_sc, hc4_args] at sc4_l
  have sub_sc := sc4_l.append_right.cons_tail
  clear sc4_l hc_sc hc4_args
  -- 5. `let (_, peeled, _) = KernelCheck::peel_n_lams_collect(rhs, d, 0, (&(Lists::Node::Nil)))`
  obtain ⟨_, h_peel, _, _, _, d5, mt5, rest5, hc5⟩ := rest4.letValue_inv; clear rest4
  rw [hc5] at sc4; have sc5 := sc4.append_right; clear sc4 hc5
  obtain ⟨_, _, _, cs_peel, a5, ev_peel, _⟩ := d5.call_inv
  rw [instanceName_plain_some] at ev_peel
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, d5_1, d5_2, d5_3, d5_4⟩ := inv_args4 a5
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d5_1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d5_2
  obtain ⟨rfl, rfl, _⟩ := d5_3.literal_inv
  obtain ⟨rfl, rfl, _⟩ := inv_store_nil_kexpr d5_4
  obtain ⟨_, hv5, -, ml5a⟩ := matchPattern_tuple_inv mt5; subst hv5
  obtain ⟨r_peel_e, _, _, _, rfl, mt5_1, ml5b, rfl⟩ := matchListWith_cons_inv ml5a
  obtain rfl := matchPattern_wildcard_inv mt5_1
  obtain ⟨peeled_v, _, _, _, rfl, mt5_2, ml5c, rfl⟩ := matchListWith_cons_inv ml5b
  obtain rfl := matchPattern_bind_inv mt5_2
  obtain ⟨r_peel_acc, _, _, _, rfl, mt5_3, ml5d, rfl⟩ := matchListWith_cons_inv ml5c
  obtain rfl := matchPattern_wildcard_inv mt5_3
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml5d
  -- 6. `assert_eq!(peeled, d)`
  obtain ⟨_, _, _, _, _, d6, mt6, rest6, hc6⟩ := rest5.letValue_inv; clear rest5
  rw [hc6] at sc5; have sc6 := sc5.append_right; clear sc5 hc6
  obtain ⟨_, a6, ap6⟩ := d6.builtin_inv
  obtain ⟨_, _, _, _, _, rfl, _, d6_1, d6_2⟩ := inv_args2 a6
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d6_1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d6_2
  obtain ⟨heq6, rfl⟩ := Builtin.assertEq_inv ap6; subst peeled_v
  obtain rfl := matchPattern_wildcard_inv mt6
  -- 7. `KernelInfer::k_infer(rc, rhs, (&(Lists::Node::Nil)))`
  obtain ⟨v_rhs_ty, h_rhs_inf, _, c7a, _, d7, mt7, rest7, hc7⟩ := rest6.letValue_inv; clear rest6
  rw [hc7] at sc6; have sc7_l := sc6.append_left; have sc7 := sc6.append_right; clear sc6 hc7
  obtain ⟨_, _, _, cs_rhs_inf, a7, ev_rhs_inf, hc_rhs_inf⟩ := d7.call_inv
  rw [instanceName_plain_some] at ev_rhs_inf hc_rhs_inf
  obtain ⟨_, _, _, _, _, _, _, _, rfl, hc7_args, d7_1, d7_2, d7_3⟩ := inv_args3 a7
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d7_1
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d7_2
  obtain ⟨rfl, rfl, rfl⟩ := inv_store_nil_kexpr d7_3
  obtain rfl := matchPattern_wildcard_inv mt7
  rw [hc_rhs_inf, hc7_args] at sc7_l
  have sub_rhs_inf := sc7_l.append_right.cons_tail
  clear sc7_l hc_rhs_inf hc7_args
  -- 8. `assert_eq!(KernelClaim::addr_set_member(t, aset), 1)`
  obtain ⟨_, h_aset, _, c8a, _, d8, mt8, rest8, hc8⟩ := rest7.letValue_inv; clear rest7
  rw [hc8] at sc7; have sc8_l := sc7.append_left; have sc8 := sc7.append_right; clear sc7 hc8
  obtain ⟨_, a8, ap8⟩ := d8.builtin_inv
  obtain ⟨v_aset_m, _, _, c8_l, c8_r, rfl, hc8_args, d8_1, d8_2⟩ := inv_args2 a8
  obtain ⟨_, _, _, cs_aset, a8_c, ev_aset, hc_aset⟩ := d8_1.call_inv
  rw [instanceName_plain_some] at ev_aset hc_aset
  obtain ⟨_, _, _, _, _, rfl, hc8_cargs, d8_c1, d8_c2⟩ := inv_args2 a8_c
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d8_c1
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d8_c2
  obtain ⟨rfl, rfl, rfl⟩ := d8_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap8
  obtain rfl := matchPattern_wildcard_inv mt8
  rw [hc8_args, hc_aset, hc8_cargs] at sc8_l
  have sub_aset := sc8_l.append_left.append_right.cons_tail
  clear sc8_l hc8_args hc_aset hc8_cargs
  -- 9. `match (*(Ingress::get_ci(t))) { KernelTypes::KConstantInfo::Thm(tnl, tty, _) => { ... } }`
  obtain ⟨_, h_tci, _, _, c9a, c9b, d9_scr, sel9, rest9, hc9⟩ := rest8.matchValue_inv; clear rest8
  rw [hc9] at sc8; have sc9_l := sc8.append_left; have sc9 := sc8.append_right; clear sc8 hc9
  obtain ⟨p_tci, d9_call, ld_tci⟩ := d9_scr.load_inv
  obtain ⟨_, _, _, cs_tci, a9, ev_tci, hc_tci⟩ := d9_call.call_inv
  rw [instanceName_plain_some] at ev_tci hc_tci
  obtain ⟨_, rfl, d9_t⟩ := inv_args1 a9
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d9_t
  rw [hc_tci] at sc9_l
  have sub_tci := sc9_l.append_right.cons_tail
  clear sc9_l hc_tci
  rcases selectArm_cons_inv sel9 with ⟨mt9, rfl⟩ | ⟨_, sel9_nil⟩
  swap; · exact (selectArm_nil_inv sel9_nil).elim
  obtain ⟨_, hv9, -, ml9a⟩ := matchPattern_construct_inv mt9
  rw [Obs.Names.n11677430323439928978] at hv9; subst hv9
  obtain ⟨tnl, _, _, _, rfl, mt9_1, ml9b, rfl⟩ := matchListWith_cons_inv ml9a
  obtain rfl := matchPattern_bind_inv mt9_1
  obtain ⟨tty, _, _, _, rfl, mt9_2, ml9c, rfl⟩ := matchListWith_cons_inv ml9b
  obtain rfl := matchPattern_bind_inv mt9_2
  obtain ⟨w_tval, _, _, _, rfl, mt9_3, ml9d, rfl⟩ := matchListWith_cons_inv ml9c
  obtain rfl := matchPattern_wildcard_inv mt9_3
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml9d
  -- 10. `assert_eq!(tnl, nl)`
  obtain ⟨_, _, _, _, _, d10, mt10, rest10, hc10⟩ := rest9.letValue_inv; clear rest9
  rw [hc10] at sc9; have sc10 := sc9.append_right; clear sc9 hc10
  obtain ⟨_, a10, ap10⟩ := d10.builtin_inv
  obtain ⟨_, _, _, _, _, rfl, _, d10_1, d10_2⟩ := inv_args2 a10
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d10_1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d10_2
  obtain ⟨heq10, rfl⟩ := Builtin.assertEq_inv ap10; subst tnl
  obtain rfl := matchPattern_wildcard_inv mt10
  -- 11. `let (tbody, ctx) = peel_collect(tty, d, (&(Lists::Node::Nil)))`
  obtain ⟨_, h_open, _, _, _, d11, mt11, rest11, hc11⟩ := rest10.letValue_inv; clear rest10
  rw [hc11] at sc10; have sc11 := sc10.append_right; clear sc10 hc11
  obtain ⟨_, _, _, cs_open, a11, ev_open, _⟩ := d11.call_inv
  rw [instanceName_plain_some] at ev_open
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d11_1, d11_2, d11_3⟩ := inv_args3 a11
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d11_1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d11_2
  obtain ⟨rfl, rfl, _⟩ := inv_store_nil_kexpr d11_3
  obtain ⟨_, hv11, -, ml11a⟩ := matchPattern_tuple_inv mt11; subst hv11
  obtain ⟨tbody, _, _, _, rfl, mt11_1, ml11b, rfl⟩ := matchListWith_cons_inv ml11a
  obtain rfl := matchPattern_bind_inv mt11_1
  obtain ⟨ctx, _, _, _, rfl, mt11_2, ml11c, rfl⟩ := matchListWith_cons_inv ml11b
  obtain rfl := matchPattern_bind_inv mt11_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml11c
  -- 12. `let (eqh, targs) = KernelTypes::collect_spine(tbody)`
  obtain ⟨_, h_tsp, _, _, _, d12, mt12, rest12, hc12⟩ := rest11.letValue_inv; clear rest11
  rw [hc12] at sc11; have sc12 := sc11.append_right; clear sc11 hc12
  obtain ⟨_, _, _, cs_tsp, a12, ev_tsp, _⟩ := d12.call_inv
  rw [instanceName_plain_some] at ev_tsp
  obtain ⟨_, rfl, d12_1⟩ := inv_args1 a12
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d12_1
  obtain ⟨_, hv12, -, ml12a⟩ := matchPattern_tuple_inv mt12; subst hv12
  obtain ⟨eqh, _, _, _, rfl, mt12_1, ml12b, rfl⟩ := matchListWith_cons_inv ml12a
  obtain rfl := matchPattern_bind_inv mt12_1
  obtain ⟨targs, _, _, _, rfl, mt12_2, ml12c, rfl⟩ := matchListWith_cons_inv ml12b
  obtain rfl := matchPattern_bind_inv mt12_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml12c
  -- 13. `match (*(eqh)) { KernelTypes::KExprNode::Const(eqa, eqls) => { ... } }`
  obtain ⟨_, _, _, _, _, _, d13_scr, sel13, rest13, hc13⟩ := rest12.matchValue_inv; clear rest12
  rw [hc13] at sc12; have sc13 := sc12.append_right; clear sc12 hc13
  obtain ⟨_, d13_v, ld_eqh⟩ := d13_scr.load_inv
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d13_v
  rcases selectArm_cons_inv sel13 with ⟨mt13, rfl⟩ | ⟨_, sel13_nil⟩
  swap; · exact (selectArm_nil_inv sel13_nil).elim
  obtain ⟨_, hv13, -, ml13a⟩ := matchPattern_construct_inv mt13
  rw [kexpr_ctor] at hv13; subst hv13
  obtain ⟨eqa, _, _, _, rfl, mt13_1, ml13b, rfl⟩ := matchListWith_cons_inv ml13a
  obtain rfl := matchPattern_bind_inv mt13_1
  obtain ⟨eqls, _, _, _, rfl, mt13_2, ml13c, rfl⟩ := matchListWith_cons_inv ml13b
  obtain rfl := matchPattern_bind_inv mt13_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml13c
  -- 14. `assert_eq!(Bytes::address_eq(eqa, KernelRoles::role_addr(rc, KernelRoleSpec::role_eq())), 1)`
  obtain ⟨_, h_eqa, _, c14a, _, d14, mt14, rest14, hc14⟩ := rest13.letValue_inv; clear rest13
  rw [hc14] at sc13; have sc14_l := sc13.append_left; have sc14 := sc13.append_right; clear sc13 hc14
  obtain ⟨_, a14, ap14⟩ := d14.builtin_inv
  obtain ⟨_, _, _, c14_l, _, rfl, hc14_args, d14_1, d14_2⟩ := inv_args2 a14
  obtain ⟨_, h_raddr, c14_eqa, cs_eqa, a14_eq, ev_eqa, hc_eqa⟩ := d14_1.call_inv
  rw [instanceName_plain_some] at ev_eqa hc_eqa
  obtain ⟨_, v_raddr, _, c14_ea1, c14_ea2, rfl, hc14_ea, d14_eqa, d14_ra⟩ := inv_args2 a14_eq
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d14_eqa
  obtain ⟨_, h_req, c14_raa, cs_raddr, a14_ra, ev_raddr, hc_raddr⟩ := d14_ra.call_inv
  rw [instanceName_plain_some] at ev_raddr hc_raddr
  obtain ⟨_, v_req, _, _, c14_req, rfl, hc14_raa, d14_rc, d14_req⟩ := inv_args2 a14_ra
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d14_rc
  obtain ⟨_, _, _, cs_req, a14_req, ev_req, _⟩ := d14_req.call_inv
  rw [instanceName_plain_some] at ev_req
  obtain ⟨rfl, rfl, rfl⟩ := a14_req.nil_inv
  obtain ⟨rfl, rfl, rfl⟩ := d14_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap14
  obtain rfl := matchPattern_wildcard_inv mt14
  rw [hc14_args, hc_eqa, hc14_ea, hc_raddr] at sc14_l
  have sub_raddr :=
    sc14_l.append_left.append_left.append_right.append_right.cons_tail
  clear sc14_l hc14_args hc_eqa hc14_ea hc_raddr hc14_raa
  -- 15. `let Lists::Node::Cons(ell, eqrest) = (*(eqls))`
  obtain ⟨_, _, _, _, _, d15, mt15, rest15, hc15⟩ := rest14.letValue_inv; clear rest14
  rw [hc15] at sc14; have sc15 := sc14.append_right; clear sc14 hc15
  obtain ⟨_, d15_v, ld_eqls1⟩ := d15.load_inv
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d15_v
  obtain ⟨_, hv15, -, ml15a⟩ := matchPattern_construct_inv mt15
  rw [klevelList_ctor] at hv15; subst hv15
  obtain ⟨ell, _, _, _, rfl, mt15_1, ml15b, rfl⟩ := matchListWith_cons_inv ml15a
  obtain rfl := matchPattern_bind_inv mt15_1
  obtain ⟨eqrest, _, _, _, rfl, mt15_2, ml15c, rfl⟩ := matchListWith_cons_inv ml15b
  obtain rfl := matchPattern_bind_inv mt15_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml15c
  -- 16. `let Lists::Node::Nil = (*(eqrest))`
  obtain ⟨_, _, _, _, _, d16, mt16, rest16, hc16⟩ := rest15.letValue_inv; clear rest15
  rw [hc16] at sc15; have sc16 := sc15.append_right; clear sc15 hc16
  obtain ⟨_, d16_v, ld_eqls2⟩ := d16.load_inv
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d16_v
  obtain ⟨_, hv16, -, ml16⟩ := matchPattern_construct_inv mt16
  rw [klevelList_ctor] at hv16; subst hv16
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml16
  -- 17. `assert_eq!(Lists::length(targs), 3)`
  obtain ⟨_, h_tlen, _, c17a, _, d17, mt17, rest17, hc17⟩ := rest16.letValue_inv; clear rest16
  rw [hc17] at sc16; have sc17_l := sc16.append_left; have sc17 := sc16.append_right; clear sc16 hc17
  obtain ⟨_, a17, ap17⟩ := d17.builtin_inv
  obtain ⟨_, _, _, c17_l, _, rfl, hc17_args, d17_1, d17_2⟩ := inv_args2 a17
  obtain ⟨_, _, _, cs_tlen, a17_c, ev_tlen, hc_tlen⟩ := d17_1.call_inv
  rw [Obs.Names.n6682477127133607924] at ev_tlen hc_tlen
  obtain ⟨_, rfl, d17_v⟩ := inv_args1 a17_c
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d17_v
  obtain ⟨rfl, rfl, rfl⟩ := d17_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap17
  obtain rfl := matchPattern_wildcard_inv mt17
  rw [hc17_args, hc_tlen] at sc17_l
  have call_tlen := sc17_l.append_left.append_right.cons_head
  clear sc17_l hc17_args hc_tlen
  -- 18. `let alpha = Lists::lookup(targs, 0)`
  obtain ⟨alpha, h_a0, _, _, _, d18, mt18, rest18, hc18⟩ := rest17.letValue_inv; clear rest17
  rw [hc18] at sc17; have sc18 := sc17.append_right; clear sc17 hc18
  obtain ⟨_, _, _, cs_a0, a18, ev_a0, _⟩ := d18.call_inv
  rw [Obs.Names.n11123572196661760086] at ev_a0
  obtain ⟨_, _, _, _, _, rfl, _, d18_1, d18_2⟩ := inv_args2 a18
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d18_1
  obtain ⟨rfl, rfl, _⟩ := d18_2.literal_inv
  obtain rfl := matchPattern_bind_inv mt18
  -- 19. `let lhs = Lists::lookup(targs, 1)`
  obtain ⟨lhs, h_a1, _, _, _, d19, mt19, rest19, hc19⟩ := rest18.letValue_inv; clear rest18
  rw [hc19] at sc18; have sc19 := sc18.append_right; clear sc18 hc19
  obtain ⟨_, _, _, cs_a1, a19, ev_a1, _⟩ := d19.call_inv
  rw [Obs.Names.n11123572196661760086] at ev_a1
  obtain ⟨_, _, _, _, _, rfl, _, d19_1, d19_2⟩ := inv_args2 a19
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d19_1
  obtain ⟨rfl, rfl, _⟩ := d19_2.literal_inv
  obtain rfl := matchPattern_bind_inv mt19
  -- 20. `let rhs_s = Lists::lookup(targs, 2)`
  obtain ⟨rhs_s, h_a2, _, _, _, d20, mt20, rest20, hc20⟩ := rest19.letValue_inv; clear rest19
  rw [hc20] at sc19; have sc20 := sc19.append_right; clear sc19 hc20
  obtain ⟨_, _, _, cs_a2, a20, ev_a2, _⟩ := d20.call_inv
  rw [Obs.Names.n11123572196661760086] at ev_a2
  obtain ⟨_, _, _, _, _, rfl, _, d20_1, d20_2⟩ := inv_args2 a20
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d20_1
  obtain ⟨rfl, rfl, _⟩ := d20_2.literal_inv
  obtain rfl := matchPattern_bind_inv mt20
  -- 21. `let (lh, largs) = KernelTypes::collect_spine(lhs)`
  obtain ⟨_, h_lsp, _, _, _, d21, mt21, rest21, hc21⟩ := rest20.letValue_inv; clear rest20
  rw [hc21] at sc20; have sc21 := sc20.append_right; clear sc20 hc21
  obtain ⟨_, _, _, cs_lsp, a21, ev_lsp, _⟩ := d21.call_inv
  rw [instanceName_plain_some] at ev_lsp
  obtain ⟨_, rfl, d21_1⟩ := inv_args1 a21
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d21_1
  obtain ⟨_, hv21, -, ml21a⟩ := matchPattern_tuple_inv mt21; subst hv21
  obtain ⟨lh, _, _, _, rfl, mt21_1, ml21b, rfl⟩ := matchListWith_cons_inv ml21a
  obtain rfl := matchPattern_bind_inv mt21_1
  obtain ⟨largs, _, _, _, rfl, mt21_2, ml21c, rfl⟩ := matchListWith_cons_inv ml21b
  obtain rfl := matchPattern_bind_inv mt21_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml21c
  -- 22. `let rhead = (&(KernelTypes::KExprNode::Const(rm, KernelCheck::build_param_lvls_range(0, nl, 0))))`
  obtain ⟨_, _, _, _, _, d22, mt22, rest22, hc22⟩ := rest21.letValue_inv; clear rest21
  rw [hc22] at sc21; have sc22 := sc21.append_right; clear sc21 hc22
  obtain ⟨inp22, h_plvls, d22_c, rfl, rfl⟩ := d22.store_inv
  obtain ⟨_, a22_c, hres22⟩ := d22_c.construct_inv
  rw [instanceName_plain_some] at hres22; subst hres22
  obtain ⟨_, v_plvls, _, _, _, rfl, _, d22_rm, d22_pl⟩ := inv_args2 a22_c
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d22_rm
  obtain ⟨_, _, _, cs_plvls, a22_pl, ev_plvls, _⟩ := d22_pl.call_inv
  rw [instanceName_plain_some] at ev_plvls
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d22_p1, d22_p2, d22_p3⟩ := inv_args3 a22_pl
  obtain ⟨rfl, rfl, _⟩ := d22_p1.literal_inv
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d22_p2
  obtain ⟨rfl, rfl, _⟩ := d22_p3.literal_inv
  obtain rfl := matchPattern_bind_inv mt22
  -- 23. `assert_eq!(KernelCheck::kexpr_struct_eq(lh, rhead), 1)`
  obtain ⟨_, h_lheq, _, _, _, d23, mt23, rest23, hc23⟩ := rest22.letValue_inv; clear rest22
  rw [hc23] at sc22; have sc23 := sc22.append_right; clear sc22 hc23
  obtain ⟨_, a23, ap23⟩ := d23.builtin_inv
  obtain ⟨_, _, _, _, _, rfl, _, d23_1, d23_2⟩ := inv_args2 a23
  obtain ⟨_, _, _, cs_lheq, a23_c, ev_lheq, _⟩ := d23_1.call_inv
  rw [instanceName_plain_some] at ev_lheq
  obtain ⟨_, _, _, _, _, rfl, _, d23_c1, d23_c2⟩ := inv_args2 a23_c
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d23_c1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d23_c2
  obtain ⟨rfl, rfl, _⟩ := d23_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap23
  simp only [Value.type] at ev_lheq
  obtain rfl := matchPattern_wildcard_inv mt23
  -- 24. `assert_eq!(Lists::length(largs), mi + 1)`
  obtain ⟨_, h_llen, _, c24a, _, d24, mt24, rest24, hc24⟩ := rest23.letValue_inv; clear rest23
  rw [hc24] at sc23; have sc24_l := sc23.append_left; have sc24 := sc23.append_right; clear sc23 hc24
  obtain ⟨_, a24, ap24⟩ := d24.builtin_inv
  obtain ⟨v_llen, mi1, _, c24_l, _, rfl, hc24_args, d24_1, d24_2⟩ := inv_args2 a24
  obtain ⟨_, _, _, cs_llen, a24_c, ev_llen, hc_llen⟩ := d24_1.call_inv
  rw [Obs.Names.n6682477127133607924] at ev_llen hc_llen
  obtain ⟨_, rfl, d24_v⟩ := inv_args1 a24_c
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d24_v
  obtain ⟨_, _, _, _, _, d24_b1, d24_b2, op_mi1, _⟩ := d24_2.binary_inv
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d24_b1
  obtain ⟨rfl, rfl, _⟩ := d24_b2.literal_inv
  obtain ⟨heq24, rfl⟩ := Builtin.assertEq_inv ap24; subst v_llen
  obtain rfl := matchPattern_wildcard_inv mt24
  rw [hc24_args, hc_llen] at sc24_l
  have call_llen := sc24_l.append_left.append_right.cons_head
  clear sc24_l hc24_args hc_llen
  -- 25. `assert_eq!(KernelCheck::spec_params_ptr_eq(Lists::take(largs, rp), bvars_desc(d, rp)), 1)`
  obtain ⟨_, h_pref, _, _, _, d25, mt25, rest25, hc25⟩ := rest24.letValue_inv; clear rest24
  rw [hc25] at sc24; have sc25 := sc24.append_right; clear sc24 hc25
  obtain ⟨_, a25, ap25⟩ := d25.builtin_inv
  obtain ⟨_, _, _, _, _, rfl, _, d25_1, d25_2⟩ := inv_args2 a25
  obtain ⟨_, h_bvd1, _, cs_pref, a25_c, ev_pref, _⟩ := d25_1.call_inv
  rw [instanceName_plain_some] at ev_pref
  obtain ⟨v_ltake, v_bvd1, h_ltake, _, _, rfl, _, d25_tk, d25_bv⟩ := inv_args2 a25_c
  obtain ⟨_, _, _, cs_ltake, a25_tk, ev_ltake, _⟩ := d25_tk.call_inv
  rw [Obs.Names.n3863982424408310192] at ev_ltake
  obtain ⟨_, _, _, _, _, rfl, _, d25_tk1, d25_tk2⟩ := inv_args2 a25_tk
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d25_tk1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d25_tk2
  obtain ⟨_, _, _, cs_bvd1, a25_bv, ev_bvd1, _⟩ := d25_bv.call_inv
  rw [instanceName_plain_some] at ev_bvd1
  obtain ⟨_, _, _, _, _, rfl, _, d25_bv1, d25_bv2⟩ := inv_args2 a25_bv
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d25_bv1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d25_bv2
  obtain ⟨rfl, rfl, _⟩ := d25_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap25
  obtain rfl := matchPattern_wildcard_inv mt25
  -- 26. `let major = Lists::lookup(largs, mi)`
  obtain ⟨major, h_maj, _, _, _, d26, mt26, rest26, hc26⟩ := rest25.letValue_inv; clear rest25
  rw [hc26] at sc25; have sc26 := sc25.append_right; clear sc25 hc26
  obtain ⟨_, _, _, cs_maj, a26, ev_maj, _⟩ := d26.call_inv
  rw [Obs.Names.n11123572196661760086] at ev_maj
  obtain ⟨_, _, _, _, _, rfl, _, d26_1, d26_2⟩ := inv_args2 a26
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d26_1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d26_2
  obtain rfl := matchPattern_bind_inv mt26
  -- 27. `let cren = rename_addr(cprj, src, dst)`
  obtain ⟨cren, h_cren, _, _, _, d27, mt27, rest27, hc27⟩ := rest26.letValue_inv; clear rest26
  rw [hc27] at sc26; have sc27 := sc26.append_right; clear sc26 hc27
  obtain ⟨_, _, _, cs_cren, a27, ev_cren, _⟩ := d27.call_inv
  rw [instanceName_plain_some] at ev_cren
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d27_1, d27_2, d27_3⟩ := inv_args3 a27
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d27_1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d27_2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d27_3
  obtain rfl := matchPattern_bind_inv mt27
  -- 28. `let pins_ren = rename_list(pins, src, dst)`
  obtain ⟨pins_ren, h_pren, _, _, _, d28, mt28, rest28, hc28⟩ := rest27.letValue_inv; clear rest27
  rw [hc28] at sc27; have sc28 := sc27.append_right; clear sc27 hc28
  obtain ⟨_, _, _, cs_pren, a28, ev_pren, _⟩ := d28.call_inv
  rw [instanceName_plain_some] at ev_pren
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d28_1, d28_2, d28_3⟩ := inv_args3 a28
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d28_1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d28_2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d28_3
  obtain rfl := matchPattern_bind_inv mt28
  -- 29. `let pins_d = lift_list(pins_ren, cnf)`
  obtain ⟨pins_d, h_pd, _, c29a, _, d29, mt29, rest29, hc29⟩ := rest28.letValue_inv; clear rest28
  rw [hc29] at sc28; have sc29_l := sc28.append_left; have sc29 := sc28.append_right; clear sc28 hc29
  obtain ⟨_, _, _, cs_pd, a29, ev_pd, hc_pd⟩ := d29.call_inv
  rw [instanceName_plain_some] at ev_pd hc_pd
  obtain ⟨_, _, _, _, _, rfl, hc29_args, d29_1, d29_2⟩ := inv_args2 a29
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d29_1
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d29_2
  obtain rfl := matchPattern_bind_inv mt29
  rw [hc_pd, hc29_args] at sc29_l
  have sub_pd := sc29_l.append_right.cons_tail
  clear sc29_l hc_pd hc29_args
  -- 30. `let expected = KernelWhnf::apply_spine((&(Const(cren, ilvls))), Lists::concat(pins_d, bvars_desc(cnf, cnf)))`
  obtain ⟨expected, h_exp, _, _, _, d30, mt30, rest30, hc30⟩ := rest29.letValue_inv; clear rest29
  rw [hc30] at sc29; have sc30 := sc29.append_right; clear sc29 hc30
  obtain ⟨_, h_cat, _, cs_exp, a30, ev_exp, _⟩ := d30.call_inv
  rw [instanceName_plain_some] at ev_exp
  obtain ⟨_, v_cat, _, _, _, rfl, _, d30_1, d30_2⟩ := inv_args2 a30
  obtain ⟨_, _, d30_c, rfl, rfl⟩ := d30_1.store_inv
  obtain ⟨_, a30_c, hres30⟩ := d30_c.construct_inv
  rw [instanceName_plain_some] at hres30; subst hres30
  obtain ⟨_, _, _, _, _, rfl, _, d30_c1, d30_c2⟩ := inv_args2 a30_c
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d30_c1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d30_c2
  simp only [Value.type] at ev_exp
  obtain ⟨_, h_bvd2, _, cs_cat, a30_cat, ev_cat, _⟩ := d30_2.call_inv
  rw [Obs.Names.n7100276142009841923] at ev_cat
  obtain ⟨_, v_bvd2, _, _, _, rfl, _, d30_pd, d30_bv⟩ := inv_args2 a30_cat
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d30_pd
  obtain ⟨_, _, _, cs_bvd2, a30_bv, ev_bvd2, _⟩ := d30_bv.call_inv
  rw [instanceName_plain_some] at ev_bvd2
  obtain ⟨_, _, _, _, _, rfl, _, d30_bv1, d30_bv2⟩ := inv_args2 a30_bv
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d30_bv1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d30_bv2
  obtain rfl := matchPattern_bind_inv mt30
  -- 31. `assert_eq!(KernelCheck::kexpr_struct_eq(major, expected), 1)`
  obtain ⟨_, h_majeq, _, _, _, d31, mt31, rest31, hc31⟩ := rest30.letValue_inv; clear rest30
  rw [hc31] at sc30; have sc31 := sc30.append_right; clear sc30 hc31
  obtain ⟨_, a31, ap31⟩ := d31.builtin_inv
  obtain ⟨_, _, _, _, _, rfl, _, d31_1, d31_2⟩ := inv_args2 a31
  obtain ⟨_, _, _, cs_majeq, a31_c, ev_majeq, _⟩ := d31_1.call_inv
  rw [instanceName_plain_some] at ev_majeq
  obtain ⟨_, _, _, _, _, rfl, _, d31_c1, d31_c2⟩ := inv_args2 a31_c
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d31_c1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d31_c2
  obtain ⟨rfl, rfl, _⟩ := d31_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap31
  obtain rfl := matchPattern_wildcard_inv mt31
  -- 32. `let cty_l = KernelLevels::expr_inst_levels(cty, ilvls)`
  obtain ⟨cty_l, h_ctyl, _, c32a, _, d32, mt32, rest32, hc32⟩ := rest31.letValue_inv; clear rest31
  rw [hc32] at sc31; have sc32_l := sc31.append_left; have sc32 := sc31.append_right; clear sc31 hc32
  obtain ⟨_, _, _, cs_ctyl, a32, ev_ctyl, hc_ctyl⟩ := d32.call_inv
  rw [instanceName_plain_some] at ev_ctyl hc_ctyl
  obtain ⟨_, _, _, _, _, rfl, hc32_args, d32_1, d32_2⟩ := inv_args2 a32
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d32_1
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d32_2
  obtain rfl := matchPattern_bind_inv mt32
  rw [hc_ctyl, hc32_args] at sc32_l
  have sub_ctyl := sc32_l.append_right.cons_tail
  clear sc32_l hc_ctyl hc32_args
  -- 33. `let (chead0, _) = KernelTypes::collect_spine(KernelCheck::peel_n_foralls(cty_l, cnp + cnf))`
  obtain ⟨_, h_csp0, _, c33a, _, d33, mt33, rest33, hc33⟩ := rest32.letValue_inv; clear rest32
  rw [hc33] at sc32; have sc33_l := sc32.append_left; have sc33 := sc32.append_right; clear sc32 hc33
  obtain ⟨_, h_peel0, c33_spargs, cs_csp0, a33, ev_csp0, hc_csp0⟩ := d33.call_inv
  rw [instanceName_plain_some] at ev_csp0 hc_csp0
  obtain ⟨v_peel0, rfl, d33_p⟩ := inv_args1 a33
  obtain ⟨_, _, _, cs_peel0, a33_p, ev_peel0, _⟩ := d33_p.call_inv
  rw [instanceName_plain_some] at ev_peel0
  obtain ⟨_, cnp_cnf, _, _, _, rfl, _, d33_p1, d33_p2⟩ := inv_args2 a33_p
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d33_p1
  obtain ⟨_, _, _, _, _, d33_b1, d33_b2, op_cnp_cnf, _⟩ := d33_p2.binary_inv
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d33_b1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d33_b2
  obtain ⟨_, hv33, -, ml33a⟩ := matchPattern_tuple_inv mt33; subst hv33
  obtain ⟨chead0, _, _, _, rfl, mt33_1, ml33b, rfl⟩ := matchListWith_cons_inv ml33a
  obtain rfl := matchPattern_bind_inv mt33_1
  obtain ⟨cargs0, _, _, _, rfl, mt33_2, ml33c, rfl⟩ := matchListWith_cons_inv ml33b
  obtain rfl := matchPattern_wildcard_inv mt33_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml33c
  rw [hc_csp0] at sc33_l
  have sub_csp0 := sc33_l.append_right.cons_tail
  clear sc33_l hc_csp0
  -- 34. `match (*(chead0)) { Const(_, _) => { () } };`
  obtain ⟨w_ch0a, w_ch0b, _, ld_chead0, sc34, rest34⟩ :=
    inv_match_kexpr_const_unit (by rfl) sc33 rest33; clear sc33 rest33
  -- 35. `let crest = inst_params(rename(cty_l, src, dst), pins_ren)`
  obtain ⟨crest, h_crest, _, c35a, _, d35, mt35, rest35, hc35⟩ := rest34.letValue_inv; clear rest34
  rw [hc35] at sc34; have sc35_l := sc34.append_left; have sc35 := sc34.append_right; clear sc34 hc35
  obtain ⟨_, _, c35_args, cs_crest, a35, ev_crest, hc_crest⟩ := d35.call_inv
  rw [instanceName_plain_some] at ev_crest hc_crest
  obtain ⟨v_cty_ren, _, h_cty_ren, _, _, rfl, _, d35_1, d35_2⟩ := inv_args2 a35
  obtain ⟨_, _, _, cs_cty_ren, a35_r, ev_cty_ren, _⟩ := d35_1.call_inv
  rw [instanceName_plain_some] at ev_cty_ren
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d35_r1, d35_r2, d35_r3⟩ := inv_args3 a35_r
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d35_r1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d35_r2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d35_r3
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d35_2
  obtain rfl := matchPattern_bind_inv mt35
  rw [hc_crest] at sc35_l
  have sub_crest := sc35_l.append_right.cons_tail
  clear sc35_l hc_crest
  -- 36. `let (cres, _) = peel_collect(crest, cnf, (&(Lists::Node::Nil)))`
  obtain ⟨_, h_cres, _, _, _, d36, mt36, rest36, hc36⟩ := rest35.letValue_inv; clear rest35
  rw [hc36] at sc35; have sc36 := sc35.append_right; clear sc35 hc36
  obtain ⟨_, _, _, cs_cres, a36, ev_cres, _⟩ := d36.call_inv
  rw [instanceName_plain_some] at ev_cres
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d36_1, d36_2, d36_3⟩ := inv_args3 a36
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d36_1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d36_2
  obtain ⟨rfl, rfl, _⟩ := inv_store_nil_kexpr d36_3
  obtain ⟨_, hv36, -, ml36a⟩ := matchPattern_tuple_inv mt36; subst hv36
  obtain ⟨cres, _, _, _, rfl, mt36_1, ml36b, rfl⟩ := matchListWith_cons_inv ml36a
  obtain rfl := matchPattern_bind_inv mt36_1
  obtain ⟨w_cctx, _, _, _, rfl, mt36_2, ml36c, rfl⟩ := matchListWith_cons_inv ml36b
  obtain rfl := matchPattern_wildcard_inv mt36_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml36c
  -- 37. `let (chead, cargs) = KernelTypes::collect_spine(cres)`
  obtain ⟨_, h_csp, _, c37a, _, d37, mt37, rest37, hc37⟩ := rest36.letValue_inv; clear rest36
  rw [hc37] at sc36; have sc37_l := sc36.append_left; have sc37 := sc36.append_right; clear sc36 hc37
  obtain ⟨_, _, _, cs_csp, a37, ev_csp, hc_csp⟩ := d37.call_inv
  rw [instanceName_plain_some] at ev_csp hc_csp
  obtain ⟨_, rfl, d37_1⟩ := inv_args1 a37
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d37_1
  obtain ⟨_, hv37, -, ml37a⟩ := matchPattern_tuple_inv mt37; subst hv37
  obtain ⟨chead, _, _, _, rfl, mt37_1, ml37b, rfl⟩ := matchListWith_cons_inv ml37a
  obtain rfl := matchPattern_bind_inv mt37_1
  obtain ⟨cargs, _, _, _, rfl, mt37_2, ml37c, rfl⟩ := matchListWith_cons_inv ml37b
  obtain rfl := matchPattern_bind_inv mt37_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml37c
  rw [hc_csp] at sc37_l
  have sub_csp := sc37_l.append_right.cons_tail
  clear sc37_l hc_csp
  -- 38. `match (*(chead)) { Const(_, _) => { () } };`
  obtain ⟨w_cha, w_chb, _, ld_chead, sc38, rest38⟩ :=
    inv_match_kexpr_const_unit (by rfl) sc37 rest37; clear sc37 rest37
  -- 39. `assert_eq!(Lists::length(cargs), cnp + ni)`
  obtain ⟨_, _, _, c39a, _, d39, mt39, rest39, hc39⟩ := rest38.letValue_inv; clear rest38
  rw [hc39] at sc38; have sc39_l := sc38.append_left; have sc39 := sc38.append_right; clear sc38 hc39
  obtain ⟨_, a39, ap39⟩ := d39.builtin_inv
  obtain ⟨v39_l, cnp_ni, h_clen, c39_l, _, rfl, hc39_args, d39_1, d39_2⟩ := inv_args2 a39
  obtain ⟨_, _, _, cs_clen, a39_c, ev_clen, hc_clen⟩ := d39_1.call_inv
  rw [Obs.Names.n6682477127133607924] at ev_clen hc_clen
  obtain ⟨_, rfl, d39_v⟩ := inv_args1 a39_c
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d39_v
  obtain ⟨_, _, _, _, _, d39_b1, d39_b2, op_cnp_ni, _⟩ := d39_2.binary_inv
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d39_b1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d39_b2
  obtain ⟨heq39, rfl⟩ := Builtin.assertEq_inv ap39; subst v39_l
  obtain rfl := matchPattern_wildcard_inv mt39
  rw [hc39_args, hc_clen] at sc39_l
  have call_clen := sc39_l.append_left.append_right.cons_head
  clear sc39_l hc39_args hc_clen
  -- 40. `assert_eq!(defeq_list_ok(rc, Lists::take(Lists::drop(largs, rp), ni), Lists::drop(cargs, cnp), ctx), 1)`
  obtain ⟨_, h_deidx, _, c40a, _, d40, mt40, rest40, hc40⟩ := rest39.letValue_inv; clear rest39
  rw [hc40] at sc39; have sc40_l := sc39.append_left; have sc40 := sc39.append_right; clear sc39 hc40
  obtain ⟨_, a40, ap40⟩ := d40.builtin_inv
  obtain ⟨_, _, _, c40_l, _, rfl, hc40_args, d40_1, d40_2⟩ := inv_args2 a40
  obtain ⟨_, _, _, cs_deidx, a40_c, ev_deidx, hc_deidx⟩ := d40_1.call_inv
  rw [instanceName_plain_some] at ev_deidx hc_deidx
  obtain ⟨_, v_idxl, v_idxr, _, _, h_idxl, h_idxr, _, _, _, _, rfl, _, d40_c1, d40_c2, d40_c3, d40_c4⟩ :=
    inv_args4 a40_c
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d40_c1
  obtain ⟨_, _, _, cs_idxl, a40_tk, ev_idxl, _⟩ := d40_c2.call_inv
  rw [Obs.Names.n3863982424408310192] at ev_idxl
  obtain ⟨v_ldrop, _, h_ldrop, _, _, rfl, _, d40_dr1, d40_ni⟩ := inv_args2 a40_tk
  obtain ⟨_, _, _, cs_ldrop, a40_dr1, ev_ldrop, _⟩ := d40_dr1.call_inv
  rw [Obs.Names.n4825454920124213627] at ev_ldrop
  obtain ⟨_, _, _, _, _, rfl, _, d40_la, d40_rp⟩ := inv_args2 a40_dr1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d40_la
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d40_rp
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d40_ni
  obtain ⟨_, _, _, cs_idxr, a40_dr2, ev_idxr, _⟩ := d40_c3.call_inv
  rw [Obs.Names.n4825454920124213627] at ev_idxr
  obtain ⟨_, _, _, _, _, rfl, _, d40_ca, d40_cp⟩ := inv_args2 a40_dr2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d40_ca
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d40_cp
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d40_c4
  obtain ⟨rfl, rfl, _⟩ := d40_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap40
  obtain rfl := matchPattern_wildcard_inv mt40
  rw [hc40_args, hc_deidx] at sc40_l
  have sub_deidx := sc40_l.append_left.append_right.cons_tail
  clear sc40_l hc40_args hc_deidx
  -- 41. `defeq_tele(rc, tty, rename(ty_r, src, dst), rp, (&(Lists::Node::Nil)))`
  obtain ⟨v_dt1, h_dt1, _, c41a, _, d41, mt41, rest41, hc41⟩ := rest40.letValue_inv; clear rest40
  rw [hc41] at sc40; have sc41_l := sc40.append_left; have sc41 := sc40.append_right; clear sc40 hc41
  obtain ⟨_, _, _, cs_dt1, a41, ev_dt1, hc_dt1⟩ := d41.call_inv
  rw [instanceName_plain_some] at ev_dt1 hc_dt1
  obtain ⟨_, _, v_tyr_ren, _, _, _, _, h_tyr_ren, _, _, _, _, _, _, rfl, _,
    d41_1, d41_2, d41_3, d41_4, d41_5⟩ := inv_args5 a41
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d41_1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d41_2
  obtain ⟨_, _, _, cs_tyr_ren, a41_r, ev_tyr_ren, _⟩ := d41_3.call_inv
  rw [instanceName_plain_some] at ev_tyr_ren
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d41_r1, d41_r2, d41_r3⟩ := inv_args3 a41_r
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d41_r1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d41_r2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d41_r3
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d41_4
  obtain ⟨rfl, rfl, _⟩ := inv_store_nil_kexpr d41_5
  obtain rfl := matchPattern_wildcard_inv mt41
  rw [hc_dt1] at sc41_l
  have sub_dt1 := sc41_l.append_right.cons_tail
  clear sc41_l hc_dt1
  -- 42. `defeq_tele(rc, KernelCheck::peel_n_foralls(tty, rp), crest, cnf, Lists::drop(ctx, cnf))`
  obtain ⟨v_dt2, h_dt2, _, c42a, _, d42, mt42, rest42, hc42⟩ := rest41.letValue_inv; clear rest41
  rw [hc42] at sc41; have sc42_l := sc41.append_left; have sc42 := sc41.append_right; clear sc41 hc42
  obtain ⟨_, h_ctx_rp, _, cs_dt2, a42, ev_dt2, hc_dt2⟩ := d42.call_inv
  rw [instanceName_plain_some] at ev_dt2 hc_dt2
  obtain ⟨_, v_tty_rp, _, _, v_ctx_rp, _, h_tty_rp, _, _, _, _, _, _, _, rfl, _,
    d42_1, d42_2, d42_3, d42_4, d42_5⟩ := inv_args5 a42
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d42_1
  obtain ⟨_, _, _, cs_tty_rp, a42_p, ev_tty_rp, _⟩ := d42_2.call_inv
  rw [instanceName_plain_some] at ev_tty_rp
  obtain ⟨_, _, _, _, _, rfl, _, d42_p1, d42_p2⟩ := inv_args2 a42_p
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d42_p1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d42_p2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d42_3
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d42_4
  obtain ⟨_, _, _, cs_ctx_rp, a42_dr, ev_ctx_rp, _⟩ := d42_5.call_inv
  rw [Obs.Names.n4825454920124213627] at ev_ctx_rp
  obtain ⟨_, _, _, _, _, rfl, _, d42_dr1, d42_dr2⟩ := inv_args2 a42_dr
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d42_dr1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d42_dr2
  obtain rfl := matchPattern_wildcard_inv mt42
  rw [hc_dt2] at sc42_l
  have sub_dt2 := sc42_l.append_right.cons_tail
  clear sc42_l hc_dt2
  -- 43. `let (_, ctx_p) = peel_collect(ty_r, rp, (&(Lists::Node::Nil)))`
  obtain ⟨_, h_ctxp, _, _, _, d43, mt43, rest43, hc43⟩ := rest42.letValue_inv; clear rest42
  rw [hc43] at sc42; have sc43 := sc42.append_right; clear sc42 hc43
  obtain ⟨_, _, _, cs_ctxp, a43, ev_ctxp, _⟩ := d43.call_inv
  rw [instanceName_plain_some] at ev_ctxp
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d43_1, d43_2, d43_3⟩ := inv_args3 a43
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d43_1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d43_2
  obtain ⟨rfl, rfl, _⟩ := inv_store_nil_kexpr d43_3
  obtain ⟨_, hv43, -, ml43a⟩ := matchPattern_tuple_inv mt43; subst hv43
  obtain ⟨w_pbody, _, _, _, rfl, mt43_1, ml43b, rfl⟩ := matchListWith_cons_inv ml43a
  obtain rfl := matchPattern_wildcard_inv mt43_1
  obtain ⟨ctx_p, _, _, _, rfl, mt43_2, ml43c, rfl⟩ := matchListWith_cons_inv ml43b
  obtain rfl := matchPattern_bind_inv mt43_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml43c
  -- 44. `let crest_p = inst_params_typed(rc, cty_l, pins, ctx_p)`
  obtain ⟨crest_p, h_crestp, _, c44a, _, d44, mt44, rest44, hc44⟩ := rest43.letValue_inv; clear rest43
  rw [hc44] at sc43; have sc44_l := sc43.append_left; have sc44 := sc43.append_right; clear sc43 hc44
  obtain ⟨_, _, _, cs_crestp, a44, ev_crestp, hc_crestp⟩ := d44.call_inv
  rw [instanceName_plain_some] at ev_crestp hc_crestp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, d44_1, d44_2, d44_3, d44_4⟩ := inv_args4 a44
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d44_1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d44_2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d44_3
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d44_4
  obtain rfl := matchPattern_bind_inv mt44
  rw [hc_crestp] at sc44_l
  have sub_crestp := sc44_l.append_right.cons_tail
  clear sc44_l hc_crestp
  -- 45. `let (rhs_rp, lctx) = defeq_lam_tele(rc, rhs, ty_r, rp, (&(Lists::Node::Nil)))`
  obtain ⟨_, h_lt1, _, c45a, _, d45, mt45, rest45, hc45⟩ := rest44.letValue_inv; clear rest44
  rw [hc45] at sc44; have sc45_l := sc44.append_left; have sc45 := sc44.append_right; clear sc44 hc45
  obtain ⟨_, _, _, cs_lt1, a45, ev_lt1, hc_lt1⟩ := d45.call_inv
  rw [instanceName_plain_some] at ev_lt1 hc_lt1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _,
    d45_1, d45_2, d45_3, d45_4, d45_5⟩ := inv_args5 a45
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d45_1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d45_2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d45_3
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d45_4
  obtain ⟨rfl, rfl, _⟩ := inv_store_nil_kexpr d45_5
  obtain ⟨_, hv45, -, ml45a⟩ := matchPattern_tuple_inv mt45; subst hv45
  obtain ⟨rhs_rp, _, _, _, rfl, mt45_1, ml45b, rfl⟩ := matchListWith_cons_inv ml45a
  obtain rfl := matchPattern_bind_inv mt45_1
  obtain ⟨lctx, _, _, _, rfl, mt45_2, ml45c, rfl⟩ := matchListWith_cons_inv ml45b
  obtain rfl := matchPattern_bind_inv mt45_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml45c
  rw [hc_lt1] at sc45_l
  have sub_lt1 := sc45_l.append_right.cons_tail
  clear sc45_l hc_lt1
  -- 46. `let (_, _) = defeq_lam_tele(rc, rhs_rp, crest_p, cnf, lctx)`
  obtain ⟨_, h_lt2, _, c46a, _, d46, mt46, rest46, hc46⟩ := rest45.letValue_inv; clear rest45
  rw [hc46] at sc45; have sc46_l := sc45.append_left; have sc46 := sc45.append_right; clear sc45 hc46
  obtain ⟨_, _, _, cs_lt2, a46, ev_lt2, hc_lt2⟩ := d46.call_inv
  rw [instanceName_plain_some] at ev_lt2 hc_lt2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _,
    d46_1, d46_2, d46_3, d46_4, d46_5⟩ := inv_args5 a46
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d46_1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d46_2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d46_3
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d46_4
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d46_5
  obtain ⟨_, hv46, -, ml46a⟩ := matchPattern_tuple_inv mt46; subst hv46
  obtain ⟨w_lt2a, _, _, _, rfl, mt46_1, ml46b, rfl⟩ := matchListWith_cons_inv ml46a
  obtain rfl := matchPattern_wildcard_inv mt46_1
  obtain ⟨w_lt2b, _, _, _, rfl, mt46_2, ml46c, rfl⟩ := matchListWith_cons_inv ml46b
  obtain rfl := matchPattern_wildcard_inv mt46_2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml46c
  rw [hc_lt2] at sc46_l
  have sub_lt2 := sc46_l.append_right.cons_tail
  clear sc46_l hc_lt2
  -- 47. `let rhs_app = KernelWhnf::apply_spine(rename(rhs, src, dst), bvars_desc(d, d))`
  obtain ⟨rhs_app, h_rhsapp, _, _, _, d47, mt47, rest47, hc47⟩ := rest46.letValue_inv; clear rest46
  rw [hc47] at sc46; have sc47 := sc46.append_right; clear sc46 hc47
  obtain ⟨_, h_bvd3, _, cs_rhsapp, a47, ev_rhsapp, _⟩ := d47.call_inv
  rw [instanceName_plain_some] at ev_rhsapp
  obtain ⟨v_rhs_ren, v_bvd3, h_rhs_ren, _, _, rfl, _, d47_1, d47_2⟩ := inv_args2 a47
  obtain ⟨_, _, _, cs_rhs_ren, a47_r, ev_rhs_ren, _⟩ := d47_1.call_inv
  rw [instanceName_plain_some] at ev_rhs_ren
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d47_r1, d47_r2, d47_r3⟩ := inv_args3 a47_r
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d47_r1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d47_r2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d47_r3
  obtain ⟨_, _, _, cs_bvd3, a47_bv, ev_bvd3, _⟩ := d47_2.call_inv
  rw [instanceName_plain_some] at ev_bvd3
  obtain ⟨_, _, _, _, _, rfl, _, d47_bv1, d47_bv2⟩ := inv_args2 a47_bv
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d47_bv1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d47_bv2
  obtain rfl := matchPattern_bind_inv mt47
  -- 48. `assert_eq!(KernelDefEq::k_is_def_eq(rc, rhs_s, rhs_app, ctx), 1)`
  obtain ⟨_, h_derhs, _, c48a, _, d48, mt48, rest48, hc48⟩ := rest47.letValue_inv; clear rest47
  rw [hc48] at sc47; have sc48_l := sc47.append_left; have sc48 := sc47.append_right; clear sc47 hc48
  obtain ⟨_, a48, ap48⟩ := d48.builtin_inv
  obtain ⟨_, _, _, c48_l, _, rfl, hc48_args, d48_1, d48_2⟩ := inv_args2 a48
  obtain ⟨_, _, _, cs_derhs, a48_c, ev_derhs, hc_derhs⟩ := d48_1.call_inv
  rw [instanceName_plain_some] at ev_derhs hc_derhs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, d48_c1, d48_c2, d48_c3, d48_c4⟩ := inv_args4 a48_c
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d48_c1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d48_c2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d48_c3
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d48_c4
  obtain ⟨rfl, rfl, _⟩ := d48_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap48
  obtain rfl := matchPattern_wildcard_inv mt48
  rw [hc48_args, hc_derhs] at sc48_l
  have sub_derhs := sc48_l.append_left.append_right.cons_tail
  clear sc48_l hc48_args hc_derhs
  -- 49. `let tl = KernelInfer::k_infer(rc, lhs, ctx)`
  obtain ⟨tl, h_tl, _, c49a, _, d49, mt49, rest49, hc49⟩ := rest48.letValue_inv; clear rest48
  rw [hc49] at sc48; have sc49_l := sc48.append_left; have sc49 := sc48.append_right; clear sc48 hc49
  obtain ⟨_, _, _, cs_tl, a49, ev_tl, hc_tl⟩ := d49.call_inv
  rw [instanceName_plain_some] at ev_tl hc_tl
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d49_1, d49_2, d49_3⟩ := inv_args3 a49
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d49_1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d49_2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d49_3
  obtain rfl := matchPattern_bind_inv mt49
  rw [hc_tl] at sc49_l
  have sub_tl := sc49_l.append_right.cons_tail
  clear sc49_l hc_tl
  -- 50. `assert_eq!(KernelDefEq::k_is_def_eq(rc, tl, alpha, ctx), 1)`
  obtain ⟨_, h_detl, _, c50a, _, d50, mt50, rest50, hc50⟩ := rest49.letValue_inv; clear rest49
  rw [hc50] at sc49; have sc50_l := sc49.append_left; have sc50 := sc49.append_right; clear sc49 hc50
  obtain ⟨_, a50, ap50⟩ := d50.builtin_inv
  obtain ⟨_, _, _, c50_l, _, rfl, hc50_args, d50_1, d50_2⟩ := inv_args2 a50
  obtain ⟨_, _, _, cs_detl, a50_c, ev_detl, hc_detl⟩ := d50_1.call_inv
  rw [instanceName_plain_some] at ev_detl hc_detl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, d50_c1, d50_c2, d50_c3, d50_c4⟩ := inv_args4 a50_c
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d50_c1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d50_c2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d50_c3
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d50_c4
  obtain ⟨rfl, rfl, _⟩ := d50_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap50
  obtain rfl := matchPattern_wildcard_inv mt50
  rw [hc50_args, hc_detl] at sc50_l
  have sub_detl := sc50_l.append_left.append_right.cons_tail
  clear sc50_l hc50_args hc_detl
  -- 51. `let tr = KernelInfer::k_infer(rc, rhs_s, ctx)`
  obtain ⟨tr, h_tr, _, c51a, _, d51, mt51, rest51, hc51⟩ := rest50.letValue_inv; clear rest50
  rw [hc51] at sc50; have sc51_l := sc50.append_left; have sc51 := sc50.append_right; clear sc50 hc51
  obtain ⟨_, _, _, cs_tr, a51, ev_tr, hc_tr⟩ := d51.call_inv
  rw [instanceName_plain_some] at ev_tr hc_tr
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d51_1, d51_2, d51_3⟩ := inv_args3 a51
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d51_1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d51_2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d51_3
  obtain rfl := matchPattern_bind_inv mt51
  rw [hc_tr] at sc51_l
  have sub_tr := sc51_l.append_right.cons_tail
  clear sc51_l hc_tr
  -- 52. `assert_eq!(KernelDefEq::k_is_def_eq(rc, tr, alpha, ctx), 1)`
  obtain ⟨_, h_detr, _, c52a, _, d52, mt52, rest52, hc52⟩ := rest51.letValue_inv; clear rest51
  rw [hc52] at sc51; have sc52_l := sc51.append_left; have sc52 := sc51.append_right; clear sc51 hc52
  obtain ⟨_, a52, ap52⟩ := d52.builtin_inv
  obtain ⟨_, _, _, c52_l, _, rfl, hc52_args, d52_1, d52_2⟩ := inv_args2 a52
  obtain ⟨_, _, _, cs_detr, a52_c, ev_detr, hc_detr⟩ := d52_1.call_inv
  rw [instanceName_plain_some] at ev_detr hc_detr
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, d52_c1, d52_c2, d52_c3, d52_c4⟩ := inv_args4 a52_c
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d52_c1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d52_c2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d52_c3
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d52_c4
  obtain ⟨rfl, rfl, _⟩ := d52_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap52
  obtain rfl := matchPattern_wildcard_inv mt52
  rw [hc52_args, hc_detr] at sc52_l
  have sub_detr := sc52_l.append_left.append_right.cons_tail
  clear sc52_l hc52_args hc_detr
  -- 53. `let ta = KernelInfer::k_infer(rc, alpha, ctx)`
  obtain ⟨ta, h_ta, _, c53a, _, d53, mt53, rest53, hc53⟩ := rest52.letValue_inv; clear rest52
  rw [hc53] at sc52; have sc53_l := sc52.append_left; have sc53 := sc52.append_right; clear sc52 hc53
  obtain ⟨_, _, _, cs_ta, a53, ev_ta, hc_ta⟩ := d53.call_inv
  rw [instanceName_plain_some] at ev_ta hc_ta
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, d53_1, d53_2, d53_3⟩ := inv_args3 a53
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d53_1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d53_2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d53_3
  obtain rfl := matchPattern_bind_inv mt53
  rw [hc_ta] at sc53_l
  have sub_ta := sc53_l.append_right.cons_tail
  clear sc53_l hc_ta
  -- 54. `assert_eq!(KernelDefEq::k_is_def_eq(rc, ta, (&(KernelTypes::KExprNode::Srt(ell))), ctx), 1)`
  obtain ⟨_, h_deta, _, c54a, _, d54, _, _, hc54⟩ := rest53.letValue_inv; clear rest53
  rw [hc54] at sc53; have sc54_l := sc53.append_left; clear sc53 hc54
  obtain ⟨_, a54, ap54⟩ := d54.builtin_inv
  obtain ⟨_, _, _, c54_l, _, rfl, hc54_args, d54_1, d54_2⟩ := inv_args2 a54
  obtain ⟨_, _, _, cs_deta, a54_c, ev_deta, hc_deta⟩ := d54_1.call_inv
  rw [instanceName_plain_some] at ev_deta hc_deta
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _, d54_c1, d54_c2, d54_c3, d54_c4⟩ := inv_args4 a54_c
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d54_c1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d54_c2
  obtain ⟨_, _, d54_srt, rfl, rfl⟩ := d54_c3.store_inv
  obtain ⟨_, a54_srt, hres54⟩ := d54_srt.construct_inv
  rw [instanceName_plain_some] at hres54; subst hres54
  obtain ⟨_, rfl, d54_ell⟩ := inv_args1 a54_srt
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d54_ell
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) d54_c4
  obtain ⟨rfl, rfl, _⟩ := d54_2.literal_inv
  obtain ⟨rfl, rfl⟩ := Builtin.assertEq_inv ap54
  simp only [Value.type] at ev_deta
  rw [hc54_args, hc_deta] at sc54_l
  have sub_deta := sc54_l.append_left.append_right.cons_tail
  subst hcalls₀_eq
  exact ⟨
    { mi, d, op_mi, op_d, h_plen, cs_plen, call_plen, ev_plen
      v_sc, h_sc, cs_sc, ev_sc, sub_sc
      r_peel_e, r_peel_acc, h_peel, cs_peel, ev_peel
      v_rhs_ty, h_rhs_inf, cs_rhs_inf, ev_rhs_inf, sub_rhs_inf
      h_aset, cs_aset, ev_aset, sub_aset
      p_tci, h_tci, cs_tci, ev_tci, sub_tci, tty, w_tval, ld_tci
      tbody, ctx, h_open, cs_open, ev_open
      eqh, targs, h_tsp, cs_tsp, ev_tsp, eqa, eqls, ld_eqh
      v_req, h_req, cs_req, v_raddr, h_raddr, cs_raddr, h_eqa, cs_eqa
      ev_req, ev_raddr, sub_raddr, ev_eqa
      ell, eqrest, ld_eqls1, ld_eqls2
      h_tlen, cs_tlen, call_tlen, ev_tlen
      alpha, lhs, rhs_s, h_a0, cs_a0, h_a1, cs_a1, h_a2, cs_a2, ev_a0, ev_a1, ev_a2
      lh, largs, h_lsp, cs_lsp, ev_lsp
      v_plvls, h_plvls, cs_plvls, ev_plvls
      h_lheq, cs_lheq, ev_lheq
      mi1, op_mi1, h_llen, cs_llen, call_llen, ev_llen
      v_ltake, h_ltake, cs_ltake, v_bvd1, h_bvd1, cs_bvd1, h_pref, cs_pref
      ev_ltake, ev_bvd1, ev_pref
      major, h_maj, cs_maj, ev_maj
      cren, h_cren, cs_cren, ev_cren
      pins_ren, h_pren, cs_pren, ev_pren
      pins_d, h_pd, cs_pd, ev_pd, sub_pd
      v_bvd2, h_bvd2, cs_bvd2, v_cat, h_cat, cs_cat
      expected, h_exp, cs_exp, h_majeq, cs_majeq
      ev_bvd2, ev_cat, ev_exp, ev_majeq
      cty_l, h_ctyl, cs_ctyl, ev_ctyl, sub_ctyl
      cnp_cnf, op_cnp_cnf, v_peel0, h_peel0, cs_peel0
      chead0, cargs0, h_csp0, cs_csp0, ev_peel0, ev_csp0, sub_csp0
      w_ch0a, w_ch0b, ld_chead0
      v_cty_ren, h_cty_ren, cs_cty_ren, crest, h_crest, cs_crest
      ev_cty_ren, ev_crest, sub_crest
      cres, w_cctx, h_cres, cs_cres, ev_cres
      chead, cargs, h_csp, cs_csp, ev_csp, sub_csp
      w_cha, w_chb, ld_chead
      cnp_ni, op_cnp_ni, h_clen, cs_clen, call_clen, ev_clen
      v_ldrop, h_ldrop, cs_ldrop, v_idxl, h_idxl, cs_idxl, v_idxr, h_idxr, cs_idxr
      h_deidx, cs_deidx, ev_ldrop, ev_idxl, ev_idxr, ev_deidx, sub_deidx
      v_tyr_ren, h_tyr_ren, cs_tyr_ren, v_dt1, h_dt1, cs_dt1
      ev_tyr_ren, ev_dt1, sub_dt1
      v_tty_rp, h_tty_rp, cs_tty_rp, v_ctx_rp, h_ctx_rp, cs_ctx_rp
      v_dt2, h_dt2, cs_dt2, ev_tty_rp, ev_ctx_rp, ev_dt2, sub_dt2
      w_pbody, ctx_p, h_ctxp, cs_ctxp, ev_ctxp
      crest_p, h_crestp, cs_crestp, ev_crestp, sub_crestp
      rhs_rp, lctx, h_lt1, cs_lt1, ev_lt1, sub_lt1
      w_lt2a, w_lt2b, h_lt2, cs_lt2, ev_lt2, sub_lt2
      v_rhs_ren, h_rhs_ren, cs_rhs_ren, v_bvd3, h_bvd3, cs_bvd3
      rhs_app, h_rhsapp, cs_rhsapp, h_derhs, cs_derhs
      ev_rhs_ren, ev_bvd3, ev_rhsapp, ev_derhs, sub_derhs
      tl, h_tl, cs_tl, h_detl, cs_detl, tr, h_tr, cs_tr, h_detr, cs_detr
      ta, h_ta, cs_ta, h_deta, cs_deta
      ev_tl, sub_tl, ev_detl, sub_detl, ev_tr, sub_tr, ev_detr, sub_detr
      ev_ta, sub_ta, ev_deta, sub_deta }⟩

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
  obtain ⟨_, ev_lkp, _⟩ := Obs.«KernelClaim::addr_set_member».obs ev
  have hfn : Specs.Roles.rbtree_map_lookup_or_default_field c
      [t_addr, aset, .field 0] h (.field 1) h' _ :=
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
        Expr.ctorTeleOk e m = true
  | 0, e, _, rem, Dc, usc, hs, hfn => by
    injection hs with hp; injection hp with _ hrem; subst hrem
    rw [getAppFn_instantiateLevelParams] at hfn
    cases hgf : e.getAppFn with
    | const Dc₀ usc₀ =>
      rw [hgf] at hfn
      simp only [Expr.instantiateLevelParams, Expr.const.injEq] at hfn
      obtain ⟨rfl, _⟩ := hfn
      exact ⟨[], e, usc₀, rfl, hgf, by simp [Expr.ctorTeleOk, Expr.stripPis, hgf]⟩
    | bvar _ | fvar _ _ | sort _ | app _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _ _
    | lit _ | proj _ _ _ =>
      rw [hgf] at hfn; simp [Expr.instantiateLevelParams] at hfn
  | m + 1, .forallE dom body bm, _, _, Dc, usc, hs, hfn => by
    simp only [Expr.instantiateLevelParams, Expr.stripPis] at hs
    cases hsb : (body.instantiateLevelParams ks us).stripPis m with
    | none => simp [hsb] at hs
    | some p =>
      rw [hsb] at hs; injection hs with hp; injection hp with _ hrem; subst hrem
      obtain ⟨bs₀, rem₀, usc₀, hbs₀, hfn₀, _⟩ :=
        stripPis_constHead_of_instantiateLevelParams ks us m body hsb hfn
      refine ⟨(dom, bm) :: bs₀, rem₀, usc₀, by simp [Expr.stripPis, hbs₀], hfn₀, ?_⟩
      simp [Expr.ctorTeleOk, Expr.stripPis, hbs₀, hfn₀]
  | _ + 1, .bvar _, _, _, _, _, hs, _ | _ + 1, .fvar _ _, _, _, _, _, hs, _
  | _ + 1, .sort _, _, _, _, _, hs, _ | _ + 1, .const _ _, _, _, _, _, hs, _
  | _ + 1, .app _ _, _, _, _, _, hs, _ | _ + 1, .lam _ _ _, _, _, _, hs, _
  | _ + 1, .letE _ _ _ _, _, _, _, hs, _ | _ + 1, .lit _, _, _, _, _, hs, _
  | _ + 1, .proj _ _ _, _, _, _, hs, _ => by
    simp [Expr.instantiateLevelParams, Expr.stripPis] at hs

private theorem stripPis_renameConsts (π : KKey → KKey) :
    ∀ (m : Nat) (e : KExpr) {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem : KExpr},
      e.stripPis m = some (bs, rem) →
      (e.renameConsts π).stripPis m =
        some (bs.map (fun p => (p.1.renameConsts π, p.2)), rem.renameConsts π)
  | 0, _, _, _, hs => by
    injection hs with hp; injection hp with h1 h2; subst h1 h2; rfl
  | m + 1, .forallE dom body bm, _, _, hs => by
    simp only [Expr.stripPis] at hs
    cases hsb : body.stripPis m with
    | none => simp [hsb] at hs
    | some p =>
      rw [hsb] at hs; injection hs with hp; injection hp with h1 h2; subst h1 h2
      simp [Expr.renameConsts, Expr.stripPis, stripPis_renameConsts π m body hsb]
  | _ + 1, .bvar _, _, _, hs | _ + 1, .fvar _ _, _, _, hs | _ + 1, .sort _, _, _, hs
  | _ + 1, .const _ _, _, _, hs | _ + 1, .app _ _, _, _, hs | _ + 1, .lam _ _ _, _, _, hs
  | _ + 1, .letE _ _ _ _, _, _, hs | _ + 1, .lit _, _, _, hs | _ + 1, .proj _ _ _, _, _, hs =>
    nomatch hs

private theorem noProjIn_stripPis {bad : List KKey} :
    ∀ (m : Nat) {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem : KExpr},
      NoProjIn bad e = true → e.stripPis m = some (bs, rem) → NoProjIn bad rem = true
  | 0, _, _, _, hnp, hs => by
    injection hs with hp; injection hp with _ h2; subst h2; exact hnp
  | m + 1, .forallE _ body _, _, _, hnp, hs => by
    simp only [NoProjIn, Bool.and_eq_true] at hnp
    simp only [Expr.stripPis] at hs
    cases hsb : body.stripPis m with
    | none => simp [hsb] at hs
    | some p =>
      rw [hsb] at hs; injection hs with hp; injection hp with _ h2; subst h2
      exact noProjIn_stripPis m hnp.2 hsb
  | _ + 1, .bvar _, _, _, _, hs | _ + 1, .fvar _ _, _, _, _, hs | _ + 1, .sort _, _, _, _, hs
  | _ + 1, .const _ _, _, _, _, hs | _ + 1, .app _ _, _, _, _, hs | _ + 1, .lam _ _ _, _, _, hs
  | _ + 1, .letE _ _ _ _, _, _, hs | _ + 1, .lit _, _, _, _, hs | _ + 1, .proj _ _ _, _, _, hs =>
    nomatch hs

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
  | .fvar _ ty, c => noProjIn_lowerBVars bad s ty c
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

private theorem env_find?_name_eq {env : Ix.Kernel.Env .anon} {k : KKey} {ci : ConstantInfo .anon}
    (hf : env.find? k = some ci) : ci.name = k := by
  have hf' : env.consts.find? (fun x => x.name == k) = some ci := hf
  exact beq_iff_eq.mp (List.find?_some hf')

/-! ## Unified VM rule judgement records (`RawIotaRuleVmRun`, `RawIotaRulesVmRun`) -/

/-- Unified per-rule output of `KernelModeled::check_iota_rule` across public (`c_pub`) and advice
(`c_adv`) contexts, capturing both canonical and nested rule shapes together with the advice
theorem's universe sort check so `ModeledAux` can construct the `.aux` model environment and lift
directly to `IotaRulesVmRunJ`. -/
structure RawIotaRuleVmRun
    (c_pub c_adv : Ctx)
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
  hrhs_cr : r.rhs.constsResolve c_pub.env = true
  hrhs_typed : ∃ t', posRulesJ.infer c_pub.env 0 r.rhs t'
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
    (c_pub c_adv : Ctx)
    (blockNames : List KKey) (f_id : KKey → KKey) (advSet : Bytes.Address → Prop)
    (cvName : KKey) (lps : List LevelParam) (tyA : KExpr) (mI rP : Nat)
    (lvls_lps : List KLevel) (pins_lps : List KExpr) :
    Nat → List (RecRule .anon) → Prop
  | _, [] => True
  | j, r :: rest =>
    Nonempty (RawIotaRuleVmRun c_pub c_adv blockNames f_id advSet cvName lps tyA mI rP
      lvls_lps pins_lps j r) ∧
      RawIotaRulesVmRun c_pub c_adv blockNames f_id advSet cvName lps tyA mI rP lvls_lps pins_lps
        (j + 1) rest

/-! ## Refinement of `check_iota_rule`, `check_rules_go`, and `check_rules` -/

set_option maxHeartbeats 4000000 in
/-- **Refinement of `KernelModeled::check_iota_rule`**: discharges every syntactic, telescope,
and typing obligation in `RawIotaRuleVmRun` across `(c_pub, c_adv)`. -/
theorem check_iota_rule_vm_spec
    (hCore : IxVM.Consistency.Core S₀) (hroles : RolesSpec)
    {c_pub c_adv : Ctx}
    (ht_eq : c_adv.t = c_pub.t) (hlim_eq : c_adv.lim = c_pub.lim)
    (hef_pub : EnvFacts c_pub) (hlf_pub : LoadFacts c_pub)
    (hef_adv : EnvFacts c_adv) (hlf_adv : LoadFacts c_adv)
    (hexact_adv : ExactGetCI c_adv)
    {blockNames : List KKey} {f_id : KKey → KKey} {advSet : Bytes.Address → Prop}
    (hf_out : ∀ k, blockNames.contains k = false → f_id k = k)
    (hproj_pub : ∀ sn i entry, c_pub.env.findProj? sn i = some entry →
      blockNames.contains sn = false)
    {cvName : KKey} {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat}
    {lvls_lps : List KLevel} {pins_lps : List KExpr}
    {j : Nat} {r : RecRule .anon}
    {cvj : ConstantVal .anon} {cnP cnF : Nat}
    {a_rm a_cprj a_t : Bytes.Address}
    {rc rm ty_r rhs cprj cty ilvls pins t_addr src dst aset v_ret : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hgood_pub : Good c_pub calls) (hgood_adv : Good c_adv calls)
    (hlps_lt : lps.length < 4294967296)
    (hlps_perm : lps.Perm (List.range lps.length))
    (hrp_le : rP ≤ mI) (hmi_lt : mI < 288230376151711744)
    (hcnp_lt : cnP < 72057594037927936) (hcnf_lt : cnF < 72057594037927936)
    (hfind_ctor : c_pub.env.find? r.ctor = some (.ctorInfo cvj cnP cnF))
    (hlvls_len : lvls_lps.length = cvj.levelParams.length)
    (hnfields : r.nfields = cnF)
    (hnp_ty : NoProjIn blockNames tyA = true)
    (hnp_cty : NoProjIn blockNames cvj.type = true)
    (hnp_pins : ∀ p ∈ pins_lps, NoProjIn blockNames p = true)
    (hrc : RCRep c_pub.t c_pub.lim h rc)
    (hrm : Bytes.RepAddressRef addrTy h a_rm rm)
    (hrm_key : c_pub.κ (ixAddr a_rm) = f_id cvName)
    (hcprj : Bytes.RepAddressRef addrTy h a_cprj cprj)
    (hcprj_key : c_pub.κ (ixAddr a_cprj) = r.ctor)
    (ha_t : Bytes.RepAddressRef addrTy h a_t t_addr)
    (haset : AddrMapAll addrMapEnum (fun _ k _ => advSet k) h aset)
    (hren : RenameMap c_pub.κ c_pub.κ f_id h src dst)
    (hty_rep : TmCExact c_pub.κ h (posOf lps tyA) ty_r)
    (hrhs_rep : TmCExact c_pub.κ h (posOf lps r.rhs) rhs)
    (hcty_rep : TmCExact c_pub.κ h (posOf cvj.levelParams cvj.type) cty)
    (hilvls_rep : RepKLevelList h (lvls_lps.map (Level.subst lps (posLevels lps))) ilvls)
    (hpins_rep : RepList kexprListEnum
      (fun h P p => TmExact c_pub.κ 0 zeroGhost h rP P p) h (pins_lps.map (posOf lps)) pins)
    (ev : ObsFn W "KernelModeled::check_iota_rule"
      [rc, rm, .field (lps.length : F), ty_r, .field (rP : F), .field ((mI - rP) : F),
       rhs, cprj, cty, .field (cnP : F), .field (cnF : F), ilvls, pins, t_addr, src, dst, aset]
      h v_ret h' calls) :
    Nonempty (RawIotaRuleVmRun c_pub c_adv blockNames f_id advSet cvName lps tyA mI rP
      lvls_lps pins_lps j r) := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  have hval0 : ZMod.val (0 : F) = 0 := ZMod.val_zero
  have hval1 : ZMod.val (1 : F) = 1 := rfl
  have hval2 : ZMod.val (2 : F) = 2 := rfl
  have hval3 : ZMod.val (3 : F) = 3 := rfl
  have hκ_eq : c_adv.κ = c_pub.κ := by unfold Ctx.κ; rw [ht_eq]
  have hrc_adv : RCRep c_adv.t c_adv.lim h rc := by rw [ht_eq, hlim_eq]; exact hrc
  have hnd_lps : lps.Nodup := levelParam_nodup_of_perm_range hlps_perm
  let nI : Nat := mI - rP
  let depth : Nat := rP + cnF
  have hrp_val : ZMod.val (rP : F) = rP := SubstAux.val_natCast (by omega)
  have hni_val : ZMod.val (nI : F) = nI := SubstAux.val_natCast (by omega)
  have hcnp_val : ZMod.val (cnP : F) = cnP := SubstAux.val_natCast (by omega)
  have hcnf_val : ZMod.val (cnF : F) = cnF := SubstAux.val_natCast (by omega)
  have hnl_val : ZMod.val (lps.length : F) = lps.length := SubstAux.val_natCast (by omega)
  have hmi_val : ZMod.val (mI : F) = mI := SubstAux.val_natCast (by omega)
  have hd_val : ZMod.val (depth : F) = depth := SubstAux.val_natCast (by omega)
  obtain ⟨inv⟩ := check_iota_rule_inv ev
  have hmi_eq : inv.mi = .field (mI : F) := by
    rw [SubstAux.add_ok inv.op_mi]; congr 1
    exact ZMod.val_injective _ (by rw [SubstAux.val_add (by omega), hrp_val, hni_val, hmi_val]; omega)
  have hd_eq : inv.d = .field (depth : F) := by
    rw [SubstAux.add_ok inv.op_d]; congr 1
    exact ZMod.val_injective _ (by rw [SubstAux.val_add (by omega), hrp_val, hcnf_val, hd_val])
  -- 1. `pins.length = cnP`
  have hpins_lt : (pins_lps.map (posOf lps)).length < 2 ^ 39 :=
    IxVM.Refinement.RomBound.bounded_length_lt hgood_pub.2 inv.call_plen (by simp) hpins_rep
  obtain ⟨hplen_f, h_plen_eq⟩ := tele_klength inv.ev_plen hpins_rep
  subst h_plen_eq
  have hpins_len : pins_lps.length = cnP := by
    injection hplen_f with hf
    have hv := congrArg ZMod.val hf
    rw [hcnp_val, SubstAux.val_natCast (by omega), List.length_map] at hv
    exact hv.symm
  -- 2. Stored `r.rhs` front-end (`validate_expr_well_scoped`, `peel_n_lams_collect`, `k_infer`)
  have hrhs_pos_tm0 : TmExact c_pub.κ 0 zeroGhost h 0 (posOf lps r.rhs) rhs := hrhs_rep 0 zeroGhost
  have hrhs_bvars : r.rhs.looseBVarsBounded 0 = true := by
    have hb := Tm.wscopedB (ghostScoped_zero zeroGhost) hrhs_pos_tm0.toTm
    rwa [Expr.looseBVarsBounded_instantiateLevelParams] at hb
  have hrhs_nofvar : r.rhs.hasFvar = false := by
    have hf := Tm.hasFvar_false hrhs_pos_tm0.toTm
    rwa [Expr.hasFvar_instantiateLevelParams] at hf
  have hrhs_lvls : r.rhs.allLevelParamsDefined lps = true :=
    allLevelParamsDefined_of_posOf_perm hlps_perm
      (validate_expr_well_scoped_spec hlps_lt hrhs_pos_tm0 inv.ev_sc)
  have ext_sc := inv.ev_sc.heap_extends
  have ext_peel_in := ext_sc.trans (Heap.Extends.snoc inv.h_sc _)
  have ev_peel' := inv.ev_peel
  rw [hd_eq] at ev_peel'
  have hrhs_lams_pos : ((posOf lps r.rhs).stripLams depth).isSome = true := by
    have hs := (peel_n_lams_collect_spec_wide (by rw [hd_val]; omega) ev_peel'
      (hrhs_pos_tm0.mono ext_peel_in)).1
    rwa [hd_val] at hs
  have hrhs_lams : (r.rhs.stripLams depth).isSome = true := by
    have hcomm : ∀ (m : Nat) (e : KExpr),
        ((posOf lps e).stripLams m).isSome = (e.stripLams m).isSome := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ m ih =>
        intro e; cases e <;> simp [posOf, Expr.instantiateLevelParams, Expr.stripLams]
        case lam _ b _ => exact ih b
    rwa [hcomm] at hrhs_lams_pos
  have ext_peel := ext_peel_in.trans inv.ev_peel.heap_extends
  have ext_rhs_in := ext_peel.trans (Heap.Extends.snoc inv.h_peel _)
  obtain ⟨rhs_ty_pos, _, hrhs_inf_pos⟩ :=
    core_infer hCore (hrc.mono ext_rhs_in)
      (typesRep_alloc_nil c_pub.κ zeroGhost inv.h_peel) (ghostScoped_zero zeroGhost)
      hef_pub hlf_pub (hgood_pub.sub inv.sub_rhs_inf) inv.ev_rhs_inf
      (hrhs_pos_tm0.toTm.mono ext_rhs_in)
  have hrhs_typed : ∃ t', posRulesJ.infer c_pub.env 0 r.rhs t' :=
    ⟨invPosOf lps rhs_ty_pos, posRulesJ_infer_of_pos hlps_perm hrhs_inf_pos⟩
  have hrhs_cr : r.rhs.constsResolve c_pub.env = true := by
    have hcr := infer_constsResolve hrhs_inf_pos hef_pub.store
      (Tm.hasFvar_false hrhs_pos_tm0.toTm)
    rwa [constsResolve_posOf] at hcr
  have hrhs_noproj : NoProjIn blockNames r.rhs = true := by
    have hnp := infer_noProjIn hrhs_inf_pos hproj_pub (Tm.hasFvar_false hrhs_pos_tm0.toTm)
    rwa [noProjIn_instantiateLevelParams] at hnp
  have ext_rhs_inf := ext_rhs_in.trans inv.ev_rhs_inf.heap_extends
  -- 3. Advice membership & theorem lookup `Ingress::get_ci(t_addr)`
  have hadv_t : advSet a_t :=
    addr_set_member_one (c := c_adv) hroles hef_adv.tableWf
      (Bytes.repAddressRef_heapMono₂ addrTy ext_rhs_inf ha_t)
      (haset.mono ext_rhs_inf) inv.ev_aset
  have ext_aset := ext_rhs_inf.trans inv.ev_aset.heap_extends
  obtain ⟨ci_t, hfind_t0, _, hthm_range, v_tci, ld_tci', hcir_t⟩ :=
    hexact_adv a_t t_addr inv.p_tci inv.h_aset inv.h_tci inv.cs_tci inv.ev_tci
      (hgood_adv.sub inv.sub_tci)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_aset ha_t)
      (not_rec_or_quot_of_load inv.ld_tci (by decide) (by decide))
  rw [inv.ld_tci] at ld_tci'; injection ld_tci' with hv_tci; subst hv_tci
  cases hcir_t with
  | @thm _ _ _ cvt vt hv_t _ =>
    have ht_nl_len : cvt.levelParams.length = lps.length := by
      injection hv_t.1 with hf
      have hv := congrArg ZMod.val hf
      rw [hnl_val, SubstAux.val_natCast (by have := hv_t.2.1; omega)] at hv
      exact hv.symm
    have ht_lps : cvt.levelParams = List.range lps.length := by
      rw [hthm_range cvt vt rfl, ht_nl_len]
    let cvt_lps : KExpr := invPosOf lps cvt.type
    have hcvt_pos_eq : posOf lps cvt_lps = cvt.type := posOf_invPosOf hlps_perm cvt.type
    have htty_rep : TmCExact c_pub.κ inv.h_tci (posOf lps cvt_lps) inv.tty := by
      have hrep0 := hv_t.2.2.2
      rw [ht_lps, posOf_range lps.length cvt.type, ← hcvt_pos_eq, hκ_eq] at hrep0
      exact hrep0
    have ext_tci := ext_aset.trans inv.ev_tci.heap_extends
    -- 4. Opening `tty` at `depth = rP + cnF` (`peel_collect`)
    have ext_open_in := Heap.Extends.snoc inv.h_tci (.construct kexprListEnum "Nil" [])
    have ev_open' := inv.ev_open
    rw [hd_eq] at ev_open'
    obtain ⟨r_tbody, r_ctx, Γ_t, fvs_pos, tbody_pos, htup_open, hopen_pos, _, hΓt_hi,
        htbody_ex, hctx_rep, hsc_t⟩ :=
      peel_collect_open_exact depth hd_val ev_open'
        ((htty_rep 0 zeroGhost).mono ext_open_in)
        (typesRep_alloc_nil c_pub.κ zeroGhost inv.h_tci)
        (ghostScoped_zero zeroGhost)
    injection htup_open with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    rw [Nat.zero_add] at hΓt_hi htbody_ex hctx_rep hsc_t
    obtain ⟨fvs, tbody, hopen_t, hfvs_pos, htbody_pos⟩ := openPisAtFvars_of_posOf hopen_pos
    obtain ⟨hfvs_len, _, hfvs_shape⟩ := openPisAtFvars_spec depth cvt_lps 0 hopen_t
    have hfvs_pos_len : fvs_pos.length = depth := by rw [hfvs_pos, List.length_map, hfvs_len]
    have ext_open := ext_tci.trans (ext_open_in.trans inv.ev_open.heap_extends)
    -- 5. Equation spine (`collect_spine(tbody)`, `eqName`, `[ell]`, `targs.length = 3`)
    obtain ⟨r_eqh, r_targs, eqH_pos, targs_pos, htup_tsp, heqH_ex, htargs_rep, htbody_app⟩ :=
      collect_spine_exact inv.ev_tsp htbody_ex
    injection htup_tsp with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    obtain ⟨a_eq, eqls_pos, rfl, ra_eq, reqls⟩ := heqH_ex.const_of_load inv.ld_eqh
    have ext_tsp := ext_open.trans inv.ev_tsp.heap_extends
    have ext_req := ext_tsp.trans inv.ev_req.heap_extends
    have ext_raddr := ext_req.trans inv.ev_raddr.heap_extends
    obtain ⟨heq_key_adv, h_eqa_eq⟩ :=
      eq_addr_key_spec (c := c_adv) hroles hef_adv.tableWf (hgood_adv.sub inv.sub_raddr)
        (hrc_adv.mono ext_req) (Bytes.repAddressRef_heapMono₂ addrTy ext_raddr ra_eq)
        inv.ev_req inv.ev_raddr inv.ev_eqa
    subst h_eqa_eq
    have heq_key : c_pub.κ (ixAddr a_eq) = eqName := by rwa [hκ_eq] at heq_key_adv
    have reqls_eqa := reqls.mono (inv.ev_req.heap_extends.trans inv.ev_raddr.heap_extends)
    have hld_eqls1' := inv.ld_eqls1
    have hld_eqls2' := inv.ld_eqls2
    rw [klevelListEnum_eq] at hld_eqls1' hld_eqls2'
    obtain ⟨ell_pos, eqls_tail, heqls_cons, rell_pos, reqls_tail⟩ :=
      Lib.rep_cons_of_load reqls_eqa hld_eqls1'
    obtain rfl := Lib.rep_nil_of_load reqls_tail hld_eqls2'
    subst heqls_cons
    let ell_lps : KLevel := invPosLevel lps ell_pos
    have hell_subst : Level.subst lps (posLevels lps) ell_lps = ell_pos :=
      subst_invPosLevel hlps_perm ell_pos
    have heq_head : tbody.getAppFn = .const eqName [ell_lps] := by
      have hfn_pos : tbody_pos.getAppFn = .const eqName [ell_pos] := by
        rw [htbody_app, getAppFn_mkAppN, heq_key]; rfl
      rw [htbody_pos, ← hell_subst] at hfn_pos
      exact posOf_inj hlps_perm (by
        show posOf lps tbody.getAppFn = posOf lps (.const eqName [ell_lps])
        unfold posOf
        rw [← getAppFn_instantiateLevelParams]
        exact hfn_pos)
    have htargs_pos_eq : targs_pos = tbody.getAppArgs.map (posOf lps) := by
      have h1 : tbody_pos.getAppArgs = targs_pos := by
        rw [htbody_app, getAppArgs_mkAppN]; rfl
      rw [htbody_pos] at h1
      unfold posOf at h1
      rw [getAppArgs_instantiateLevelParams] at h1
      exact h1.symm
    have htargs_eqa := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e)
      (inv.ev_req.heap_extends.trans inv.ev_raddr.heap_extends) htargs_rep
    have htargs_lt : targs_pos.length < 2 ^ 39 :=
      IxVM.Refinement.RomBound.bounded_length_lt hgood_pub.2 inv.call_tlen (by simp) htargs_eqa
    obtain ⟨htlen_f, h_tlen_eq⟩ := tele_klength inv.ev_tlen htargs_eqa
    subst h_tlen_eq
    have htargs_len : tbody.getAppArgs.length = 3 := by
      injection htlen_f with hf
      have hv := congrArg ZMod.val hf
      rw [hval3, SubstAux.val_natCast (by omega), htargs_pos_eq, List.length_map] at hv
      exact hv.symm
    let alphaS := tbody.getAppArgs.getD 0 (.bvar 0)
    let lhsS := tbody.getAppArgs.getD 1 (.bvar 0)
    let rhsS := tbody.getAppArgs.getD 2 (.bvar 0)
    obtain ⟨⟨alpha_pos, ha0_get, halpha_ex⟩, h_a0_eq⟩ := tele_klookup inv.ev_a0 htargs_eqa
    subst h_a0_eq
    obtain ⟨⟨lhs_pos, ha1_get, hlhs_ex⟩, h_a1_eq⟩ := tele_klookup inv.ev_a1 htargs_eqa
    subst h_a1_eq
    obtain ⟨⟨rhsS_pos, ha2_get, hrhsS_ex⟩, h_a2_eq⟩ := tele_klookup inv.ev_a2 htargs_eqa
    subst h_a2_eq
    rw [hval0, htargs_pos_eq, List.getElem?_map] at ha0_get
    rw [hval1, htargs_pos_eq, List.getElem?_map] at ha1_get
    rw [hval2, htargs_pos_eq, List.getElem?_map] at ha2_get
    have halpha_pos : alpha_pos = posOf lps alphaS := by
      have h0 : tbody.getAppArgs[0]? = some alphaS := by
        cases hts : tbody.getAppArgs with
        | nil => simp [hts] at htargs_len
        | cons x0 xs => simp [alphaS, hts]
      rw [h0] at ha0_get; injection ha0_get with h; exact h.symm
    have hlhs_pos : lhs_pos = posOf lps lhsS := by
      have h1 : tbody.getAppArgs[1]? = some lhsS := by
        rcases hts : tbody.getAppArgs with _ | ⟨x0, _ | ⟨x1, xs⟩⟩
        · simp [hts] at htargs_len
        · simp [hts] at htargs_len
        · simp [lhsS, hts]
      rw [h1] at ha1_get; injection ha1_get with h; exact h.symm
    have hrhsS_pos : rhsS_pos = posOf lps rhsS := by
      have h2 : tbody.getAppArgs[2]? = some rhsS := by
        rcases hts : tbody.getAppArgs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, xs⟩⟩⟩
        · simp [hts] at htargs_len
        · simp [hts] at htargs_len
        · simp [hts] at htargs_len
        · simp [rhsS, hts]
      rw [h2] at ha2_get; injection ha2_get with h; exact h.symm
    subst halpha_pos hlhs_pos hrhsS_pos
    -- 6. Left-hand side spine, head, prefix variables, and major premise
    obtain ⟨r_lh, r_largs, lh_pos, largs_pos, htup_lsp, hlh_ex, hlargs_rep, hlhs_app⟩ :=
      collect_spine_exact inv.ev_lsp hlhs_ex
    injection htup_lsp with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    have hplvls_rep := build_param_lvls_range_spec (by rw [hnl_val]; exact hlps_lt) inv.ev_plvls
    rw [hnl_val] at hplvls_rep
    have ext_lsp := inv.ev_lsp.heap_extends
    have ext_plvls := ext_lsp.trans inv.ev_plvls.heap_extends
    have ext_rhead := Heap.Extends.snoc inv.h_plvls (.construct kexprEnum "Const" [rm, inv.v_plvls])
    have ext_h_to_rhead :=
      ext_raddr.trans (ext_plvls.trans ext_rhead)
    have hrhead_ex : TmExact c_pub.κ depth Γ_t
        (inv.h_plvls ++ [.construct kexprEnum "Const" [rm, inv.v_plvls]]) 0
        (posOf lps (.const (f_id cvName) (lps.map .param)))
        (.ptr (.enum kexprEnum) inv.h_plvls.length) := by
      rw [posOf_const_self_levels lps (f_id cvName) hnd_lps, ← hrm_key]
      exact .const (by simp)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_h_to_rhead hrm)
        (hplvls_rep.mono ext_rhead)
    have hlh_eq_pos : lh_pos = posOf lps (.const (f_id cvName) (lps.map .param)) :=
      kexpr_struct_eq_one (hlh_ex.mono (inv.ev_plvls.heap_extends.trans ext_rhead))
        hrhead_ex inv.ev_lheq
    have hlhs_fn : lhsS.getAppFn = .const (f_id cvName) (lps.map .param) := by
      have hfn_pos : (posOf lps lhsS).getAppFn = posOf lps (.const (f_id cvName) (lps.map .param)) := by
        rw [hlhs_app, getAppFn_mkAppN, hlh_eq_pos,
          posOf_const_self_levels lps (f_id cvName) hnd_lps]; rfl
      exact posOf_inj hlps_perm (by
        unfold posOf at hfn_pos ⊢
        rwa [← getAppFn_instantiateLevelParams])
    have hlargs_pos_eq : largs_pos = lhsS.getAppArgs.map (posOf lps) := by
      have h1 : (posOf lps lhsS).getAppArgs = largs_pos := by
        rw [hlhs_app, getAppArgs_mkAppN, hlh_eq_pos,
          posOf_const_self_levels lps (f_id cvName) hnd_lps]; rfl
      unfold posOf at h1
      rw [getAppArgs_instantiateLevelParams] at h1
      exact h1.symm
    have ext_lsp_lheq := inv.ev_plvls.heap_extends.trans
      (ext_rhead.trans inv.ev_lheq.heap_extends)
    have hlargs_lheq := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext_lsp_lheq hlargs_rep
    have hlargs_lt : largs_pos.length < 2 ^ 39 :=
      IxVM.Refinement.RomBound.bounded_length_lt hgood_pub.2 inv.call_llen (by simp) hlargs_lheq
    obtain ⟨hllen_f, h_llen_eq⟩ := tele_klength inv.ev_llen hlargs_lheq
    subst h_llen_eq
    have hlargs_len : lhsS.getAppArgs.length = mI + 1 := by
      have hmi1_eq := inv.op_mi1
      rw [hmi_eq] at hmi1_eq
      rw [SubstAux.add_ok hmi1_eq] at hllen_f
      injection hllen_f with hf
      have hv := congrArg ZMod.val hf
      rw [SubstAux.val_natCast (by omega), SubstAux.val_add (by omega), hmi_val, hval1,
        hlargs_pos_eq, List.length_map] at hv
      exact hv
    -- Prefix check: `largs.take rP = fvs.take rP`
    obtain ⟨_, hltake_rep⟩ := tele_ktake (fun _ _ _ _ e x => x.mono e) inv.ev_ltake hlargs_lheq
    rw [hrp_val] at hltake_rep
    have ev_bvd1' := inv.ev_bvd1
    rw [hd_eq] at ev_bvd1'
    have hbvd1_rep := bvars_desc_exact_wide (κ := c_pub.κ) (d := depth) (Γ := Γ_t)
      (by rw [hrp_val, hd_val]; omega) (by rw [hd_val]) (by omega) ev_bvd1'
    rw [hrp_val, hd_val, Nat.sub_self] at hbvd1_rep
    have hbvd1_fvs :
        ((List.range rP).map fun m => Expr.fvar (0 + m) (Γ_t (0 + m))) =
          (fvs.take rP).map (posOf lps) := by
      have hlen_take : ((fvs.take rP).map (posOf lps)).length = rP := by
        simp [hfvs_len]; omega
      apply List.ext_getElem (by simp [hlen_take])
      intro m hm1 hm2
      simp only [List.length_map, List.length_range] at hm1
      have hm_lt : m < fvs_pos.length := by rw [hfvs_pos_len]; omega
      have hΓm := hΓt_hi m hm_lt
      have hfv_pos_m : fvs_pos[m] = .fvar m (fvs_pos[m].fvarTypeD) := by
        rw [hfvs_pos]
        simp only [List.getElem_map]
        have hm_fvs : m < fvs.length := by rw [hfvs_len]; omega
        have hsh := hfvs_shape m hm_fvs
        rw [Nat.zero_add] at hsh
        conv_lhs => rw [hsh]
        simp [posOf, Expr.instantiateLevelParams, Expr.fvarTypeD]
      simp only [List.getElem_map, List.getElem_range, Nat.zero_add, hΓm, ← hfv_pos_m]
      simp [hfvs_pos, List.getElem_take]
    rw [hbvd1_fvs] at hbvd1_rep
    have hltake_eq_pos :
        largs_pos.take rP = (fvs.take rP).map (posOf lps) :=
      spec_params_ptr_eq_one (RepLinkedList.mono (fun _ _ _ _ e x => x.mono e)
        inv.ev_bvd1.heap_extends hltake_rep) hbvd1_rep inv.ev_pref
    have hlargs_pre : lhsS.getAppArgs.take rP = fvs.take rP := by
      rw [hlargs_pos_eq, ← List.map_take] at hltake_eq_pos
      exact List.map_injective_iff.mpr (posOf_inj hlps_perm) hltake_eq_pos
    -- Major premise check
    have ext_lheq_pref := inv.ev_ltake.heap_extends.trans
      (inv.ev_bvd1.heap_extends.trans inv.ev_pref.heap_extends)
    have hlargs_pref := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext_lheq_pref hlargs_lheq
    have ev_maj' := inv.ev_maj
    rw [hmi_eq] at ev_maj'
    obtain ⟨⟨major_pos, hmaj_get, hmaj_ex⟩, h_maj_eq⟩ := tele_klookup ev_maj' hlargs_pref
    subst h_maj_eq
    rw [hmi_val, hlargs_pos_eq, List.getElem?_map] at hmaj_get
    have hmaj_last : major_pos = posOf lps (lhsS.getAppArgs.getLastD (.bvar 0)) := by
      cases hget_m : lhsS.getAppArgs[mI]? with
      | none => simp [hget_m] at hmaj_get
      | some mj =>
        rw [hget_m] at hmaj_get; injection hmaj_get with hmj; subst hmj
        rw [getLastD_eq_of_getElem? lhsS.getAppArgs mI mj (.bvar 0) hlargs_len hget_m]
    have ext_h_pref := ext_raddr.trans (inv.ev_lsp.heap_extends.trans
      (ext_lsp_lheq.trans ext_lheq_pref))
    obtain ⟨⟨a_cren, ra_cren, hcren_key⟩, h_cren_eq⟩ :=
      rename_addr_spec inv.ev_cren
        (Bytes.repAddressRef_heapMono₂ addrTy ext_h_pref hcprj)
        (hren.mono ext_h_pref)
    subst h_cren_eq
    rw [hcprj_key] at hcren_key
    have hpins_ren_rep := rename_list_exact (Γ₂ := zeroGhost) inv.ev_pren
      (RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext_h_pref hpins_rep)
      (hren.mono ext_h_pref)
    have hpins_ren_eq :
        (pins_lps.map (posOf lps)).map (renameAll f_id) =
          (pins_lps.map (·.renameConsts f_id)).map (posOf lps) := by
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro p hp
      simp only [Function.comp_apply]
      have hnp_p : NoProjIn blockNames (posOf lps p) = true := by
        unfold posOf; rw [noProjIn_instantiateLevelParams]; exact hnp_pins p hp
      rw [renameAll_eq_renameConsts_of_noProjIn hf_out hnp_p]
      unfold posOf
      exact (Ix.Kernel.Expr.renameConsts_instantiateLevelParams f_id lps (posLevels lps) p).symm
    rw [hpins_ren_eq] at hpins_ren_rep
    -- Open `pins_ren` at `fvs.take rP` (depth `rP`, ghost `Γ_t`), then `lift_list` by `cnF` to `depth`
    let pinsF_lps : List KExpr :=
      pins_lps.map fun p => Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f_id)
    have hpins_ren_open :
        RepList kexprListEnum (fun h P p => TmExact c_pub.κ rP Γ_t h 0 P p) inv.h_pren
          (pinsF_lps.map (posOf lps)) inv.pins_ren := by
      have hlist_eq :
          ((pins_lps.map (·.renameConsts f_id)).map (posOf lps)).map
            (fun P => Expr.instSpine ((List.range rP).map fun j => .fvar j (Γ_t j)) (rP - 1) P) =
            pinsF_lps.map (posOf lps) := by
        have hpre_eq : ((List.range rP).map fun j => Expr.fvar j (Γ_t j)) =
            (fvs.take rP).map (posOf lps) := by
          simpa [Nat.zero_add] using hbvd1_fvs
        rw [hpre_eq, List.map_map, List.map_map]
        dsimp only [pinsF_lps]
        rw [List.map_map]
        apply List.map_congr_left
        intro p _; simp only [Function.comp_apply]
        unfold posOf
        exact (Ix.Kernel.Expr.instSpine_instantiateLevelParams lps (posLevels lps)
          (fvs.take rP) (rP - 1) (p.renameConsts f_id)).symm
      rw [← hlist_eq]
      clear hlist_eq
      generalize ((pins_lps.map (·.renameConsts f_id)).map (posOf lps)) = qs at hpins_ren_rep
      induction hpins_ren_rep with
      | nil cell => exact .nil cell
      | cons cell hhead _ ih => exact .cons cell (hhead.open_prefix_eq Γ_t) ih
    have hpd_rep := lift_list_exact (bounded_sub inv.sub_pd hgood_pub.2)
      (by rw [hcnf_val]; omega) inv.ev_pd hpins_ren_open
    rw [hcnf_val] at hpd_rep
    have ext_pd_c := Heap.Extends.snoc inv.h_pd (.construct kexprEnum "Const" [inv.cren, ilvls])
    have ext_h_pd := ext_h_pref.trans (inv.ev_pren.heap_extends.trans inv.ev_pd.heap_extends)
    have hchead_exp_ex : TmExact c_pub.κ depth Γ_t
        (inv.h_pd ++ [.construct kexprEnum "Const" [inv.cren, ilvls]]) 0
        (posOf lps (.const (f_id r.ctor) lvls_lps))
        (.ptr (.enum kexprEnum) inv.h_pd.length) := by
      unfold posOf
      simp only [Expr.instantiateLevelParams]
      rw [hcren_key]
      exact .const (by simp)
        (Bytes.repAddressRef_heapMono₂ addrTy
          (inv.ev_pren.heap_extends.trans (inv.ev_pd.heap_extends.trans ext_pd_c)) ra_cren)
        (hilvls_rep.mono (ext_h_pd.trans ext_pd_c))
    have hbvd2_rep := bvars_desc_exact_wide (κ := c_pub.κ) (d := depth) (Γ := Γ_t)
      (by rw [hcnf_val]) (by rw [hcnf_val]; omega) (by omega) inv.ev_bvd2
    rw [hcnf_val, show depth - cnF = rP by omega] at hbvd2_rep
    have hbvd2_fvs :
        ((List.range cnF).map fun m => Expr.fvar (rP + m) (Γ_t (rP + m))) =
          (fvs.drop rP).map (posOf lps) := by
      have hlen_drop : ((fvs.drop rP).map (posOf lps)).length = cnF := by
        simp [hfvs_len]; omega
      apply List.ext_getElem (by simp [hlen_drop])
      intro m hm1 hm2
      simp only [List.length_map, List.length_range] at hm1
      have hm_lt : rP + m < fvs_pos.length := by rw [hfvs_pos_len]; omega
      have hΓm := hΓt_hi (rP + m) hm_lt
      have hm_fvs : rP + m < fvs.length := by rw [hfvs_len]; omega
      have hfv_pos_m : fvs_pos[rP + m] = .fvar (rP + m) (fvs_pos[rP + m].fvarTypeD) := by
        rw [hfvs_pos]; simp only [List.getElem_map]
        have hsh := hfvs_shape (rP + m) hm_fvs
        rw [Nat.zero_add] at hsh
        conv_lhs => rw [hsh]
        simp [posOf, Expr.instantiateLevelParams, Expr.fvarTypeD]
      simp only [List.getElem_map, List.getElem_range, hΓm, ← hfv_pos_m]
      simp [hfvs_pos, List.getElem_drop]
    rw [hbvd2_fvs] at hbvd2_rep
    have hcat_rep := tele_kconcat (fun _ _ _ _ e x => x.mono e) inv.ev_cat
      (RepLinkedList.mono (fun _ _ _ _ e x => x.mono e)
        (ext_pd_c.trans inv.ev_bvd2.heap_extends) hpd_rep)
      hbvd2_rep
    have hexp_ex := apply_spine_exact inv.ev_exp
      (hchead_exp_ex.mono (inv.ev_bvd2.heap_extends.trans inv.ev_cat.heap_extends)) hcat_rep
    have hexp_pos_eq :
        Expr.mkAppN (posOf lps (.const (f_id r.ctor) lvls_lps))
          (pinsF_lps.map (posOf lps) ++ (fvs.drop rP).map (posOf lps)) =
          posOf lps (Expr.mkAppN (.const (f_id r.ctor) lvls_lps) (pinsF_lps ++ fvs.drop rP)) := by
      rw [← List.map_append]
      unfold posOf
      exact (mkAppN_instantiateLevelParams lps (posLevels lps)
        (pinsF_lps ++ fvs.drop rP) (.const (f_id r.ctor) lvls_lps)).symm
    rw [hexp_pos_eq] at hexp_ex
    have ext_pref_exp := inv.ev_pren.heap_extends.trans (inv.ev_pd.heap_extends.trans
      (ext_pd_c.trans (inv.ev_bvd2.heap_extends.trans
        (inv.ev_cat.heap_extends.trans inv.ev_exp.heap_extends))))
    have hmajor_pos_eq := kexpr_struct_eq_one (hmaj_ex.mono ext_pref_exp) hexp_ex inv.ev_majeq
    rw [hmaj_last] at hmajor_pos_eq
    have hmajor_eq :
        lhsS.getAppArgs.getLastD (.bvar 0) =
          Expr.mkAppN (.const (f_id r.ctor) lvls_lps) (pinsF_lps ++ fvs.drop rP) :=
      posOf_inj hlps_perm hmajor_pos_eq
    -- 7. Constructor telescope (`cty_l`, `ctorTeleOk`, `crest`, `cres`, index `defeq_list_ok`)
    have ext_h_majeq := ext_h_pref.trans (ext_pref_exp.trans inv.ev_majeq.heap_extends)
    have hcvj_def : cvj.type.allLevelParamsDefined cvj.levelParams = true :=
      (hef_pub.store.wf _ _ hfind_ctor).2.2.1
    let cty_inst : KExpr := cvj.type.instantiateLevelParams cvj.levelParams lvls_lps
    have hctyl_tm0 : Tm c_pub.κ 0 zeroGhost inv.h_ctyl 0 (posOf lps cty_inst) inv.cty_l := by
      have hinst := SubstAux.gall c_pub.κ .expr_inst_levels [cty, ilvls] inv.h_majeq inv.cty_l
        inv.h_ctyl inv.cs_ctyl inv.ev_ctyl cty ilvls rfl
        (bounded_sub inv.sub_ctyl hgood_pub.2) zeroGhost 0 (posOf cvj.levelParams cvj.type)
        (lvls_lps.map (Level.subst lps (posLevels lps)))
        ((hcty_rep 0 zeroGhost).toTm.mono ext_h_majeq)
        ⟨_, hilvls_rep.mono ext_h_majeq, LvEqList.refl _⟩
      rwa [posOf_instantiateLevelParams_eq hlvls_len hcvj_def] at hinst
    have hcnp_cnf_eq : inv.cnp_cnf = .field ((cnP + cnF) : F) := by
      rw [SubstAux.add_ok inv.op_cnp_cnf]; congr 1
      exact ZMod.val_injective _ (by
        rw [SubstAux.val_add (by omega), hcnp_val, hcnf_val, SubstAux.val_natCast (by omega)])
    have ev_peel0' := inv.ev_peel0
    rw [hcnp_cnf_eq] at ev_peel0'
    obtain ⟨bs0_pos, rem0_pos, hstrip0_pos, hrem0_tm, h_peel0_eq⟩ :=
      peel_n_foralls_tm (cnP + cnF) (SubstAux.val_natCast (by omega)) ev_peel0' hctyl_tm0
    subst h_peel0_eq; rw [Nat.zero_add] at hrem0_tm
    obtain ⟨r_ch0, r_ca0, ch0_pos, ca0_pos, htup_csp0, hch0_tm, _, hrem0_app⟩ :=
      SubstAux.gall c_pub.κ .collect_spine [inv.v_peel0] inv.h_ctyl
        (.tuple [inv.chead0, inv.cargs0]) inv.h_csp0 inv.cs_csp0 inv.ev_csp0 inv.v_peel0 rfl
        (bounded_sub inv.sub_csp0 hgood_pub.2) 0 zeroGhost (cnP + cnF) rem0_pos hrem0_tm
    injection htup_csp0 with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    obtain ⟨a_ch0, us_ch0, rfl, _, _, _, _⟩ := hch0_tm.const_of_load inv.ld_chead0
    have hrem0_fn : rem0_pos.getAppFn = .const (c_pub.κ (ixAddr a_ch0)) us_ch0 := by
      rw [hrem0_app, getAppFn_mkAppN]; rfl
    obtain ⟨bs_inst, cbody_inst, usc_inst, hstrip_inst, hfn_inst, _⟩ :=
      stripPis_constHead_of_instantiateLevelParams lps (posLevels lps) (cnP + cnF) cty_inst
        hstrip0_pos hrem0_fn
    obtain ⟨cbinders, cbody0, usc0, hstrip_cvj, hfn_cvj, hctor_tele⟩ :=
      stripPis_constHead_of_instantiateLevelParams cvj.levelParams lvls_lps (cnP + cnF) cvj.type
        hstrip_inst hfn_inst
    have hctor_head : ∃ cbinders cbody0 Dc usc,
        cvj.type.stripPis (cnP + cnF) = some (cbinders, cbody0) ∧ cbody0.getAppFn = .const Dc usc :=
      ⟨cbinders, cbody0, _, usc0, hstrip_cvj, hfn_cvj⟩
    have ext_ctyl_csp0 := inv.ev_csp0.heap_extends
    have ext_h_csp0 := ext_h_majeq.trans (inv.ev_ctyl.heap_extends.trans ext_ctyl_csp0)
    have hcty_ren_tm0 : Tm c_pub.κ 0 zeroGhost inv.h_cty_ren 0
        (posOf lps (cty_inst.renameConsts f_id)) inv.v_cty_ren := by
      have hr := rename_tm (Γ₂ := zeroGhost) inv.ev_cty_ren
        (hctyl_tm0.mono ext_ctyl_csp0) (hren.mono ext_h_csp0)
      have hnp_inst : NoProjIn blockNames (posOf lps cty_inst) = true := by
        unfold posOf cty_inst
        rw [noProjIn_instantiateLevelParams, noProjIn_instantiateLevelParams]
        exact hnp_cty
      rw [renameAll_eq_renameConsts_of_noProjIn hf_out hnp_inst] at hr
      have hcomm : (posOf lps cty_inst).renameConsts f_id = posOf lps (cty_inst.renameConsts f_id) := by
        unfold posOf
        exact (Ix.Kernel.Expr.renameConsts_instantiateLevelParams f_id lps (posLevels lps) cty_inst).symm
      rwa [hcomm] at hr
    have ext_pren_ctyren := inv.ev_pd.heap_extends.trans (ext_pd_c.trans
      (inv.ev_bvd2.heap_extends.trans (inv.ev_cat.heap_extends.trans
        (inv.ev_exp.heap_extends.trans (inv.ev_majeq.heap_extends.trans
          (inv.ev_ctyl.heap_extends.trans (ext_ctyl_csp0.trans inv.ev_cty_ren.heap_extends)))))))
    have hpins_ren_tm_rp :
        RepList kexprListEnum (fun h P p => Tm c_pub.κ rP Γ_t h 0 P p) inv.h_cty_ren
          (pinsF_lps.map (posOf lps)) inv.pins_ren := by
      have h1 := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext_pren_ctyren hpins_ren_open
      clear ext_pren_ctyren
      induction h1 with
      | nil cell => exact .nil cell
      | cons cell hh _ ih => exact .cons cell hh.toTm ih
    obtain ⟨cdoms1_pos, crest_pos, hinst_c1_pos, hcrest_tm⟩ :=
      inst_params_tm (bounded_sub inv.sub_crest hgood_pub.2) inv.ev_crest
        (hcty_ren_tm0.of_depth_zero rP) hpins_ren_tm_rp
    obtain ⟨cdoms1, crest_lps, hinst_c1, hcdoms1_pos, hcrest_pos⟩ := instPisAt_of_posOf hinst_c1_pos
    subst hcdoms1_pos hcrest_pos
    have ext_crest_in := Heap.Extends.snoc inv.h_crest (.construct kexprListEnum "Nil" [])
    have hdrop_fvs_len : ZMod.val (cnF : F) = ((fvs.drop rP).map (posOf lps)).length := by
      rw [hcnf_val, List.length_map, List.length_drop, hfvs_len]; omega
    have hdrop_fvs_Γ : ∀ m (hm : m < ((fvs.drop rP).map (posOf lps)).length),
        Expr.fvar (rP + m) (Γ_t (rP + m)) = ((fvs.drop rP).map (posOf lps))[m] := by
      intro m hm
      have hm_cnF : m < cnF := by rw [← hcnf_val, hdrop_fvs_len] at hm; exact hm
      have h1 := congrArg (·[m]?) hbvd2_fvs
      rw [List.getElem?_map, List.getElem?_range hm_cnF, Option.map_some,
        List.getElem?_eq_getElem hm] at h1
      exact Option.some.inj h1
    obtain ⟨r_cres, _, cdoms2_pos, cres_pos, htup_cres, hinst_c2_pos, hcres_tm⟩ :=
      peel_collect_inst_tm hdrop_fvs_len hdrop_fvs_Γ inv.ev_cres (hcrest_tm.mono ext_crest_in)
    injection htup_cres with hl; injection hl with h1 _; subst h1
    rw [show rP + ((fvs.drop rP).map (posOf lps)).length = depth by
      rw [ ← hdrop_fvs_len, hcnf_val]] at hcres_tm
    obtain ⟨cdoms2, cres, hinst_c2, hcdoms2_pos, hcres_pos⟩ := instPisAt_of_posOf hinst_c2_pos
    subst hcdoms2_pos hcres_pos
    let cdoms := cdoms1 ++ cdoms2
    have hinst_c : Expr.instPisAt (pinsF_lps ++ fvs.drop rP) (cty_inst.renameConsts f_id) =
        some (cdoms, cres) := by
      rw [instPisAt_append, hinst_c1, Option.map_eq_some_iff]
      exact ⟨(cdoms2, cres), hinst_c2, rfl⟩
    have hcdoms_drop : cdoms.drop cnP = cdoms2 := by
      have hlen1 : cdoms1.length = cnP := by
        rw [instPisAt_length hinst_c1]; simp [pinsF_lps, hpins_len]
      simp [cdoms, List.drop_append, hlen1]
    obtain ⟨r_ch, r_ca, ch_pos, cargs_pos, htup_csp, hch_tm, hcargs_rep, hcres_app⟩ :=
      SubstAux.gall c_pub.κ .collect_spine [inv.cres] inv.h_cres
        (.tuple [inv.chead, inv.cargs]) inv.h_csp inv.cs_csp inv.ev_csp inv.cres rfl
        (bounded_sub inv.sub_csp hgood_pub.2) depth Γ_t 0 (posOf lps cres) hcres_tm
    injection htup_csp with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    obtain ⟨a_ch, us_ch, rfl, _, _, _, _⟩ := hch_tm.const_of_load inv.ld_chead
    have hcargs_pos_eq : cargs_pos = cres.getAppArgs.map (posOf lps) := by
      have h1 : (posOf lps cres).getAppArgs = cargs_pos := by
        rw [hcres_app, getAppArgs_mkAppN]; rfl
      unfold posOf at h1
      rw [getAppArgs_instantiateLevelParams] at h1
      exact h1.symm
    have hcargs_lt : cargs_pos.length < 2 ^ 39 :=
      IxVM.Refinement.RomBound.bounded_length_lt hgood_pub.2 inv.call_clen (by simp) hcargs_rep
    obtain ⟨hclen_f, h_clen_eq⟩ := tele_klength inv.ev_clen hcargs_rep
    subst h_clen_eq
    have hcres_len : cres.getAppArgs.length = cnP + nI := by
      rw [SubstAux.add_ok inv.op_cnp_ni] at hclen_f
      injection hclen_f with hf
      have hv := congrArg ZMod.val hf
      rw [SubstAux.val_natCast (by omega), SubstAux.val_add (by omega), hcnp_val, hni_val,
        hcargs_pos_eq, List.length_map] at hv
      exact hv
    -- Deduce `cbody_inst.getAppArgs.length = cnP + nI` via `instPisAt_constHead` on `cty_inst.renameConsts f_id`
    have hcbody_inst_len : cbody_inst.getAppArgs.length = cnP + nI := by
      have hstrip_ren := stripPis_renameConsts f_id (cnP + cnF) cty_inst hstrip_inst
      have hfn_ren : (cbody_inst.renameConsts f_id).getAppFn =
          .const (f_id (c_pub.κ (ixAddr a_ch0))) usc_inst := by
        rw [getAppFn_renameConsts, hfn_inst]; rfl
      have hlen_ren : (cbody_inst.renameConsts f_id).getAppArgs.length =
          cbody_inst.getAppArgs.length := by
        rw [getAppArgs_renameConsts, List.length_map]
      have hpfx_len : (pinsF_lps ++ fvs.drop rP).length + 0 = cnP + cnF := by
        simp [pinsF_lps, hpins_len, hfvs_len]; omega
      rw [← hpfx_len] at hstrip_ren
      obtain ⟨_, cres', _, cbody_r, hinst_r', hs0, _, hlen_r⟩ :=
        instPisAt_constHead _ _ cbody_inst.getAppArgs.length (pinsF_lps ++ fvs.drop rP) 0
          (cty_inst.renameConsts f_id) hstrip_ren hfn_ren hlen_ren
      rw [hinst_c] at hinst_r'; injection hinst_r' with hp; injection hp with _ hcr; subst hcr
      injection hs0 with hp; injection hp with _ hcb; subst hcb
      exact hlen_r.symm.trans hcres_len
    -- Index `defeq_list_ok` (`c_adv`)
    have ext_pref_csp := ext_pref_exp.trans (inv.ev_majeq.heap_extends.trans
      (inv.ev_ctyl.heap_extends.trans (ext_ctyl_csp0.trans (inv.ev_cty_ren.heap_extends.trans
        (inv.ev_crest.heap_extends.trans (ext_crest_in.trans
          (inv.ev_cres.heap_extends.trans inv.ev_csp.heap_extends)))))))
    have hlargs_csp := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext_pref_csp hlargs_pref
    obtain ⟨_, hldrop_rep, h_ldrop_eq⟩ := tele_kdrop inv.ev_ldrop hlargs_csp
    subst h_ldrop_eq; rw [hrp_val] at hldrop_rep
    obtain ⟨_, hidxl_rep⟩ := tele_ktake (fun _ _ _ _ e x => x.mono e) inv.ev_idxl hldrop_rep
    rw [hni_val] at hidxl_rep
    have hcargs_idxl := RepLinkedList.mono tmE_heapMono₂ inv.ev_idxl.heap_extends hcargs_rep
    obtain ⟨_, hidxr_rep, h_idxr_eq⟩ := tele_kdrop inv.ev_idxr hcargs_idxl
    subst h_idxr_eq; rw [hcnp_val] at hidxr_rep
    have hidxl_tm : RepList kexprListEnum (fun h X p => Tm c_adv.κ depth Γ_t h 0 X p) inv.h_idxl
        (((lhsS.getAppArgs.drop rP).take nI).map (posOf lps)) inv.v_idxl := by
      rw [hκ_eq, hlargs_pos_eq, ← List.map_drop, ← List.map_take] at hidxl_rep ⊢
      induction hidxl_rep with
      | nil cell => exact .nil cell
      | cons cell hh _ ih => exact .cons cell hh.toTm ih
    have hidxr_tm : RepList kexprListEnum (fun h Y p => Tm c_adv.κ depth Γ_t h 0 Y p) inv.h_idxl
        ((cres.getAppArgs.drop cnP).map (posOf lps)) inv.v_idxr := by
      rw [hκ_eq]; rwa [hcargs_pos_eq, ← List.map_drop] at hidxr_rep
    have ext_open_idxl := inv.ev_tsp.heap_extends.trans (inv.ev_req.heap_extends.trans
      (inv.ev_raddr.heap_extends.trans (inv.ev_lsp.heap_extends.trans
        (ext_lsp_lheq.trans (ext_lheq_pref.trans
          (ext_pref_csp.trans inv.ev_idxl.heap_extends))))))
    have ext_h_idxl := ext_open.trans ext_open_idxl
    have hde_idx : DefEqListJ posRulesJ c_adv.env depth
        ((lhsS.getAppArgs.drop rP).take nI) (cres.getAppArgs.drop cnP) :=
      rawDefEqList_to_posRulesJ hlps_perm
        (defeq_list_ok_spec hCore (hrc_adv.mono ext_h_idxl)
          (by rw [hκ_eq]; exact hctx_rep.mono ext_open_idxl) hsc_t
          hef_adv hlf_adv (hgood_adv.sub inv.sub_deidx) inv.ev_deidx hidxl_tm hidxr_tm)
    -- 8. Statement domain telescopes (`defeq_tele` #1 and #2 in `c_adv`)
    have ext_idxl_deidx := inv.ev_deidx.heap_extends
    have ext_h_deidx := ext_h_idxl.trans ext_idxl_deidx
    have htyr_ren_ex : TmExact c_adv.κ 0 zeroGhost inv.h_tyr_ren 0
        (posOf lps (tyA.renameConsts f_id)) inv.v_tyr_ren := by
      rw [hκ_eq]
      have hr := rename_exact (Γ₂ := zeroGhost) inv.ev_tyr_ren
        ((hty_rep 0 zeroGhost).mono ext_h_deidx) (hren.mono ext_h_deidx)
      have hnp_ty_pos : NoProjIn blockNames (posOf lps tyA) = true := by
        unfold posOf; rw [noProjIn_instantiateLevelParams]; exact hnp_ty
      rw [renameAll_eq_renameConsts_of_noProjIn hf_out hnp_ty_pos] at hr
      have hcomm : (posOf lps tyA).renameConsts f_id = posOf lps (tyA.renameConsts f_id) := by
        unfold posOf
        exact (Ix.Kernel.Expr.renameConsts_instantiateLevelParams f_id lps (posLevels lps) tyA).symm
      rwa [hcomm] at hr
    have ext_tyr_nil := Heap.Extends.snoc inv.h_tyr_ren (.construct kexprListEnum "Nil" [])
    have ext_tci_dt1_in := ext_open_in.trans (inv.ev_open.heap_extends.trans
      (ext_open_idxl.trans (ext_idxl_deidx.trans (inv.ev_tyr_ren.heap_extends.trans ext_tyr_nil))))
    have ext_h_dt1_in := ext_tci.trans ext_tci_dt1_in
    obtain ⟨fvs1_pos, remA1_pos, rdoms_pos, lrest_pos, hop_dt1_pos, hinst_r_pos, hraw_pre⟩ :=
      defeq_tele_spec hCore hef_adv.storeClosed rP (d := 0) (depth := depth)
        hrp_val (by omega)
        (hrc_adv.mono ext_h_dt1_in)
        (typesRep_alloc_nil c_adv.κ zeroGhost inv.h_tyr_ren)
        (ghostScoped_zero zeroGhost) hef_adv hlf_adv (hgood_adv.sub inv.sub_dt1) inv.ev_dt1
        (by rw [hκ_eq]; exact (htty_rep 0 zeroGhost).mono ext_tci_dt1_in)
        (htyr_ren_ex.toTm.mono ext_tyr_nil)
    obtain ⟨fvs1, remA1, hop_dt1, hfvs1_pos, hremA1_pos⟩ := openPisAtFvars_of_posOf hop_dt1_pos
    subst hfvs1_pos hremA1_pos
    have hfvs_split := openPisAtFvars_split rP cnF cvt_lps 0
    rw [show rP + cnF = depth from rfl, hopen_t, hop_dt1, Nat.zero_add, Option.map_eq_some_iff]
      at hfvs_split
    obtain ⟨⟨fvs2, tbody'⟩, hop_dt2_expected, hfvs_pair⟩ := hfvs_split
    injection hfvs_pair with hfvs_app htbody_eq; subst htbody_eq
    have hfvs1_len : fvs1.length = rP := (openPisAtFvars_spec rP cvt_lps 0 hop_dt1).1
    have hfvs_take_eq : fvs.take rP = fvs1 := by
      rw [← hfvs_app, List.take_left' hfvs1_len]
    have hfvs_drop_eq : fvs.drop rP = fvs2 := by
      rw [← hfvs_app, List.drop_left' hfvs1_len]
    rw [← hfvs_take_eq] at hinst_r_pos hraw_pre
    obtain ⟨rdoms, lrest, hinst_r, hrdoms_pos, _⟩ := instPisAt_of_posOf hinst_r_pos
    subst hrdoms_pos
    have hde_pre : DefEqListJ posRulesJ c_adv.env depth
        ((fvs.take rP).map Expr.fvarTypeD) rdoms := by
      have hmap_ty : ((fvs.take rP).map (posOf lps)).map Expr.fvarTypeD =
          ((fvs.take rP).map Expr.fvarTypeD).map (posOf lps) := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro x hx
        have hx_mem : x ∈ fvs := List.mem_of_mem_take hx
        obtain ⟨idx, hidx_lt, rfl⟩ := List.getElem_of_mem hx_mem
        conv_lhs => rw [Function.comp_apply, hfvs_shape idx hidx_lt]
        conv_rhs => rw [Function.comp_apply, hfvs_shape idx hidx_lt]
        rfl
      rw [hmap_ty] at hraw_pre
      exact rawDefEqList_to_posRulesJ hlps_perm hraw_pre
    -- `defeq_tele` #2
    have ext_tci_dt1 := ext_tci_dt1_in.trans inv.ev_dt1.heap_extends
    have htake_fvs_len : ZMod.val (rP : F) = ((fvs.take rP).map (posOf lps)).length := by
      rw [hrp_val, List.length_map, List.length_take, hfvs_len]; omega
    have htake_fvs_Γ : ∀ m (hm : m < ((fvs.take rP).map (posOf lps)).length),
        Expr.fvar (0 + m) (Γ_t (0 + m)) = ((fvs.take rP).map (posOf lps))[m] := by
      intro m hm
      have hm_rP : m < rP := by rw [← hrp_val, htake_fvs_len] at hm; exact hm
      have h1 := congrArg (·[m]?) hbvd1_fvs
      rw [List.getElem?_map, List.getElem?_range hm_rP, Option.map_some,
        List.getElem?_eq_getElem hm] at h1
      exact Option.some.inj h1
    obtain ⟨_, remA1_inst, hinst_tty_rp, htty_rp_ex, h_tty_rp_eq⟩ :=
      peel_n_foralls_inst_exact htake_fvs_len htake_fvs_Γ inv.ev_tty_rp
        ((htty_rep 0 zeroGhost).mono ext_tci_dt1)
    subst h_tty_rp_eq; rw [ ← htake_fvs_len, hrp_val, Nat.zero_add] at htty_rp_ex
    have hremA1_eq : remA1_inst = posOf lps remA1 := by
      rw [hfvs_take_eq] at hinst_tty_rp
      have hop_spec := (openPisAtFvars_spec rP (posOf lps cvt_lps) 0 hop_dt1_pos).2.1
      rw [hop_spec] at hinst_tty_rp
      injection hinst_tty_rp with hp; exact hp.2.symm
    subst hremA1_eq
    have ext_open_dt1 := ext_open_idxl.trans (ext_idxl_deidx.trans
      (inv.ev_tyr_ren.heap_extends.trans (ext_tyr_nil.trans inv.ev_dt1.heap_extends)))
    obtain ⟨_, hctx_rp_rep, h_ctx_rp_eq⟩ :=
      typesRep_drop cnF hcnf_val inv.ev_ctx_rp (hctx_rep.mono ext_open_dt1)
    subst h_ctx_rp_eq
    rw [show depth - ZMod.val (cnF : F) = rP by rw [hcnf_val]; omega] at hctx_rp_rep
    have hsc_t_rp : GhostScoped Γ_t rP := fun i hi => hsc_t i (by omega)
    have ext_crest_dt1 := ext_crest_in.trans (inv.ev_cres.heap_extends.trans
      (inv.ev_csp.heap_extends.trans (inv.ev_idxl.heap_extends.trans
        (ext_idxl_deidx.trans (inv.ev_tyr_ren.heap_extends.trans
          (ext_tyr_nil.trans inv.ev_dt1.heap_extends))))))
    have ext_h_dt1 := ext_tci.trans ext_tci_dt1
    obtain ⟨fvs2_pos, _, doms2_pos, _, hop_dt2_pos, hinst_dt2_pos, hraw_dom⟩ :=
      defeq_tele_spec hCore hef_adv.storeClosed cnF (d := rP) (depth := depth)
        hcnf_val (by omega)
        (hrc_adv.mono ext_h_dt1) (by rw [hκ_eq]; exact hctx_rp_rep) hsc_t_rp
        hef_adv hlf_adv (hgood_adv.sub inv.sub_dt2) inv.ev_dt2
        (by rw [hκ_eq]; exact htty_rp_ex)
        (by rw [hκ_eq]; exact hcrest_tm.mono ext_crest_dt1)
    obtain ⟨fvs2', _, hop_dt2', hfvs2_pos, _⟩ := openPisAtFvars_of_posOf hop_dt2_pos
    subst hfvs2_pos
    rw [hop_dt2_expected] at hop_dt2'; injection hop_dt2' with hp
    obtain ⟨hfvs2_eq, _⟩ := Prod.mk.inj hp; subst hfvs2_eq
    rw [← hfvs_drop_eq] at hinst_dt2_pos hraw_dom
    rw [hinst_c2_pos] at hinst_dt2_pos
    injection hinst_dt2_pos with hp; obtain ⟨hdoms2_eq, _⟩ := Prod.mk.inj hp; subst hdoms2_eq
    have hde_dom : DefEqListJ posRulesJ c_adv.env depth
        ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP) := by
      rw [hcdoms_drop]
      have hmap_ty : ((fvs.drop rP).map (posOf lps)).map Expr.fvarTypeD =
          ((fvs.drop rP).map Expr.fvarTypeD).map (posOf lps) := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro x hx
        have hx_mem : x ∈ fvs := List.mem_of_mem_drop hx
        obtain ⟨idx, hidx_lt, rfl⟩ := List.getElem_of_mem hx_mem
        conv_lhs => rw [Function.comp_apply, hfvs_shape idx hidx_lt]
        conv_rhs => rw [Function.comp_apply, hfvs_shape idx hidx_lt]
        rfl
      rw [hmap_ty] at hraw_dom
      exact rawDefEqList_to_posRulesJ hlps_perm hraw_dom
    -- 9. Public parameter typing & `defeq_lam_tele` (#1 and #2 in `c_pub`)
    have ext_h_dt2 := ext_h_dt1.trans inv.ev_dt2.heap_extends
    have ext_dt2_nil := Heap.Extends.snoc inv.h_dt2 (.construct kexprListEnum "Nil" [])
    obtain ⟨r_pbody, r_ctxp, Γ_p, fvsP_pos, crest2_pos, htup_ctxp, hopen_p_pos, _, hΓp_hi,
        _, hctxp_rep, hsc_p⟩ :=
      peel_collect_open_exact rP hrp_val inv.ev_ctxp
        ((hty_rep 0 zeroGhost).mono (ext_h_dt2.trans ext_dt2_nil))
        (typesRep_alloc_nil c_pub.κ zeroGhost inv.h_dt2)
        (ghostScoped_zero zeroGhost)
    injection htup_ctxp with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    rw [Nat.zero_add] at hΓp_hi hctxp_rep hsc_p
    obtain ⟨fvsP, crest2, hopen_p, hfvsP_pos, hcrest2_pos⟩ := openPisAtFvars_of_posOf hopen_p_pos
    subst hfvsP_pos hcrest2_pos
    obtain ⟨hfvsP_len, _, hfvsP_shape⟩ := openPisAtFvars_spec rP tyA 0 hopen_p
    have hfvsP_take : fvsP.take rP = fvsP := List.take_of_length_le (by omega)
    -- Apply `defeq_lam_tele` #1 FIRST so we have `Γ_l` ready for `inst_params_typed_spec`!
    have ext_h_ctxp := ext_h_dt2.trans (ext_dt2_nil.trans inv.ev_ctxp.heap_extends)
    have ext_h_crestp := ext_h_ctxp.trans inv.ev_crestp.heap_extends
    have ext_crestp_nil := Heap.Extends.snoc inv.h_crestp (.construct kexprListEnum "Nil" [])
    have ext_h_lt1_in := ext_h_crestp.trans ext_crestp_nil
    obtain ⟨r_rhs_rp, r_lctx, Γ_l, lfvs1_pos, remL1_pos, pdoms1_pos, tyRest_pos,
        htup_lt1, hop_lt1_pos, hinst_lt1_pos, _, hΓl_hi, hremL1_tm, hlctx_rep, hsc_l, hraw_lt1⟩ :=
      defeq_lam_tele_spec hCore hef_pub.storeClosed rP (d := 0) (depth := depth)
        hrp_val (by omega)
        (hrc.mono ext_h_lt1_in)
        (typesRep_alloc_nil c_pub.κ zeroGhost inv.h_crestp)
        (ghostScoped_zero zeroGhost) hef_pub hlf_pub (hgood_pub.sub inv.sub_lt1) inv.ev_lt1
        (hrhs_pos_tm0.toTm.mono ext_h_lt1_in)
        ((hty_rep 0 zeroGhost).toTm.mono ext_h_lt1_in)
    injection htup_lt1 with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    rw [Nat.zero_add] at hΓl_hi hremL1_tm hlctx_rep hsc_l
    obtain ⟨lfvs1, remL1, hop_lt1, hlfvs1_pos, hremL1_pos⟩ := openLamsAtFvars_of_posOf hop_lt1_pos
    subst hlfvs1_pos hremL1_pos
    obtain ⟨hlfvs1_len, _, hlfvs1_shape⟩ := openLamsAtFvars_spec rP r.rhs 0 hop_lt1
    obtain ⟨pdoms1, tyRest, hinst_lt1, hpdoms1_pos, _⟩ := instPisAt_of_posOf hinst_lt1_pos
    subst hpdoms1_pos
    -- Now apply `inst_params_typed_spec` with `Γ₁ := Γ_p` and `Γ₂ := Γ_l`!
    have hΓp_list : ((List.range rP).map fun m => Expr.fvar m (Γ_p m)) = fvsP.map (posOf lps) := by
      apply List.ext_getElem (by simp [hfvsP_len])
      intro m hm1 hm2
      simp only [List.length_range, List.length_map] at hm1
      have hm_pos : m < (fvsP.map (posOf lps)).length := by simp [hfvsP_len, hm1]
      have hΓm := hΓp_hi m hm_pos
      have hm_fvsP : m < fvsP.length := by rw [hfvsP_len]; exact hm1
      have hsh := hfvsP_shape m hm_fvsP
      rw [Nat.zero_add] at hsh
      simp only [List.getElem_map, List.getElem_range, hΓm]
      conv_rhs => rw [hsh]
      simp [posOf, Expr.instantiateLevelParams, Expr.fvarTypeD]
    have hΓl_list : ((List.range rP).map fun m => Expr.fvar m (Γ_l m)) = lfvs1.map (posOf lps) := by
      apply List.ext_getElem (by simp [hlfvs1_len])
      intro m hm1 hm2
      simp only [List.length_range, List.length_map] at hm1
      have hm_pos : m < (lfvs1.map (posOf lps)).length := by simp [hlfvs1_len, hm1]
      have hΓm := hΓl_hi m hm_pos
      have hm_lfvs1 : m < lfvs1.length := by rw [hlfvs1_len]; exact hm1
      have hsh := hlfvs1_shape m hm_lfvs1
      rw [Nat.zero_add] at hsh
      simp only [List.getElem_map, List.getElem_range, hΓm]
      conv_rhs => rw [hsh]
      simp [posOf, Expr.instantiateLevelParams, Expr.fvarTypeD]
    let pinsP_lps := pins_lps.map fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p
    let pinsL_lps := pins_lps.map fun p => Expr.instSpine lfvs1 (rP - 1) p
    have hpins_ctxp_1 : RepList kexprListEnum (fun h P p => Tm c_pub.κ rP Γ_p h 0 P p) inv.h_ctxp
        (pinsP_lps.map (posOf lps)) pins := by
      have h1 := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext_h_ctxp hpins_rep
      have hlist_eq :
          (pins_lps.map (posOf lps)).map
            (fun P => Expr.instSpine ((List.range rP).map fun m => .fvar m (Γ_p m)) (rP - 1) P) =
            pinsP_lps.map (posOf lps) := by
        rw [hΓp_list]
        dsimp only [pinsP_lps]
        rw [hfvsP_take, List.map_map, List.map_map]
        apply List.map_congr_left
        intro p _; simp only [Function.comp_apply]
        unfold posOf
        exact (Ix.Kernel.Expr.instSpine_instantiateLevelParams lps (posLevels lps)
          fvsP (rP - 1) p).symm
      rw [← hlist_eq]; clear hlist_eq
      induction h1 with
      | nil cell => exact .nil cell
      | cons cell hh _ ih => exact .cons cell (hh.open_prefix_eq Γ_p).toTm ih
    have hpins_ctxp_2 : RepList kexprListEnum (fun h P p => Tm c_pub.κ rP Γ_l h 0 P p) inv.h_ctxp
        (pinsL_lps.map (posOf lps)) pins := by
      have h1 := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext_h_ctxp hpins_rep
      have hlist_eq :
          (pins_lps.map (posOf lps)).map
            (fun P => Expr.instSpine ((List.range rP).map fun m => .fvar m (Γ_l m)) (rP - 1) P) =
            pinsL_lps.map (posOf lps) := by
        rw [hΓl_list]
        dsimp only [pinsL_lps]
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro p _; simp only [Function.comp_apply]
        unfold posOf
        exact (Ix.Kernel.Expr.instSpine_instantiateLevelParams lps (posLevels lps)
          lfvs1 (rP - 1) p).symm
      rw [← hlist_eq]; clear hlist_eq
      induction h1 with
      | nil cell => exact .nil cell
      | cons cell hh _ ih => exact .cons cell (hh.open_prefix_eq Γ_l).toTm ih
    have ext_ctyl_ctxp := ext_ctyl_csp0.trans (inv.ev_cty_ren.heap_extends.trans
      (inv.ev_crest.heap_extends.trans (ext_crest_dt1.trans
        (inv.ev_dt2.heap_extends.trans (ext_dt2_nil.trans inv.ev_ctxp.heap_extends)))))
    obtain ⟨cdomsP_pos, crestP_pos, cdomsL_pos, crestL_pos,
        hinst_p_pos, hinst_l_pos, _, hcrestL_tm, hraw_pins_typed⟩ :=
      inst_params_typed_spec hCore hef_pub.storeClosed (d₁ := rP) (d₂ := rP) (depth := depth)
        (by omega) (hrc.mono ext_h_ctxp) hctxp_rep hsc_p hef_pub hlf_pub
        (hgood_pub.sub inv.sub_crestp) inv.ev_crestp
        ((hctyl_tm0.mono ext_ctyl_ctxp).of_depth_zero rP)
        ((hctyl_tm0.mono ext_ctyl_ctxp).of_depth_zero rP)
        hpins_ctxp_1 hpins_ctxp_2
    obtain ⟨cdomsP, crestP, hinst_p, hcdomsP_pos, _⟩ := instPisAt_of_posOf hinst_p_pos
    subst hcdomsP_pos
    obtain ⟨cdomsL, crestL, hinst_l, _, hcrestL_pos⟩ := instPisAt_of_posOf hinst_l_pos
    subst hcrestL_pos
    have hpins_typed : TypedListJ posRulesJ c_pub.env depth pinsP_lps cdomsP :=
      rawTypedList_to_posRulesJ hlps_perm hraw_pins_typed
    -- Construct `xFvsP, ldoms` (`openPisAtFvars cnF crestP rP`) and `ldoms.getAppArgs.length = cnP + nI`
    have hpP_len : pinsP_lps.length + cnF = cnP + cnF := by simp [pinsP_lps, hpins_len]
    rw [← hpP_len] at hstrip_inst
    obtain ⟨_, crestP', bs_cp, cbody_cp, hinst_p', hstrip_cp, hfn_cp, hlen_cp⟩ :=
      instPisAt_constHead _ _ (cnP + nI) pinsP_lps cnF cty_inst
        hstrip_inst hfn_inst hcbody_inst_len
    rw [hinst_p] at hinst_p'; injection hinst_p' with hp; injection hp with _ hcp; subst hcp
    obtain ⟨xFvsP, ldoms, hopen_cf, _, hldoms_len⟩ :=
      openPisAtFvars_constHead _ _ (cnP + nI) cnF crestP rP hstrip_cp hfn_cp hlen_cp
    -- `defeq_lam_tele` #2 (`ev_lt2`)
    have ext_crestp_lt1 := ext_crestp_nil.trans inv.ev_lt1.heap_extends
    have ext_h_lt1 := ext_h_lt1_in.trans inv.ev_lt1.heap_extends
    obtain ⟨_, _, _, lfvs2_pos, remL2_pos, pdoms2_pos, crestEnd_pos,
        _, hop_lt2_pos, hinst_lt2_pos, _, _, _, _, _, hraw_lt2⟩ :=
      defeq_lam_tele_spec hCore hef_pub.storeClosed cnF (d := rP) (depth := depth)
        hcnf_val (by omega)
        (hrc.mono ext_h_lt1) hlctx_rep hsc_l hef_pub hlf_pub (hgood_pub.sub inv.sub_lt2) inv.ev_lt2
        hremL1_tm (hcrestL_tm.mono ext_crestp_lt1)
    obtain ⟨lfvs2, remL2, hop_lt2, hlfvs2_pos, _⟩ := openLamsAtFvars_of_posOf hop_lt2_pos
    subst hlfvs2_pos
    obtain ⟨_, _, hlfvs2_shape⟩ := openLamsAtFvars_spec cnF remL1 rP hop_lt2
    obtain ⟨pdoms2, crestEnd, hinst_lt2, hpdoms2_pos, _⟩ := instPisAt_of_posOf hinst_lt2_pos
    subst hpdoms2_pos
    have hlam_walk : LamTeleWalkJ posRulesJ c_pub.env rP cnF tyA cty_inst
        (fun pre => pins_lps.map fun p => Expr.instSpine pre (rP - 1) p) r.rhs := by
      let lfvs := lfvs1 ++ lfvs2
      have hop_lams_all : openLamsAtFvars depth r.rhs 0 = some (lfvs, remL2) := by
        show openLamsAtFvars (rP + cnF) r.rhs 0 = some (lfvs1 ++ lfvs2, remL2)
        rw [openLamsAtFvars_split rP cnF r.rhs 0, hop_lt1, Nat.zero_add, hop_lt2]; rfl
      have hlfvs_take : lfvs.take rP = lfvs1 := List.take_left' hlfvs1_len
      have hlfvs_drop : lfvs.drop rP = lfvs2 := List.drop_left' hlfvs1_len
      have hmap1 : (lfvs1.map (posOf lps)).map Expr.fvarTypeD =
          (lfvs1.map Expr.fvarTypeD).map (posOf lps) := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro x hx
        obtain ⟨idx, hidx_lt, rfl⟩ := List.getElem_of_mem hx
        conv_lhs => rw [Function.comp_apply, hlfvs1_shape idx hidx_lt]
        conv_rhs => rw [Function.comp_apply, hlfvs1_shape idx hidx_lt]
        rfl
      have hmap2 : (lfvs2.map (posOf lps)).map Expr.fvarTypeD =
          (lfvs2.map Expr.fvarTypeD).map (posOf lps) := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro x hx
        obtain ⟨idx, hidx_lt, rfl⟩ := List.getElem_of_mem hx
        conv_lhs => rw [Function.comp_apply, hlfvs2_shape idx hidx_lt]
        conv_rhs => rw [Function.comp_apply, hlfvs2_shape idx hidx_lt]
        rfl
      rw [hmap1] at hraw_lt1
      rw [hmap2] at hraw_lt2
      have hraw_both := rawDefEqList_append hraw_lt1 hraw_lt2
      rw [← List.map_append, ← List.map_append, ← List.map_append] at hraw_both
      exact ⟨lfvs, remL2, pdoms1, tyRest, cdomsL, crestL, pdoms2, crestEnd,
        hop_lams_all, by rwa [hlfvs_take], by rwa [hlfvs_take], by rwa [hlfvs_drop],
        rawDefEqList_to_posRulesJ hlps_perm hraw_both⟩
    -- 10. Right-hand side application (`rhs_s ≡ mkAppN (r.rhs.renameConsts f_id) fvs` in `c_adv`)
    have ext_h_lt2 := ext_h_lt1.trans inv.ev_lt2.heap_extends
    have hrhs_ren_ex : TmExact c_adv.κ 0 zeroGhost inv.h_rhs_ren 0
        (posOf lps (r.rhs.renameConsts f_id)) inv.v_rhs_ren := by
      rw [hκ_eq]
      have hr := rename_exact (Γ₂ := zeroGhost) inv.ev_rhs_ren
        (hrhs_pos_tm0.mono ext_h_lt2) (hren.mono ext_h_lt2)
      have hnp_rhs_pos : NoProjIn blockNames (posOf lps r.rhs) = true := by
        unfold posOf; rw [noProjIn_instantiateLevelParams]; exact hrhs_noproj
      rw [renameAll_eq_renameConsts_of_noProjIn hf_out hnp_rhs_pos] at hr
      have hcomm : (posOf lps r.rhs).renameConsts f_id = posOf lps (r.rhs.renameConsts f_id) := by
        unfold posOf
        exact (Ix.Kernel.Expr.renameConsts_instantiateLevelParams f_id lps (posLevels lps) r.rhs).symm
      rwa [hcomm] at hr
    have ev_bvd3' := inv.ev_bvd3
    rw [hd_eq] at ev_bvd3'
    have hbvd3_rep := bvars_desc_exact_wide (κ := c_adv.κ) (d := depth) (Γ := Γ_t)
      (by rw [hd_val]) (by rw [hd_val]) (by omega) ev_bvd3'
    rw [hd_val, Nat.sub_self] at hbvd3_rep
    have hbvd3_fvs :
        ((List.range depth).map fun m => Expr.fvar (0 + m) (Γ_t (0 + m))) = fvs_pos := by
      apply List.ext_getElem (by simp [hfvs_pos_len])
      intro m hm1 hm2
      simp only [List.length_map, List.length_range] at hm1
      have hΓm := hΓt_hi m hm2
      simp only [List.getElem_map, List.getElem_range, Nat.zero_add, hΓm]
      rw [hfvs_pos]; simp only [List.getElem_map]
      have hm_fvs : m < fvs.length := by rw [hfvs_len]; exact hm1
      conv_rhs => rw [hfvs_shape m hm_fvs]
      simp [Nat.zero_add, posOf, Expr.instantiateLevelParams, Expr.fvarTypeD]
    rw [hbvd3_fvs, hfvs_pos] at hbvd3_rep
    have hrhs_app_ex := apply_spine_exact inv.ev_rhsapp
      ((hrhs_ren_ex.of_depth_zero depth).mono inv.ev_bvd3.heap_extends) hbvd3_rep
    have hrhs_app_pos_eq :
        Expr.mkAppN (posOf lps (r.rhs.renameConsts f_id)) (fvs.map (posOf lps)) =
          posOf lps (Expr.mkAppN (r.rhs.renameConsts f_id) fvs) := by
      unfold posOf
      exact (mkAppN_instantiateLevelParams lps (posLevels lps) fvs (r.rhs.renameConsts f_id)).symm
    rw [hrhs_app_pos_eq] at hrhs_app_ex
    have ext_dt1_rhsapp := inv.ev_dt2.heap_extends.trans (ext_dt2_nil.trans
      (inv.ev_ctxp.heap_extends.trans (inv.ev_crestp.heap_extends.trans
        (ext_crestp_lt1.trans (inv.ev_lt2.heap_extends.trans
          (inv.ev_rhs_ren.heap_extends.trans
            (inv.ev_bvd3.heap_extends.trans inv.ev_rhsapp.heap_extends)))))))
    have ext_open_rhsapp := ext_open_dt1.trans ext_dt1_rhsapp
    have ext_eqa_rhsapp := inv.ev_lsp.heap_extends.trans (ext_lsp_lheq.trans
      (ext_lheq_pref.trans (ext_pref_csp.trans (inv.ev_idxl.heap_extends.trans
        (ext_idxl_deidx.trans (inv.ev_tyr_ren.heap_extends.trans
          (ext_tyr_nil.trans (inv.ev_dt1.heap_extends.trans ext_dt1_rhsapp))))))))
    have ext_h_rhsapp := ext_open.trans ext_open_rhsapp
    have hde_rhs : posRulesJ.defeq c_adv.env depth rhsS
        (Expr.mkAppN (r.rhs.renameConsts f_id) fvs) :=
      posRulesJ_defeq_of_pos hlps_perm
        (core_defeq hCore (hrc_adv.mono ext_h_rhsapp)
          (by rw [hκ_eq]; exact hctx_rep.mono ext_open_rhsapp) hsc_t
          hef_adv hlf_adv (hgood_adv.sub inv.sub_derhs) inv.ev_derhs
          (by rw [hκ_eq]; exact hrhsS_ex.toTm.mono ext_eqa_rhsapp)
          hrhs_app_ex.toTm)
    -- 11. `lhsS : alphaS`, `rhsS : alphaS`, and `alphaS : .sort ell_lps` (`c_adv`)
    have e_derhs := inv.ev_derhs.heap_extends
    have ext_h_derhs := ext_h_rhsapp.trans e_derhs
    have ext_open_derhs := ext_open_rhsapp.trans e_derhs
    have ext_eqa_derhs := ext_eqa_rhsapp.trans e_derhs
    obtain ⟨tl_pos, htl_tm, htl_inf⟩ :=
      core_infer hCore (hrc_adv.mono ext_h_derhs)
        (by rw [hκ_eq]; exact hctx_rep.mono ext_open_derhs) hsc_t
        hef_adv hlf_adv (hgood_adv.sub inv.sub_tl) inv.ev_tl
        (by rw [hκ_eq]; exact hlhs_ex.toTm.mono ext_eqa_derhs)
    have e_tl := inv.ev_tl.heap_extends
    have htl_de :=
      core_defeq hCore (hrc_adv.mono (ext_h_derhs.trans e_tl))
        (by rw [hκ_eq]; exact hctx_rep.mono (ext_open_derhs.trans e_tl)) hsc_t
        hef_adv hlf_adv (hgood_adv.sub inv.sub_detl) inv.ev_detl
        htl_tm (by rw [hκ_eq]; exact halpha_ex.toTm.mono (ext_eqa_derhs.trans e_tl))
    have e_detl := e_tl.trans inv.ev_detl.heap_extends
    obtain ⟨tr_pos, htr_tm, htr_inf⟩ :=
      core_infer hCore (hrc_adv.mono (ext_h_derhs.trans e_detl))
        (by rw [hκ_eq]; exact hctx_rep.mono (ext_open_derhs.trans e_detl)) hsc_t
        hef_adv hlf_adv (hgood_adv.sub inv.sub_tr) inv.ev_tr
        (by rw [hκ_eq]; exact hrhsS_ex.toTm.mono (ext_eqa_derhs.trans e_detl))
    have e_tr := e_detl.trans inv.ev_tr.heap_extends
    have htr_de :=
      core_defeq hCore (hrc_adv.mono (ext_h_derhs.trans e_tr))
        (by rw [hκ_eq]; exact hctx_rep.mono (ext_open_derhs.trans e_tr)) hsc_t
        hef_adv hlf_adv (hgood_adv.sub inv.sub_detr) inv.ev_detr
        htr_tm (by rw [hκ_eq]; exact halpha_ex.toTm.mono (ext_eqa_derhs.trans e_tr))
    have e_detr := e_tr.trans inv.ev_detr.heap_extends
    obtain ⟨ta_pos, hta_tm, hta_inf⟩ :=
      core_infer hCore (hrc_adv.mono (ext_h_derhs.trans e_detr))
        (by rw [hκ_eq]; exact hctx_rep.mono (ext_open_derhs.trans e_detr)) hsc_t
        hef_adv hlf_adv (hgood_adv.sub inv.sub_ta) inv.ev_ta
        (by rw [hκ_eq]; exact halpha_ex.toTm.mono (ext_eqa_derhs.trans e_detr))
    have e_ta := e_detr.trans inv.ev_ta.heap_extends
    have ext_srt := Heap.Extends.snoc inv.h_ta (.construct kexprEnum "Srt" [inv.ell])
    have hsrt_tm : Tm c_adv.κ depth Γ_t
        (inv.h_ta ++ [.construct kexprEnum "Srt" [inv.ell]]) 0
        (posOf lps (.sort ell_lps)) (.ptr (.enum kexprEnum) inv.h_ta.length) := by
      unfold posOf; simp only [Expr.instantiateLevelParams]
      rw [hell_subst]
      exact .sort (by simp) (rell_pos.mono (ext_eqa_derhs.trans (e_ta.trans ext_srt)))
        (LvEq.refl ell_pos)
    have hta_de :=
      core_defeq hCore (hrc_adv.mono (ext_h_derhs.trans (e_ta.trans ext_srt)))
        (by rw [hκ_eq]; exact hctx_rep.mono (ext_open_derhs.trans (e_ta.trans ext_srt))) hsc_t
        hef_adv hlf_adv (hgood_adv.sub inv.sub_deta) inv.ev_deta
        (hta_tm.mono ext_srt) hsrt_tm
    exact ⟨
      { a_t, hadv_t, cvt, vt, hfind_t := hfind_t0, ht_lps
        cvj, cnP, cnF, hfind_ctor, hlvls_len, hpins_len, hnfields
        hrhs_bvars, hrhs_nofvar, hrhs_lvls, hrhs_lams, hrhs_noproj, hrhs_cr, hrhs_typed
        hctor_tele, hctor_head
        ell_lps, fvs, tbody, hopen_t, heq_head, htargs_len
        hlhs_fn, hlargs_len, hlargs_pre, hmajor_eq
        cdoms, cres, hinst_c, hcres_len
        rdoms, lrest, hinst_r
        fvsP, crest2, hopen_p
        cdomsP, crestP, hinst_p
        xFvsP, ldoms, hopen_cf, hldoms_len
        hlam_walk, hpins_typed
        hruns := ⟨hde_idx, hde_dom, hde_pre, hde_rhs,
          ⟨invPosOf lps tl_pos, posRulesJ_infer_of_pos hlps_perm htl_inf,
            posRulesJ_defeq_of_pos hlps_perm (by rwa [posOf_invPosOf hlps_perm])⟩,
          ⟨invPosOf lps tr_pos, posRulesJ_infer_of_pos hlps_perm htr_inf,
            posRulesJ_defeq_of_pos hlps_perm (by rwa [posOf_invPosOf hlps_perm])⟩⟩
        halpha_sort := ⟨invPosOf lps ta_pos, posRulesJ_infer_of_pos hlps_perm hta_inf,
          posRulesJ_defeq_of_pos hlps_perm (by rwa [posOf_invPosOf hlps_perm])⟩ }⟩

/-- **Refinement of `KernelModeled::check_rules_go`** over a `RulesRepExact` list and `L1.Stream`. -/
theorem check_rules_go_vm_spec
    (hCore : IxVM.Consistency.Core S₀) (hroles : RolesSpec) (hcallees : CalleesSpec)
    {c_pub c_adv : Ctx}
    (ht_eq : c_adv.t = c_pub.t) (hlim_eq : c_adv.lim = c_pub.lim)
    (hef_pub : EnvFacts c_pub) (hlf_pub : LoadFacts c_pub) (hexact_pub : ExactGetCI c_pub)
    (hef_adv : EnvFacts c_adv) (hlf_adv : LoadFacts c_adv) (hexact_adv : ExactGetCI c_adv)
    {blockNames : List KKey} {f_id : KKey → KKey} {advSet : Bytes.Address → Prop}
    (hf_out : ∀ k, blockNames.contains k = false → f_id k = k)
    (hproj_pub : ∀ sn i entry, c_pub.env.findProj? sn i = some entry →
      blockNames.contains sn = false)
    {cvName : KKey} {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat}
    {lvls_lps : List KLevel} {pins_lps : List KExpr}
    (hlps_lt : lps.length < 4294967296)
    (hlps_perm : lps.Perm (List.range lps.length))
    (hrp_le : rP ≤ mI) (hmi_lt : mI < 288230376151711744)
    (hnp_ty : NoProjIn blockNames tyA = true)
    (hnp_pins : ∀ p ∈ pins_lps, NoProjIn blockNames p = true)
    (hnp_ctor : ∀ k cvj cnP cnF, c_pub.env.find? k = some (.ctorInfo cvj cnP cnF) →
      NoProjIn blockNames cvj.type = true)
    {b_ind : Bytes.Address} {i_ind inp : F} {a_rm : Bytes.Address} :
    ∀ (rls : List (RecRule .anon)) (j : Nat)
      {rc rm ty_r rules_ptr iblock ilvls pins src dst aset s_in s_out : SourceValue F}
      {bytes_in : List UInt8} {h h' : Heap F} {calls : List (Call F)},
      j + rls.length < 4611686018427387904 →
      (∀ k rl, rls[k]? = some rl →
        rl.ctor = c_pub.κ (cprjAddr (ixAddr b_ind) (ZMod.val i_ind) (j + k))) →
      (∀ k rl, rls[k]? = some rl → ∀ cvj cnP cnF,
        c_pub.env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
        lvls_lps.length = cvj.levelParams.length) →
      Good c_pub calls → Good c_adv calls →
      RCRep c_pub.t c_pub.lim h rc →
      Bytes.RepAddressRef addrTy h a_rm rm →
      c_pub.κ (ixAddr a_rm) = f_id cvName →
      Bytes.RepAddressRef addrTy h b_ind iblock →
      AddrMapAll addrMapEnum (fun _ k _ => advSet k) h aset →
      RenameMap c_pub.κ c_pub.κ f_id h src dst →
      TmCExact c_pub.κ h (posOf lps tyA) ty_r →
      RepKLevelList h (lvls_lps.map (Level.subst lps (posLevels lps))) ilvls →
      RepList kexprListEnum
        (fun h P p => TmExact c_pub.κ 0 zeroGhost h rP P p) h (pins_lps.map (posOf lps)) pins →
      RulesRepExact c_pub.κ h lps j rules_ptr rls →
      L1.Stream h bytes_in s_in →
      ObsFn W "KernelModeled::check_rules_go"
        [rc, rm, .field (lps.length : F), ty_r, .field (rP : F), .field ((mI - rP) : F),
         rules_ptr, iblock, .field i_ind, .field inp, ilvls, pins, src, dst, aset, s_in, .field (j : F)]
        h s_out h' calls →
      ∃ bytes_out, L1.Stream h' bytes_out s_out ∧
        RawIotaRulesVmRun c_pub c_adv blockNames f_id advSet cvName lps tyA mI rP
          lvls_lps pins_lps j rls := by
  intro rls
  induction rls with
  | nil =>
    intro j rc rm ty_r rules_ptr iblock ilvls pins src dst aset s_in s_out bytes_in h h' calls
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrls hstr ev
    match Obs.«KernelModeled::check_rules_go».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. =>
      subst hr hh; exact ⟨bytes_in, hstr, trivial⟩
    | .Cons (ld12 := ld) .. =>
      cases hrls with
      | nil cell => exact absurd ld (by simp [loadValue_enum_cell cell])
  | cons rl rls ih =>
    intro j rc rm ty_r rules_ptr iblock ilvls pins src dst aset s_in s_out bytes_in h h' calls
      hj_lt hctor_eq hlvls_ctor hg_pub hg_adv hrc hrm hrm_key hiblock haset hren
      hty_rep hilvls_rep hpins_rep hrls hstr ev
    have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
    have hval1 : ZMod.val (1 : F) = 1 := rfl
    match Obs.«KernelModeled::check_rules_go».obs ev with
    | .Nil (ld12 := ld) .. =>
      cases hrls with
      | cons cell _ _ => exact absurd ld (by simp [loadValue_enum_cell cell])
    | .Cons (x_rest := x_rest) (m42 := m42) (x_t := x_t) (x_s2 := x_s2) (m77 := m77)
        (x_rnf := x_rnf) (x_rhs := x_rhs) (v116 := v_cprj) (m117 := m117) (cs127 := cs127)
        (m155 := m155) (p163 := p163) (cs169 := cs169) (x_cty := x_cty)
        (x_cnp := x_cnp) (x_cnf := x_cnf) (cs290 := cs290) (cs432 := cs432) (v451 := v451)
        (ld12 := ld) (ev54 := ev_ga) (ev129 := ev_cprj) (ev171 := ev_ci) (ld165 := ld_ci)
        (heq258 := heq_cnp) (heq286 := heq_rnf) (ev292 := ev_iota) (op577 := op_j1)
        (ev434 := ev_rec) (hc579 := hc) .. =>
      subst hc
      cases hrls with
      | cons cell hrl_rep hrls_rest =>
        obtain ⟨_, heq_cons⟩ := load_cell cell ld
        injection heq_cons with hmk hrest_eq; subst hrest_eq
        obtain ⟨rhs_ptr, hmk_eq, hnf_lt, hrhs_rep⟩ := hrl_rep
        rw [hmk_eq] at hmk
        injection hmk with _ hmk_args
        injection hmk_args with _ hmk_args2
        injection hmk_args2 with hrnf_eq hmk_args3
        injection hmk_args3 with hrhs_eq _
        subst hrhs_eq
        -- `get_address`
        obtain ⟨a_t, bytes_mid, x_t', x_s2', _, htup_ga, ha_t, hstr_mid, ext_ga, _⟩ :=
          get_address_spec hstr ev_ga
        injection htup_ga with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
        -- `projection_addr_ctor`
        have hcprj_spec := hcallees c_pub .projection_addr_ctor _ _ _ _ _ ev_cprj
        obtain ⟨a_cprj, ha_cprj, haddr_cprj⟩ :=
          hcprj_spec i_ind (j : F) iblock b_ind rfl
            (hg_pub.sub fun _ hx => by simp [hx])
            (Bytes.repAddressRef_heapMono₂ addrTy ext_ga hiblock)
        have hj_val : ZMod.val (j : F) = j := SubstAux.val_natCast (by simp at hj_lt; omega)
        rw [hj_val] at haddr_cprj
        have hcprj_key : c_pub.κ (ixAddr a_cprj) = rl.ctor := by
          rw [haddr_cprj, hctor_eq 0 rl rfl, Nat.add_zero]
        -- `Ingress::get_ci(cprj)`
        obtain ⟨ci_c, hfind_c0, _, _, v_ci, ld_ci', hcir_c⟩ :=
          hexact_pub a_cprj v_cprj p163 m117 m155 cs169 ev_ci
            (hg_pub.sub fun _ hx => by simp [hx]) ha_cprj
            (not_rec_or_quot_of_load ld_ci (by decide) (by decide))
        rw [ld_ci] at ld_ci'; injection ld_ci' with hv_ci; subst hv_ci
        rw [hcprj_key] at hfind_c0
        cases hcir_c with
        | @ctor _ _ _ _ _ _ _ _ cvj cnP cnF hv_c hcnp_f hcnf_f ⟨hcnp_lt, hcnf_lt⟩ _ =>
          subst hcnp_f hcnf_f
          have hnfields : rl.nfields = cnF := by
            have hrnf_cnf := hrnf_eq.symm.trans heq_rnf
            injection hrnf_cnf with hf
            have hv := congrArg ZMod.val hf
            rwa [SubstAux.val_natCast (by omega), SubstAux.val_natCast (by omega)] at hv
          have ext_h_m155 := ext_ga.trans (ev_cprj.heap_extends.trans ev_ci.heap_extends)
          have hrule_out :=
            check_iota_rule_vm_spec (j := j) hCore hroles ht_eq hlim_eq
              hef_pub hlf_pub hef_adv hlf_adv hexact_adv hf_out hproj_pub
              (hg_pub.sub fun _ hx => by simp [hx])
              (hg_adv.sub fun _ hx => by simp [hx])
              hlps_lt hlps_perm hrp_le hmi_lt hcnp_lt hcnf_lt
              hfind_c0 (hlvls_ctor 0 rl rfl cvj cnP cnF hfind_c0) hnfields
              hnp_ty (hnp_ctor rl.ctor cvj cnP cnF hfind_c0) hnp_pins
              (hrc.mono ext_h_m155)
              (Bytes.repAddressRef_heapMono₂ addrTy ext_h_m155 hrm) hrm_key
              (Bytes.repAddressRef_heapMono₂ addrTy ev_ci.heap_extends ha_cprj) hcprj_key
              (Bytes.repAddressRef_heapMono₂ addrTy (ev_cprj.heap_extends.trans ev_ci.heap_extends) ha_t)
              (haset.mono ext_h_m155) (hren.mono ext_h_m155)
              (hty_rep.mono ext_h_m155) (hrhs_rep.mono ext_h_m155) hv_c.2.2.2
              (hilvls_rep.mono ext_h_m155)
              (RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext_h_m155 hpins_rep)
              ev_iota
          have hj1_eq : v451 = .field ((j + 1 : Nat) : F) := by
            rw [SubstAux.add_ok op_j1]; congr 1
            exact ZMod.val_injective _ (by
              rw [SubstAux.val_add (by simp at hj_lt; omega), hj_val, hval1,
                SubstAux.val_natCast (by simp at hj_lt; omega)])
          rw [hj1_eq] at ev_rec
          have ext_m42_m77 := ev_cprj.heap_extends.trans
            (ev_ci.heap_extends.trans ev_iota.heap_extends)
          have ext_h_m77 := ext_ga.trans ext_m42_m77
          obtain ⟨bytes_out, hstr_out, hrest_out⟩ :=
            ih (j + 1) (by simp at hj_lt; omega)
              (fun k rl' hk => by
                have h1 := hctor_eq (k + 1) rl' (by simpa using hk)
                simpa [Nat.add_assoc, Nat.add_comm 1 k] using h1)
              (fun k rl' hk => hlvls_ctor (k + 1) rl' (by simpa using hk))
              (hg_pub.sub fun _ hx => by simp [hx])
              (hg_adv.sub fun _ hx => by simp [hx])
              (hrc.mono ext_h_m77)
              (Bytes.repAddressRef_heapMono₂ addrTy ext_h_m77 hrm) hrm_key
              (Bytes.repAddressRef_heapMono₂ addrTy ext_h_m77 hiblock)
              (haset.mono ext_h_m77) (hren.mono ext_h_m77)
              (hty_rep.mono ext_h_m77) (hilvls_rep.mono ext_h_m77)
              (RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext_h_m77 hpins_rep)
              (hrls_rest.mono ext_h_m77) (hstr_mid.mono ext_m42_m77) ev_rec
          exact ⟨bytes_out, hstr_out, hrule_out, hrest_out⟩

/-- **Top-level refinement of `KernelModeled::check_rules`**: decomposes the recursor's major
premise domain (`rec_major_pins`), resolves its inductive record and constructor arity, and runs
`check_rules_go_vm_spec` over all rules. -/
theorem check_rules_vm_spec
    (hCore : IxVM.Consistency.Core S₀) (hroles : RolesSpec) (hcallees : CalleesSpec)
    {c_pub c_adv : Ctx}
    (ht_eq : c_adv.t = c_pub.t) (hlim_eq : c_adv.lim = c_pub.lim)
    (hef_pub : EnvFacts c_pub) (hlf_pub : LoadFacts c_pub) (hexact_pub : ExactGetCI c_pub)
    (hef_adv : EnvFacts c_adv) (hlf_adv : LoadFacts c_adv) (hexact_adv : ExactGetCI c_adv)
    {blockNames : List KKey} {f_id : KKey → KKey} {advSet : Bytes.Address → Prop}
    (hf_out : ∀ k, blockNames.contains k = false → f_id k = k)
    (hproj_pub : ∀ sn i entry, c_pub.env.findProj? sn i = some entry →
      blockNames.contains sn = false)
    {cvName : KKey} {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat}
    {rls : List (RecRule .anon)} {a_rm : Bytes.Address}
    {rc rm ty_r rules_ptr src dst aset s_in s_out : SourceValue F}
    {bytes_in : List UInt8} {h h' : Heap F} {calls : List (Call F)}
    (hg_pub : Good c_pub calls) (hg_adv : Good c_adv calls)
    (hlps_lt : lps.length < 4294967296)
    (hlps_perm : lps.Perm (List.range lps.length))
    (hrp_le : rP ≤ mI) (hmi_lt : mI < 288230376151711744)
    (hty_inf : ∃ u_rec, Infer c_pub.env .full 0 (posOf lps tyA) u_rec)
    (hnp_ty : NoProjIn blockNames tyA = true)
    (hnp_ctor : ∀ k cvj cnP cnF, c_pub.env.find? k = some (.ctorInfo cvj cnP cnF) →
      NoProjIn blockNames cvj.type = true)
    (hrule_ctor : ∀ (b_ind : Bytes.Address) (i_ind : Nat) (cv_ind : ConstantVal .anon)
      (caps_ind : Ix.Kernel.IndCaps .anon),
      c_pub.env.find? (c_pub.κ (iprjAddr (ixAddr b_ind) i_ind)) = some (.indInfo cv_ind caps_ind) →
      (∃ bs dom body mb lvls_d, tyA.stripPis mI = some (bs, .forallE dom body mb) ∧
        dom.getAppFn = .const (c_pub.κ (iprjAddr (ixAddr b_ind) i_ind)) lvls_d) →
      (∀ k rl, rls[k]? = some rl → rl.ctor = c_pub.κ (cprjAddr (ixAddr b_ind) i_ind k)) ∧
      (∀ k rl, rls[k]? = some rl → ∀ cvj cnP cnF,
        c_pub.env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
        cvj.levelParams.length = cv_ind.levelParams.length))
    (hrc : RCRep c_pub.t c_pub.lim h rc)
    (hrm : Bytes.RepAddressRef addrTy h a_rm rm)
    (hrm_key : c_pub.κ (ixAddr a_rm) = f_id cvName)
    (haset : AddrMapAll addrMapEnum (fun _ k _ => advSet k) h aset)
    (hren : RenameMap c_pub.κ c_pub.κ f_id h src dst)
    (hty_rep : TmCExact c_pub.κ h (posOf lps tyA) ty_r)
    (hrls : RulesRepExact c_pub.κ h lps 0 rules_ptr rls)
    (hstr : L1.Stream h bytes_in s_in)
    (ev : ObsFn W "KernelModeled::check_rules"
      [rc, rm, .field (lps.length : F), ty_r, .field (rP : F), .field ((mI - rP) : F),
       rules_ptr, src, dst, aset, s_in]
      h s_out h' calls) :
    ∃ (bytes_out : List UInt8) (indKey : KKey) (cnP_ind nC_ind : Nat)
      (bs : List (KExpr × Ix.Kernel.BinderMeta)) (dom body : KExpr) (mb : Ix.Kernel.BinderMeta)
      (lvls_lps : List KLevel) (pins_lps : List KExpr),
      L1.Stream h' bytes_out s_out ∧
      rls.length = nC_ind ∧
      tyA.stripPis mI = some (bs, .forallE dom body mb) ∧
      dom.getAppFn = .const indKey lvls_lps ∧
      dom.getAppArgs.length = cnP_ind + (mI - rP) ∧
      (∀ p ∈ dom.getAppArgs.take cnP_ind, noLooseIn 0 (mI - rP) p = true) ∧
      dom.getAppArgs.drop cnP_ind =
        ((List.range (mI - rP)).map fun m => .bvar (mI - rP - 1 - m)) ∧
      pins_lps = (dom.getAppArgs.take cnP_ind).map (Expr.lowerBVars (mI - rP) 0) ∧
      RawIotaRulesVmRun c_pub c_adv blockNames f_id advSet cvName lps tyA mI rP
        lvls_lps pins_lps 0 rls := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  let nI := mI - rP
  have hrp_val : ZMod.val (rP : F) = rP := SubstAux.val_natCast (by omega)
  have hni_val : ZMod.val (nI : F) = nI := SubstAux.val_natCast (by omega)
  match Obs.«KernelModeled::check_rules».obs ev with
  | .run (m2 := m2) (cs12 := cs12) (x_iaddr := x_iaddr) (x_ilvls := x_ilvls)
      (x_pins := x_pins) (m58 := m58) (p66 := p66) (cs72 := cs72)
      (x_inp := x_inp) (x_inct := x_inct) (x_iblock := x_iblock) (x_iidx := x_iidx)
      (v144 := v144) (m147 := m147) (cs155 := cs155) (cs177 := cs177)
      (ev14 := ev_rmp) (ev74 := ev_ci) (ld68 := ld_ci) (ev157 := ev_rlen)
      (heq173 := heq_inct) (ev179 := ev_go) (hc315 := hc) .. =>
    subst hc
    obtain ⟨iaddr, ilvls_ptr, pins_ptr, a_ind, inp_rmp, bs_pos, dom_pos, body_pos, mb_pos,
        lvls_pos, As_pos, htup_rmp, ha_ind, hilvls_rep, hstrip_pos, hfn_pos, hargs_pos,
        _, _, hdrop_pos, hno_pos, hpins_pos_rep, hAs_len⟩ :=
      rec_major_pins_spec_wide (bounded_sub (fun _ hx => by simp [hx]) hg_pub.2)
        (by rw [hrp_val]; omega) (by rw [hni_val]; omega) ev_rmp (hty_rep 0 zeroGhost)
    injection htup_rmp with hl; injection hl with h1 hl; injection hl with h2 hl
    injection hl with h3; subst h1 h2 h3
    rw [hrp_val, hni_val, show rP + nI = mI by omega] at hstrip_pos
    rw [hrp_val] at hpins_pos_rep
    rw [hni_val] at hdrop_pos hno_pos hpins_pos_rep hAs_len
    -- Pull `stripPis mI (posOf lps tyA)` back to `tyA`
    have hstrip_pull : ∃ bs dom body mb,
        tyA.stripPis mI = some (bs, .forallE dom body mb) ∧
        dom_pos = posOf lps dom := by
      have haux : ∀ (k : Nat) (e : KExpr) {bs' : List (KExpr × Ix.Kernel.BinderMeta)} {rem' : KExpr},
          (posOf lps e).stripPis k = some (bs', rem') →
          ∃ bs₀ rem₀, e.stripPis k = some (bs₀, rem₀) ∧ rem' = posOf lps rem₀ := by
        intro k
        induction k with
        | zero =>
          intro e _ _ hs; injection hs with hp; injection hp with _ h2; subst h2
          exact ⟨[], e, rfl, rfl⟩
        | succ k ih =>
          intro e _ _ hs
          cases e with
          | forallE d b m =>
            simp only [posOf, Expr.instantiateLevelParams, Expr.stripPis] at hs
            cases hsb : (posOf lps b).stripPis k with
            | none => unfold posOf at hsb; simp [hsb] at hs
            | some p =>
              unfold posOf at hsb ⊢
              rw [hsb] at hs; injection hs with hp; injection hp with _ h2; subst h2
              obtain ⟨bs₀, rem₀, hbs₀, hrem₀⟩ := ih b hsb
              exact ⟨(d, m) :: bs₀, rem₀, by simp [Expr.stripPis, hbs₀], hrem₀⟩
          | _ => simp [posOf, Expr.instantiateLevelParams, Expr.stripPis] at hs
      obtain ⟨bs₀, rem₀, hbs₀, hrem₀⟩ := haux mI tyA hstrip_pos
      cases rem₀ with
      | forallE dom body mb =>
        simp only [posOf, Expr.instantiateLevelParams, Expr.forallE.injEq] at hrem₀
        exact ⟨bs₀, dom, body, mb, hbs₀, hrem₀.1⟩
      | _ => simp [posOf, Expr.instantiateLevelParams] at hrem₀
    obtain ⟨bs, dom, body, mb, hstrip_ty, hdom_pos_eq⟩ := hstrip_pull
    let lvls_lps : List KLevel := lvls_pos.map (invPosLevel lps)
    have hlvls_pos_eq : lvls_lps.map (Level.subst lps (posLevels lps)) = lvls_pos := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id lvls_pos]
      exact List.map_congr_left fun u _ => subst_invPosLevel hlps_perm u
    have hfn_dom : dom.getAppFn = .const (c_pub.κ (ixAddr a_ind)) lvls_lps := by
      rw [hdom_pos_eq] at hfn_pos
      exact posOf_inj hlps_perm (by
        unfold posOf at hfn_pos ⊢
        rw [← getAppFn_instantiateLevelParams, hfn_pos]
        simp [Expr.instantiateLevelParams, hlvls_pos_eq])
    have hAs_pos_eq : As_pos = dom.getAppArgs.map (posOf lps) := by
      rw [hdom_pos_eq] at hargs_pos
      unfold posOf at hargs_pos
      rw [getAppArgs_instantiateLevelParams] at hargs_pos
      exact hargs_pos.symm
    -- Lookup `Induct` via `ExactGetCI c_pub`
    obtain ⟨ci_ind, hfind_ind, _, _, v_ind, ld_ind', hcir_ind⟩ :=
      hexact_pub a_ind x_iaddr p66 m2 m58 cs72 ev_ci
        (hg_pub.sub fun _ hx => by simp [hx]) ha_ind
        (not_rec_or_quot_of_load ld_ci (by decide) (by decide))
    rw [ld_ci] at ld_ind'; injection ld_ind' with hv_ind; subst hv_ind
    cases hcir_ind with
    | @induct _ _ _ _ _ _ _ _ cv_ind caps_ind _
        ⟨cnP_ind, _, nC_ind, hinp_f, _, hinct_f, _, _, hnc_lt⟩
        ⟨b_ind, i_ind, hb_ind, hiidx_f, hcv_ind_name⟩ =>
      subst hinp_f hinct_f hiidx_f
      -- `rls.length = nC_ind`
      have ext_rmp_ci := ev_rmp.heap_extends.trans ev_ci.heap_extends
      obtain ⟨hrlen_f, hrlen_lt, hm147_eq⟩ :=
        rulesRepExact_length hg_pub.2 (by simp) ev_rlen (hrls.mono ext_rmp_ci)
      subst hm147_eq
      have hrls_len : rls.length = nC_ind := by
        have hlen_eq := hrlen_f.symm.trans heq_inct
        injection hlen_eq with hf
        have hv := congrArg ZMod.val hf
        rwa [SubstAux.val_natCast (by omega), SubstAux.val_natCast (by omega)] at hv
      -- Level parameter count of `lvls_lps` from `hty_inf` + `infer_stripPis_dom_const_lvls`
      obtain ⟨u_rec, hinf_ty⟩ := hty_inf
      obtain ⟨ci_ind', hfind_ind_ci, hlvls_pos_len⟩ :=
        infer_stripPis_dom_const_lvls mI hinf_ty hstrip_pos hfn_pos
      rw [hfind_ind] at hfind_ind_ci
      injection hfind_ind_ci with hci_eq; subst hci_eq
      have hlvls_lps_len : lvls_lps.length = cv_ind.levelParams.length := by
        simp [lvls_lps, hlvls_pos_len, ConstantInfo.toConstantVal]
      let cnP_rmp : Nat := ZMod.val inp_rmp
      have hdom_args_len : dom.getAppArgs.length = cnP_rmp + nI := by
        have hlen := hAs_len
        rw [hAs_pos_eq, List.length_map] at hlen
        exact hlen
      have hno_dom : ∀ p ∈ dom.getAppArgs.take cnP_rmp, noLooseIn 0 nI p = true := by
        intro p hp
        have hp_pos : posOf lps p ∈ As_pos.take cnP_rmp := by
          rw [hAs_pos_eq, ← List.map_take]
          exact List.mem_map_of_mem hp
        have hn := hno_pos (posOf lps p) hp_pos
        unfold posOf at hn
        rwa [noLooseIn_instantiateLevelParams] at hn
      have hdrop_dom :
          dom.getAppArgs.drop cnP_rmp =
            ((List.range nI).map fun m => .bvar (nI - 1 - m)) := by
        have hd := hdrop_pos
        rw [hAs_pos_eq, ← List.map_drop] at hd
        have hrhs :
            ((List.range nI).map fun m => (Expr.bvar (nI - 1 - m) : KExpr)) =
              (((List.range nI).map fun m => (Expr.bvar (nI - 1 - m) : KExpr))).map (posOf lps) := by
          rw [List.map_map]; rfl
        rw [hrhs] at hd
        exact (List.map_injective_iff.mpr fun _ _ h => posOf_inj hlps_perm h) hd
      let pins_lps : List KExpr := (dom.getAppArgs.take cnP_rmp).map (Expr.lowerBVars nI 0)
      have hpins_pos_eq :
          pins_lps.map (posOf lps) = (As_pos.take cnP_rmp).map (Expr.lowerBVars nI 0) := by
        simp only [pins_lps, hAs_pos_eq, ← List.map_take, List.map_map, Function.comp_def, posOf]
        exact List.map_congr_left fun p _ => (lowerBVars_instantiateLevelParams _ _ nI p 0).symm
      have hnp_pins : ∀ p ∈ pins_lps, NoProjIn blockNames p = true := by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        have hnp_fa := noProjIn_stripPis mI hnp_ty hstrip_ty
        simp only [NoProjIn, Bool.and_eq_true] at hnp_fa
        rw [noProjIn_lowerBVars]
        exact noProjIn_getAppArgs hnp_fa.1 q (List.mem_of_mem_take hq)
      have hind_key_eq :
          c_pub.κ (ixAddr a_ind) = c_pub.κ (iprjAddr (ixAddr b_ind) (ZMod.val i_ind)) :=
        (env_find?_name_eq hfind_ind).symm.trans hcv_ind_name
      have hfind_ind_iprj :
          c_pub.env.find? (c_pub.κ (iprjAddr (ixAddr b_ind) (ZMod.val i_ind))) =
            some (.indInfo cv_ind caps_ind) := by
        rwa [← hind_key_eq]
      obtain ⟨hctor_eq0, hctor_lvls0⟩ :=
        hrule_ctor b_ind (ZMod.val i_ind) cv_ind caps_ind hfind_ind_iprj
          ⟨bs, dom, body, mb, lvls_lps, hstrip_ty, by rwa [← hind_key_eq]⟩
      have ev_go' := ev_go
      rw [show (.field 0 : SourceValue F) = .field ((0 : Nat) : F) by simp] at ev_go'
      obtain ⟨bytes_out, hstr_out, hrules_out⟩ :=
        check_rules_go_vm_spec hCore hroles hcallees ht_eq hlim_eq
          hef_pub hlf_pub hexact_pub hef_adv hlf_adv hexact_adv
          hf_out hproj_pub hlps_lt hlps_perm hrp_le hmi_lt
          hnp_ty hnp_pins hnp_ctor rls 0
          (by omega)
          (fun k rl hk => by simpa [Nat.zero_add] using hctor_eq0 k rl hk)
          (fun k rl hk cvj cnP cnF hfc =>
            hlvls_lps_len.trans (hctor_lvls0 k rl hk cvj cnP cnF hfc).symm)
          (hg_pub.sub fun _ hx => by simp [hx])
          (hg_adv.sub fun _ hx => by simp [hx])
          (hrc.mono ext_rmp_ci)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_rmp_ci hrm) hrm_key
          hb_ind
          (haset.mono ext_rmp_ci) (hren.mono ext_rmp_ci)
          (hty_rep.mono ext_rmp_ci)
          (by rw [hlvls_pos_eq]; exact hilvls_rep.mono ev_ci.heap_extends)
          (by rw [hpins_pos_eq]
              exact RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ev_ci.heap_extends hpins_pos_rep)
          (hrls.mono ext_rmp_ci)
          (hstr.mono ext_rmp_ci)
          ev_go'
      exact ⟨bytes_out, c_pub.κ (ixAddr a_ind), cnP_rmp, nC_ind, bs, dom, body, mb,
        lvls_lps, pins_lps, hstr_out, hrls_len, hstrip_ty, hfn_dom, hdom_args_len,
        hno_dom, hdrop_dom, rfl, hrules_out⟩

end IxVM.Refinement.Decl
