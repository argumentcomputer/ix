import IxVMRefinement.Iota.Rescue
import IxVMRefinement.Whnf.Heads
import IxVMRefinement.Whnf.Proj
import IxVMRefinement.Obs.KernelWhnf2
import IxVMRefinement.Obs.KernelWhnf4
import IxVMRefinement.Obs.KernelWhnf5
import IxVMRefinement.Obs.KernelTypes0

/-! # Step lemmas of `KernelWhnf`: the structure-η rescue and recursor dispatch

* **`eta_iota_fab`**: fabricates `ctor params (proj T 0 M) … (proj T (nF - 1) M)`, checks the
  type's telescope and the constructor's telescope (`certs_all`), and discharges `Red.rescueEta`
  via `DefEq.structEtaTy` (at `0 < nF`) or `DefEq.unitLikeTy` (at `nF = 0`).
* **`try_struct_eta_iota`**: checks the one-rule, zero-index, one-constructor, non-recursive
  guard, establishes `rl.eta = true` via `LoadFacts.etaIota` and `EnvFacts.recEta`, runs
  `eta_iota_fab`, and fires `red_iota` on the fabricated major.
* **`red_rec`**: dispatches a recursor spine to K-like ι (`try_k_synth_iota`), ordinary ι
  (`try_iota`), or structure-η ι (`try_struct_eta_iota`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red DefEq Infer Certs DefEqList)

set_option linter.unusedVariables false

/-! ## Additional context facts for standalone `eta_iota_fab` -/

/-- **Store and loader capabilities of an η-capable inductive**, at the inputs `eta_iota_fab`
receives directly (`rl.eta = true` and `c.ci h (.construct kciEnum "Induct" …) (.indInfo cvT caps)`
without `try_struct_eta_iota`'s `get_ci` / `block_is_multi` / `struct_is_rec` observations):
its η constructor is the first constructor projection of its block/member, its η parameter and
field counts match that constructor's and the loaded parameter count, and a zero-field η-capable
inductive carries the unit-like capability (either non-reserved, or the zero-parameter basis
unit `PUnit`). -/
structure IotaExtraFacts (c : Ctx) : Prop where
  etaCaps : ∀ (h : Heap F) (inl ity nix nc u blk : SourceValue F) (nPT : Nat) (i : F)
      (b : Bytes.Address) (T kc : KKey) (cvT cvc : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (cnP cnF : Nat),
    c.env.find? T = some (.indInfo cvT caps) → caps.eta = true → caps.etaCtor = some kc →
    c.env.find? kc = some (.ctorInfo cvc cnP cnF) →
    c.ci h (.construct kciEnum "Induct" [inl, ity, .field (nPT : F), nix, nc, u, blk, .field i])
      (.indInfo cvT caps) →
    Bytes.RepAddressRef addrTy h b blk →
    kc = c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0) ∧
    caps.etaParams = cnP ∧ caps.etaFields = cnF ∧ cnP = nPT ∧
    (cnF = 0 → caps.unitlike = true ∧ caps.unitParams = cnP ∧
      (Ix.Kernel.reservedBasisNames.contains T = false ∨
        (cnP = 0 ∧ ∀ us, Ix.Kernel.isUnitLikeTy c.env (.const T us) = true)))

/-! ## Helpers -/

private theorem ixAddr_inj {a b : Bytes.Address} (h : ixAddr a = ixAddr b) : a = b := by
  rcases a with ⟨arrA, _⟩
  rcases b with ⟨arrB, _⟩
  injection h with h1
  injection h1 with h2
  subst h2
  rfl

private theorem certs_lic_true {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ {T : KExpr} {As : List KExpr}, Certs env d false T As → Certs env d true T As
  | _, [], .nil => .nil
  | _, _ :: _, .skip hlic _ _ => nomatch hlic
  | _, _ :: _, .cert hinf hdef hr => .cert hinf hdef (certs_lic_true hr)

private theorem defEqList_refl {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ (xs : List KExpr), DefEqList env d xs xs
  | [] => .nil
  | _ :: xs => .cons .refl (defEqList_refl xs)

private theorem infer_io_of_certs {env : Ix.Kernel.Env .anon} {d : Nat} {lic : Bool} :
    ∀ (f T : KExpr) (As : List KExpr),
      Infer env .io d f T → Certs env d lic T As →
      ∃ R, Infer env .io d (Ix.Kernel.Expr.mkAppN f As) R
  | _, T, [], hf, .nil => ⟨T, hf⟩
  | f, _, a :: rest, hf, .skip _ hnev hrest =>
    infer_io_of_certs (.app f a) _ rest (.appSkip hf .refl hnev) hrest
  | f, _, a :: rest, hf, .cert ha hdef hrest =>
    infer_io_of_certs (.app f a) _ rest (.app hf .refl ha hdef) hrest

private theorem isProjFnShape_keyOf (t : Ix.Kernel.RoleTable) (a : _root_.Address) :
    Ix.Kernel.Key.isProjFnShape (keyOf t a) = false := by
  unfold keyOf
  split <;> rfl

private theorem recr_key {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty np ni nm nmi rules kf u blk idx : SourceValue F}
    {cv : Ix.Kernel.ConstantVal .anon} {mI rP : Nat} {rls : List (Ix.Kernel.RecRule .anon)}
    (r : CIRep κ h (.construct kciEnum "Rec" [nl, ty, np, ni, nm, nmi, rules, kf, u, blk, idx])
      (.recInfo cv mI rP rls)) :
    ∃ a : _root_.Address, cv.name = κ a := by
  generalize hv : (Value.construct kciEnum "Rec"
    [nl, ty, np, ni, nm, nmi, rules, kf, u, blk, idx] : SourceValue F) = v at r
  generalize hc : Ix.Kernel.ConstantInfo.recInfo cv mI rP rls = ci at r
  cases r
  case recr _ _ _ _ _ _ _ _ _ _ hkey =>
    injection hc with h1 _ _ _
    subst h1
    obtain ⟨b, i, -, -, hname⟩ := hkey
    rcases hname with hn | hn <;> exact ⟨_, hn⟩
  all_goals (injection hv with _ hc' _; exact absurd hc' (by decide))

/-- A heap spine of `App` cells rooted at a non-`App` cell `hd`. -/
private inductive SpineHead (h : Heap F) (hd : SourceValue F) : SourceValue F → Prop where
  | head {c : String} {xs : List (SourceValue F)}
      (hld : loadValue h hd = .ok (.construct kexprEnum c xs)) (hne : c ≠ "App") :
      SpineHead h hd hd
  | app {f a p : SourceValue F}
      (hld : loadValue h p = .ok (.construct kexprEnum "App" [f, a]))
      (hf : SpineHead h hd f) :
      SpineHead h hd p

private theorem SpineHead.mono {h₁ h₂ : Heap F} {hd p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hs : SpineHead h₁ hd p) : SpineHead h₂ hd p := by
  induction hs with
  | head hld hne => exact .head (ext.loadValue_eq hld) hne
  | app hld _ ih => exact .app (ext.loadValue_eq hld) ih

private theorem apply_spine_head :
    ∀ (n : Nat) {hd0 hd sp r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      calls.length ≤ n →
      ObsFn W "KernelWhnf::apply_spine" [hd, sp] h r h' calls →
      SpineHead h hd0 hd →
      SpineHead h' hd0 r
  | n, hd0, hd, sp, r, h, h', calls, hle, ev, hs => by
    rcases Obs.«KernelWhnf::apply_spine».obs ev with ⟨_, rfl, rfl, -⟩ |
      ⟨a, rest, cs, m, _, hm, ev', hc⟩
    · exact hs
    · subst hc hm
      cases n with
      | zero => simp at hle
      | succ n' =>
        have hcell : (h ++ [.construct kexprEnum "App" [hd, a]])[h.length]? =
            some (.construct kexprEnum "App" [hd, a]) := by simp
        have hs' : SpineHead (h ++ [.construct kexprEnum "App" [hd, a]]) hd0
            (.ptr (.enum kexprEnum) h.length) :=
          .app (loadValue_enum_cell hcell) (hs.mono (Heap.Extends.snoc _ _))
        exact apply_spine_head n' (by simp at hle; omega) ev' hs'

private theorem apply_n_projs_head :
    ∀ (n : Nat) {hd0 hd par maj nf idx r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      calls.length ≤ n →
      ObsFn W "KernelWhnf::apply_n_projs" [hd, par, maj, nf, idx] h r h' calls →
      SpineHead h hd0 hd →
      SpineHead h' hd0 r
  | n, hd0, hd, par, maj, nf, idx, r, h, h', calls, hle, ev, hs => by
    rcases Obs.«KernelWhnf::apply_n_projs».obs ev with ⟨_, rfl, rfl, -⟩ |
      ⟨_, m33, cs74, v81, m83, _, _, hm43, hm91, _, ev76, hc147⟩
    · exact hs
    · subst hc147 hm43 hm91
      cases n with
      | zero => simp at hle
      | succ n' =>
        let m1 : Heap F := h ++ [.construct kexprEnum "Proj" [par, idx, maj]]
        let m2 : Heap F := m1 ++ [.construct kexprEnum "App" [hd, .ptr (.enum kexprEnum) h.length]]
        have ext1 : Heap.Extends h m1 := Heap.Extends.snoc _ _
        have ext2 : Heap.Extends m1 m2 := Heap.Extends.snoc _ _
        have hcell : m2[m1.length]? =
            some (.construct kexprEnum "App" [hd, .ptr (.enum kexprEnum) h.length]) := by
          simp [m1, m2]
        have hs' := SpineHead.app (loadValue_enum_cell hcell) (hs.mono (ext1.trans ext2))
        exact apply_n_projs_head n' (by simp at hle; omega) ev76 hs'

private theorem collect_spine_head :
    ∀ (n : Nat) {hd0 e hd sp : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      calls.length ≤ n →
      ObsFn W "KernelTypes::collect_spine" [e] h (.tuple [hd, sp]) h' calls →
      SpineHead h hd0 e →
      hd = hd0
  | n, hd0, e, hd, sp, h, h', calls, hle, ev, hs => by
    cases hs with
    | head hld hne =>
      match Obs.«KernelTypes::collect_spine».obs ev with
      | .App (ld12 := ld12) .. =>
        rw [hld] at ld12
        injection ld12 with hv
        injection hv with _ hc _
        exact (hne hc).elim
      | .other (he115 := he115) .. =>
        exact (tuple2_inj he115).1
    | app hld hf =>
      match Obs.«KernelTypes::collect_spine».obs ev with
      | .App (x_f := x_f) (x_head := x_head) (cs41 := cs41) (ld12 := ld12) (ev43 := ev43)
          (he69 := he69) (hc106 := hc106) .. =>
        rw [hld] at ld12
        injection ld12 with hv
        injection hv with _ _ hxs
        simp only [List.cons.injEq, and_true] at hxs
        obtain ⟨rfl, -⟩ := hxs
        subst hc106
        obtain ⟨rfl, -⟩ := tuple2_inj he69
        cases n with
        | zero => simp at hle
        | succ n' => exact collect_spine_head n' (by simp at hle; omega) ev43 hf
      | .other (ld12 := ld12) (hne107 := hne107) .. =>
        rw [hld] at ld12
        injection ld12 with hv
        exact (hne107 _ rfl hv.symm).elim

private theorem se_parent_addr_tag_field :
    ∀ (n : Nat) {rt skip w pa : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      calls.length ≤ n →
      ObsFn W "KernelWhnf::se_parent_addr" [rt, skip] h (.tuple [w, pa]) h' calls →
      ∃ t : F, w = .field t
  | n, rt, skip, w, pa, h, h', calls, hle, ev => by
    rcases Obs.«KernelWhnf::se_parent_addr».obs ev with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he125, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, he149, _, _, _⟩ |
      ⟨_, _, _, _, _, he179, _, _, _⟩ |
      ⟨_, _, _, cs243, _, _, _, _, ev245, hc270⟩ |
      ⟨_, _, _, _, _, he279, _, _, _⟩
    · exact ⟨_, (tuple2_inj he125).1⟩
    · exact ⟨_, (tuple2_inj he149).1⟩
    · exact ⟨_, (tuple2_inj he179).1⟩
    · subst hc270
      cases n with
      | zero => simp at hle
      | succ n' => exact se_parent_addr_tag_field n' (by simp at hle; omega) ev245
    · exact ⟨_, (tuple2_inj he279).1⟩

private theorem field_three_ne_zero : (3 : F) ≠ 0 := by
  intro h
  have h3 : ZMod.val ((3 : Nat) : F) = 3 := NatAux.val_natCast (by decide)
  rw [Nat.cast_ofNat, h, ZMod.val_zero] at h3
  exact absurd h3 (by decide)

private theorem red_rec_seg1_ext {rc nl rt lvls hd sp np ni nm nmi rules kf types : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)} {rv : SourceValue F}
    (sg : Obs.«KernelWhnf::red_rec».SegX1 rc nl rt lvls hd sp np ni nm nmi rules kf types
      h rv h' calls) :
    Heap.Extends h h' := by
  rcases sg with
    ⟨_, _, _, _, _, _, _, _, _, _, ev65, _, he146, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, ev65, ev170, _, _⟩ |
    ⟨_, _, he283, _⟩
  · subst he146; exact ObsFn.heap_extends ev65
  · exact (ObsFn.heap_extends ev65).trans (ObsFn.heap_extends ev170)
  · subst he283; exact Heap.Extends.refl _

/-! ## `eta_iota_fab` -/

/-- **`KernelWhnf::eta_iota_fab`**: fabricates the constructor of the major's projections,
certifies the family's and constructor's telescopes (`certs_all`), and establishes `Red.rescueEta`
via `DefEq.structEtaTy` (at `0 < cnF`) or `DefEq.unitLikeTy` (at `cnF = 0`). -/
theorem eta_iota_fab_step (c : Ctx) (hc : CoreFacts c) (hex : IotaExtraFacts c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::eta_iota_fab" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.eta_iota_fab c args h r h' calls := by
  intro rc inl ity inp blk idx par major types hargs good hrc d Γ htypes
    k nl rt np ni nm nmi rules kf cv mI rP rl p ici nix nc u M
    hrec hrleta hp hmh hfindI hciI hM x hr
  subst hargs
  match Obs.«KernelWhnf::eta_iota_fab».obs ev with
  | .Const_n1_n1_n1_Ctor_other (he777 := he0) .. =>
    exact (tag_zero_ne_one (he0.symm.trans hr)).elim
  | .Const_n1_n1_n1_other (he802 := he0) .. =>
    exact (tag_zero_ne_one (he0.symm.trans hr)).elim
  | .Const_n1_n1_other (he826 := he0) .. =>
    exact (tag_zero_ne_one (he0.symm.trans hr)).elim
  | .Const_n1_other (he850 := he0) .. =>
    exact (tag_zero_ne_one (he0.symm.trans hr)).elim
  | .Const_other (he874 := he0) .. =>
    exact (tag_zero_ne_one (he0.symm.trans hr)).elim
  | .other (he898 := he0) .. =>
    exact (tag_zero_ne_one (he0.symm.trans hr)).elim
  | .Const_n1_n1_n1_Ctor_n1 v1 m2 cs12 v16 m26 cs34 m69 cs80 x_th x_targs x_taddr x_tus m137
      x145 y146 m147 x153 y154 m155 cs164 cs186 v189 x196 m198 cs207 cs222 v225 x232 m234 cs243
      m260 cs271 m303 cs314 v318 m330 cs338 m365 m389 p397 cs403 w435 x_cty w436 w437 w438 w439
      x_nf w440 v481 m482 cs492 v518 m519 cs529 m535 v570 m571 cs581 m624 cs635 w652 x_fargs
      m664 cs675 v679 m691 cs699 m726
      ev36 ev14 ev82 ld118 ev166 ev209 op203 ev188 op160 ev245 op239 ev224 op152 ev273 ev340
      hm373 ev316 ev405 ld399 ev494 hm543 ev531 ev583 ev637 ev701 hm734 ev677 he753 he767
      hc768 =>
    obtain ⟨-, rfl⟩ := tuple2_inj (hr.symm.trans he753)
    subst he767 hc768
    obtain ⟨hfind, -⟩ := hrec
    have hrl : rl ∈ [rl] := List.mem_singleton_self rl
    obtain ⟨cvj, cnP, cnF, T', tus', cvT', caps', hcj, hres', hT', heta, hetaCtor, -, hlp_eq⟩ :=
      hc.env.store.recEta hfind hrl hrleta
    obtain ⟨us0, hmh0⟩ := hmh
    obtain ⟨tus, htus⟩ :=
      hc.env.ruleCtorHead k cv mI rP [rl] rl cvj cnP cnF (c.κ (ixAddr p)) us0 hfind hrl hcj hmh0
    rw [htus] at hres'
    injection hres' with hTT _
    subst hTT
    have hciI' := hciI
    obtain ⟨cvT, caps, nPT, nIT, nCT, rfl, ⟨hinl, hinl_lt, hiperm, hity⟩, rfl, rfl, rfl, hnPT,
      -, -, b, i, hb, rfl, -⟩ := WhnfAux.ind_inv hciI
    rw [hfindI] at hT'
    obtain ⟨rfl, rfl⟩ := Ix.Kernel.ConstantInfo.indInfo.inj (Option.some.inj hT')
    subst hinl
    obtain ⟨hctor, hetaP, hetaF, hnP_eq, hunit0⟩ := hex.etaCaps h _ ity _ _ u blk nPT i b
      (c.κ (ixAddr p)) rl.ctor cvT cvj caps cnP cnF hfindI heta hetaCtor hcj hciI' hb
    -- heap extensions
    have e36 := ObsFn.heap_extends ev36
    have e14 := ObsFn.heap_extends ev14
    have e82 := ObsFn.heap_extends ev82
    have e166 := ObsFn.heap_extends ev166
    have e209 := ObsFn.heap_extends ev209
    have e188 := ObsFn.heap_extends ev188
    have e245 := ObsFn.heap_extends ev245
    have e224 := ObsFn.heap_extends ev224
    have e273 := ObsFn.heap_extends ev273
    have e340 := ObsFn.heap_extends ev340
    have e365 : Heap.Extends m330 m365 := by rw [hm373]; exact Heap.Extends.snoc _ _
    have e316 := ObsFn.heap_extends ev316
    have e405 := ObsFn.heap_extends ev405
    have e494 := ObsFn.heap_extends ev494
    have e535 : Heap.Extends m482 m535 := by rw [hm543]; exact Heap.Extends.snoc _ _
    have e531 := ObsFn.heap_extends ev531
    have e583 := ObsFn.heap_extends ev583
    have e637 := ObsFn.heap_extends ev637
    have e701 := ObsFn.heap_extends ev701
    have e726 : Heap.Extends m691 m726 := by rw [hm734]; exact Heap.Extends.snoc _ _
    have e677 := ObsFn.heap_extends ev677
    have X69 : Heap.Extends h m69 := e36.trans (e14.trans e82)
    have Y137 : Heap.Extends m69 m137 := e166.trans (e209.trans (e188.trans (e245.trans e224)))
    have X137 : Heap.Extends h m137 := X69.trans Y137
    have Y365 : Heap.Extends m137 m365 := e273.trans (e340.trans e365)
    have X365 : Heap.Extends h m365 := X137.trans Y365
    have Y482 : Heap.Extends m365 m482 := e316.trans (e405.trans e494)
    have X303 : Heap.Extends h m303 := X365.trans e316
    have X389 : Heap.Extends h m389 := X303.trans e405
    have Y535 : Heap.Extends m69 m535 := Y137.trans (Y365.trans (Y482.trans e535))
    have Z535 : Heap.Extends m389 m535 := e494.trans e535
    have X519 : Heap.Extends h m519 := X389.trans (Z535.trans e531)
    have Y624 : Heap.Extends m535 m624 := e531.trans (e583.trans e637)
    have Y726 : Heap.Extends m624 m726 := e701.trans e726
    have X726 : Heap.Extends h m726 := X519.trans (e583.trans (e637.trans Y726))
    -- major's type, head-normalized
    obtain ⟨TM, hTM, hinfM⟩ := ih.get (.infer .k_infer) (by lt_calls) ev36 rc major types rfl
      (good.sub fun z hz => by simp [hz]) hrc d Γ htypes M hM
    obtain ⟨TW, hTW, hredT⟩ := ih.get (.whnf .whnf) (by lt_calls) ev14 rc v16 types rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono e36 hrc) d Γ (types_mono e36 htypes) TM hTM
    obtain ⟨hd0, sp0, HT, TA, he1, hHT, hTA, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls)
      ev82 v1 rfl (good.sub fun z hz => by simp [hz]) d Γ 0 TW hTW
    obtain ⟨rfl, rfl⟩ := tuple2_inj he1
    obtain ⟨taddr, ust, rfl, hta, hust⟩ := hHT.const_of_load ld118
    -- address, parameter-arity, and level-arity tests
    obtain ⟨rfl, -⟩ := Lib.address_eq_spec ev166 hta (Bytes.repAddressRef_heapMono₂ addrTy X69 hp)
    obtain ⟨rfl, -⟩ := PrimNat.kl_length ev209 (tml_mono e166 hTA)
    have hlenTA_lt : TA.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_targs], m155⟩) (by simp)
      (by simp) (tml_mono e166 hTA)
    obtain rfl := NatAux.sub_ok op203
    obtain ⟨rfl, -⟩ := Lib.is_zero_field ev188
    obtain rfl := NatAux.mul_ok op160
    obtain ⟨ls, hls, hlsEq⟩ := LvListRep.mono (e166.trans (e209.trans e188)) hust
    obtain ⟨rfl, -⟩ := WhnfAux.lv_length ev245 (by rw [klevelListEnum_eq]; exact hls)
    have hlenLS_lt : ls.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [x_tus], m147⟩) (by simp)
      (by simp) hls
    obtain rfl := NatAux.sub_ok op239
    obtain ⟨rfl, -⟩ := Lib.is_zero_field ev224
    have hmul := (NatAux.field_inj (NatAux.mul_ok op152)).symm
    have hmul12 := left_ne_zero_of_mul_eq_one hmul
    have hy146 := WhnfAux.ite01 (right_ne_zero_of_mul_eq_one hmul)
    have hx153 := WhnfAux.ite01 (left_ne_zero_of_mul hmul12)
    have hy154 := WhnfAux.ite01 (right_ne_zero_of_mul hmul12)
    subst taddr
    have hTAlen : TA.length = nPT :=
      (NatAux.natCast_inj (by omega) (by omega)).mp (sub_eq_zero.mp hy154)
    have hlslen : ls.length = cvT.levelParams.length :=
      (NatAux.natCast_inj (by omega) (by omega)).mp (sub_eq_zero.mp hy146)
    have hustlen : ust.length = cvT.levelParams.length :=
      (WhnfAux.evalEqList_length ust ls (hlsEq (fun _ => 0))).trans hlslen
    -- never-zero sort test
    obtain ⟨l', hl', hnz'⟩ := ih.get (.whnf .type_sort_never) (by lt_calls) ev273 ity
      (.field (nPT : F)) x_tus rfl (good.sub fun z hz => by simp [hz]) 0 Γ 0 _ (nPT : F) ust
      (Tm.mono X137 (hity 0 Γ)) rfl (LvListRep.mono Y137 hust) NatAux.field_one_ne_zero
    have hnPTv : ZMod.val (nPT : F) = nPT := NatAux.val_natCast (by omega)
    rw [hnPTv, ← hnP_eq, ← hetaP] at hl'
    obtain ⟨-, halpdT, -⟩ := hc.env.store.wf _ (List.mem_of_find?_eq_some hfindI)
    have halpdT' : cvT.type.allLevelParamsDefined cvT.levelParams = true := halpdT
    obtain ⟨bsT, lT, hsT, hzT⟩ := hc.env.etaSort (c.κ (ixAddr p)) cvT caps hfindI heta
    have hcapsNZ : Ix.Kernel.capsNeverZero cvT.levelParams ust caps = true :=
      capsNeverZero_of_test hustlen halpdT' hsT hzT hl' hnz'
    -- family telescope certificate
    have hIT0 := ih.get (.subst .expr_inst_levels) (by lt_calls) ev340 ity x_tus rfl
      (good.sub fun z hz => by simp [hz]) Γ 0 _ ust (Tm.mono (X137.trans e273) (hity 0 Γ))
      (LvListRep.mono (Y137.trans e273) hust)
    rw [hustlen, posOf_inst hustlen halpdT'] at hIT0
    have hnil330 : c.tml d Γ m365 [] (.ptr (.enum kexprListEnum) m330.length) := by
      rw [hm373]; exact TmL.store_nil m330
    have hcertTR := ih.get (.whnf .certs_all) (by lt_calls) ev316 rc v318 x_targs
      (.ptr (.enum kexprListEnum) m330.length) types rfl (good.sub fun z hz => by simp [hz])
      (RCRep.mono X365 hrc) d Γ (types_mono X365 htypes) _ [] TA
      ((hIT0.of_depth_zero d).mono e365) hnil330 (tml_mono (Y137.trans Y365) hTA)
      NatAux.field_one_ne_zero
    rw [Ix.Kernel.Expr.instantiateList_nil] at hcertTR
    have harityT := (hc.env.familyArity (c.κ (ixAddr p)) cvT caps hfindI).2 heta
    have hcertT0 : Certs c.env d false (cvT.type.instantiateLevelParams cvT.levelParams ust) TA :=
      Specs.Whnf.CertsR.toCerts hcertTR
        (Specs.Whnf.stripPis_isSome_instantiateLevelParams _ _ _ _
          (by rw [hetaP, hnP_eq, ← hTAlen] at harityT; exact harityT))
    have hcertT : Certs c.env d true (cvT.type.instantiateLevelParams cvT.levelParams ust) TA :=
      certs_lic_true hcertT0
    -- constructor load & projection address
    obtain ⟨ciC, hfindC, vC, hldC, hciC⟩ := ih.get (.callees .get_ci_cprj) (by lt_calls) ev405
      blk i 0 b rfl (good.sub fun z hz => by simp [hz])
      (Bytes.repAddressRef_heapMono₂ addrTy X303 hb)
    rw [ZMod.val_zero, ← hctor, hcj] at hfindC
    injection hfindC with hciC_eq
    subst hciC_eq
    rw [ld399] at hldC
    injection hldC with hvC
    subst hvC
    obtain ⟨cvC', nPC', nFC', hctor_inj, ⟨hcnl, -, -, hcty⟩, rfl, rfl, -, hnFC_lt, -⟩ :=
      WhnfAux.ctor_inv hciC
    obtain ⟨rfl, rfl, rfl⟩ := Ix.Kernel.ConstantInfo.ctorInfo.inj hctor_inj
    obtain ⟨cpa, hcpa, hcpaa⟩ := ih.get (.callees .projection_addr_ctor) (by lt_calls) ev494
      i 0 blk b rfl (good.sub fun z hz => by simp [hz])
      (Bytes.repAddressRef_heapMono₂ addrTy X389 hb)
    have hκ : rl.ctor = c.κ (ixAddr cpa) := by rw [hctor, hcpaa, ZMod.val_zero]
    -- fabrication: Const, apply_spine, apply_n_projs, collect_spine
    have hcell535 : m535[m482.length]? =
        some (.construct kexprEnum "Const" [v481, x_tus]) := by
      rw [hm543]; simp
    have hhead : c.tmk d Γ 0 m535 (.const rl.ctor ust) (.ptr (.enum kexprEnum) m482.length) := by
      obtain ⟨ls', hls', hlseq'⟩ := LvListRep.mono Y535 hust
      rw [hκ]
      exact .const hcell535 (Bytes.repAddressRef_heapMono₂ addrTy e535 hcpa) hls' hlseq'
    have hs535 : SpineHead m535 (.ptr (.enum kexprEnum) m482.length)
        (.ptr (.enum kexprEnum) m482.length) :=
      .head (loadValue_enum_cell hcell535) (by decide)
    have happTA := ih.get (.whnf .apply_spine) (by lt_calls) ev531
      (.ptr (.enum kexprEnum) m482.length) x_targs rfl (good.sub fun z hz => by simp [hz])
      d Γ 0 _ TA hhead (tml_mono Y535 hTA)
    have hs519 := apply_spine_head cs529.length (Nat.le_refl _) ev531 hs535
    obtain ⟨m, hm_eq, hFAB0⟩ := ih.get (.whnf .apply_n_projs) (by lt_calls) ev583
      v518 par major (.field (cnF : F)) (.field 0) rfl (good.sub fun z hz => by simp [hz])
      d Γ _ p M (cnF : F) 0 happTA (Bytes.repAddressRef_heapMono₂ addrTy X519 hp)
      (Tm.mono X519 hM) rfl rfl
    have hs571 := apply_n_projs_head cs581.length (Nat.le_refl _) ev583 hs519
    obtain ⟨hdF, spF, HF, FAs, heF, hHF, hFAs, hFAB_eq⟩ := ih.get (.subst .collect_spine)
      (by lt_calls) ev637 v570 rfl (good.sub fun z hz => by simp [hz]) d Γ 0 _ hFAB0
    obtain ⟨rfl, rfl⟩ := tuple2_inj heF
    have hw652 : w652 = .ptr (.enum kexprEnum) m482.length :=
      collect_spine_head cs635.length (Nat.le_refl _) ev637 hs571
    subst hw652
    have hld624 : loadValue m624 (.ptr (.enum kexprEnum) m482.length) =
        .ok (.construct kexprEnum "Const" [v481, x_tus]) :=
      Y624.loadValue_eq (loadValue_enum_cell hcell535)
    obtain ⟨cpa', ust', rfl, -, -⟩ := hHF.const_of_load hld624
    have hFAs_eq : FAs = TA ++ (List.range m).map (fun t =>
        (Ix.Kernel.Expr.proj (c.κ (ixAddr p)) (ZMod.val ((0 : F) + (t : F))) M : KExpr)) := by
      have h1 := congrArg Ix.Kernel.Expr.getAppArgs hFAB_eq
      rw [← mkAppN_mkAppN, getAppArgs_mkAppN, getAppArgs_mkAppN] at h1
      simpa [Ix.Kernel.Expr.getAppArgs] using h1.symm
    have hlenFAs_lt : FAs.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨"KernelWhnf::certs_all",
        [rc, v679, x_fargs,
          .ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m691.length, types],
        m726⟩)
      (by simp) (by simp) (tml_mono Y726 hFAs)
    have hm_lt : m < 2 ^ 39 := by
      have hlen_sum : FAs.length = TA.length + m := by simp [hFAs_eq]
      omega
    rw [zero_add] at hm_eq
    have hm_cnF : m = cnF := (NatAux.natCast_inj (by omega) (by omega)).mp hm_eq
    subst hm_cnF
    have hprojs_eq : ((List.range m).map fun t =>
        (Ix.Kernel.Expr.proj (c.κ (ixAddr p)) (ZMod.val ((0 : F) + (t : F))) M : KExpr)) =
        (List.range m).map fun t => Ix.Kernel.Expr.proj (c.κ (ixAddr p)) t M := by
      apply List.map_congr_left
      intro t ht
      rw [List.mem_range] at ht
      rw [zero_add, NatAux.val_natCast (by omega)]
    rw [hprojs_eq] at hFAB0 hFAs_eq
    rw [← mkAppN_mkAppN, ← hFAs_eq] at hFAB0
    -- constructor telescope certificate
    obtain ⟨-, halpdC, -⟩ := hc.env.store.wf _ (List.mem_of_find?_eq_some hcj)
    have halpdC' : cvj.type.allLevelParamsDefined cvj.levelParams = true := halpdC
    have hustlenC : ust.length = cvj.levelParams.length := by rw [hlp_eq]; exact hustlen
    have hCT0 := ih.get (.subst .expr_inst_levels) (by lt_calls) ev701 x_cty x_tus rfl
      (good.sub fun z hz => by simp [hz]) Γ 0 _ ust
      (Tm.mono (Z535.trans Y624) (hcty 0 Γ)) (LvListRep.mono (Y535.trans Y624) hust)
    rw [hustlenC, posOf_inst hustlenC halpdC'] at hCT0
    have hnil691 : c.tml d Γ m726 [] (.ptr (.enum kexprListEnum) m691.length) := by
      rw [hm734]; exact TmL.store_nil m691
    have hcertCR := ih.get (.whnf .certs_all) (by lt_calls) ev677 rc v679 x_fargs
      (.ptr (.enum kexprListEnum) m691.length) types rfl (good.sub fun z hz => by simp [hz])
      (RCRep.mono X726 hrc) d Γ (types_mono X726 htypes) _ [] FAs
      ((hCT0.of_depth_zero d).mono e726) hnil691 (tml_mono Y726 hFAs) NatAux.field_one_ne_zero
    rw [Ix.Kernel.Expr.instantiateList_nil] at hcertCR
    obtain ⟨-, -, harityC⟩ := hc.env.ruleCtorArity k cv mI rP [rl] hfind rl hrl cvj cnP m hcj
    have hFAslen : FAs.length = cnP + m := by simp [hFAs_eq, hTAlen, hnP_eq]
    have hcertFAB : Certs c.env d false (cvj.type.instantiateLevelParams cvj.levelParams ust) FAs :=
      Specs.Whnf.CertsR.toCerts hcertCR
        (Specs.Whnf.stripPis_isSome_instantiateLevelParams _ _ _ _
          (by rw [← hFAslen] at harityC; exact harityC))
    -- tower slots, etaFabArgsE, and inferred type of FAB
    have htower : Ix.Kernel.towerSlotsAll c.env (c.κ (ixAddr p)) caps.etaFields = true :=
      hc.env.etaTowers (c.κ (ixAddr p)) cvT caps hfindI heta
    have hargsTW : (Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr p)) ust) TA).getAppArgs = TA := by
      rw [getAppArgs_mkAppN]; rfl
    have hetaFab : Ix.Kernel.etaFabArgsE c.env (c.κ (ixAddr p)) ust
        (Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr p)) ust) TA).getAppArgs M caps.etaFields =
        FAs := by
      rw [hargsTW, Ix.Kernel.etaFabArgsE, Ix.Kernel.etaProjs, if_pos htower, hetaF, hFAs_eq]
    obtain ⟨tf, hinfFAB⟩ := infer_io_of_certs _ _ _
      (Infer.const (ci := .ctorInfo cvj cnP m) hcj rfl hustlenC) hcertFAB
    have hredFAB := hc.env.etaType (c.κ (ixAddr p)) rl.ctor cvT cvj caps cnP m
      hfindI heta hetaCtor hcj d ust FAs tf hFAslen hinfFAB
    have htakeFAs : FAs.take cnP = TA := by
      rw [hFAs_eq, List.take_left' (by omega)]
    have hdropFAs : FAs.drop cnP =
        (List.range m).map (fun t => Ix.Kernel.Expr.proj (c.κ (ixAddr p)) t M) := by
      rw [hFAs_eq, List.drop_left' (by omega)]
    rw [htakeFAs] at hredFAB
    -- DefEq FAB M (structEtaTy at 0 < m, unitLikeTy at m = 0)
    have hdefFM : DefEq c.env d (Ix.Kernel.Expr.mkAppN (.const rl.ctor ust) FAs) M := by
      by_cases hm0 : m = 0
      · obtain ⟨hul, huP, hresU⟩ := hunit0 hm0
        refine DefEq.unitLikeTy (a := Ix.Kernel.Expr.mkAppN (.const rl.ctor ust) FAs)
          (ta := tf) (wta := Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr p)) ust) TA)
          (b := M) (tb := TM) (T := c.κ (ixAddr p)) (us := ust) (cvT := cvT) (caps := caps)
          hinfFAB hredFAB (by rw [getAppFn_mkAppN]; rfl) hfindI hul
          (by rw [hargsTW, hTAlen, ← hnP_eq, huP])
          (by rw [hargsTW]; exact hcertT) ?_ (infer_toIo hinfM)
          (.redL hredFAB (.symm (.redL hredT .refl)))
        rcases hresU with hnb | ⟨hc0, hpunit⟩
        · exact .inl hnb
        · have hTA_nil : TA = [] := List.eq_nil_of_length_eq_zero (by omega)
          rw [hTA_nil]
          exact .inr (hpunit ust)
      · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
        have htower' : Ix.Kernel.towerSlotsAll c.env (c.κ (ixAddr p)) m = true := by
          rw [← hetaF]; exact htower
        have hargsFAB : (Ix.Kernel.Expr.mkAppN (.const rl.ctor ust) FAs).getAppArgs = FAs := by
          rw [getAppArgs_mkAppN]; rfl
        refine .symm (DefEq.structEtaTy
          (a := Ix.Kernel.Expr.mkAppN (.const rl.ctor ust) FAs) (b := M) (ta := tf) (tb := TM)
          (c := rl.ctor) (us := ust) (cvc := cvj) (cnP := cnP) (cnF := m)
          (T := c.κ (ixAddr p)) (cvT := cvT) (caps := caps)
          (by rw [getAppFn_mkAppN]; rfl) hcj (by rw [hargsFAB]; exact hFAslen)
          hfindI heta hetaCtor hm_pos htower' hinfFAB
          (by rw [hargsFAB, htakeFAs]; exact hredFAB)
          (by rw [hargsFAB, htakeFAs]; exact hcertT)
          (infer_toIo hinfM) (.redL hredT (.symm (.redL hredFAB .refl)))
          (by rw [hargsFAB, hdropFAs]; exact defEqList_refl _))
    -- scope and leaf guards for FAB
    have hFAB_fin := Tm.mono (e637.trans (Y726.trans e677)) hFAB0
    have hlb := Tm.looseBVarsBounded hFAB_fin
    have hws := Tm.wscopedB (types_mono (X726.trans e677) htypes).2 hFAB_fin
    refine ⟨_, hFAB_fin, ?_⟩
    refine Red.rescueEta (recName := k) (cv := cv) (mI := mI) (rP := rP) (rl := rl)
      (cvj := cvj) (cnP := cnP) (cnF := m) (T := c.κ (ixAddr p)) (tus := tus) (ust := ust)
      (cvT := cvT) (caps := caps) (tm := TM)
      (tmaj := Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr p)) ust) TA)
      hfind hrleta hcj htus hfindI (infer_toIo hinfM) hredT (by rw [getAppFn_mkAppN]; rfl)
      (by rw [hargsTW, hTAlen, ← hnP_eq, hetaP]) hustlen hcapsNZ
      (by rw [hetaFab]) hws hlb ?_ (by rw [hetaFab]; exact hcertFAB)
      (fun htf => by rw [htower] at htf; cases htf) hdefFM
    refine List.all_eq_true.mpr fun l hl => List.contains_iff_mem.mpr ?_
    rcases Ix.Kernel.fvarLeaves_mkAppN hl with h1 | ⟨y, hy, h2⟩
    · simp [Ix.Kernel.Expr.fvarLeaves] at h1
    · rw [hFAs_eq, List.mem_append] at hy
      rcases hy with hyTA | hyP
      · have h3 := Ix.Kernel.fvarLeaves_getAppArgs
          (e := Ix.Kernel.Expr.mkAppN (.const (c.κ (ixAddr p)) ust) TA)
          (by rw [hargsTW]; exact hyTA) l h2
        exact infer_leaves hc.env.storeClosed hinfM l (red_leaves hc.env.storeClosed hredT l h3)
      · rw [List.mem_map] at hyP
        obtain ⟨t, -, rfl⟩ := hyP
        simpa [Ix.Kernel.Expr.fvarLeaves] using h2

/-! ## `try_struct_eta_iota` -/

/-- **`KernelWhnf::try_struct_eta_iota`**: verifies the single-rule non-recursive structure guards,
derives `rl.eta = true` via `LoadFacts.etaIota` and `EnvFacts.recEta`, fabricates the constructor
application (`eta_iota_fab`), and runs `red_iota`. -/
theorem try_struct_eta_iota_step (c : Ctx) (hc : CoreFacts c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::try_struct_eta_iota" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.try_struct_eta_iota c args h r h' calls := by
  intro rc rt lvls sp np nm nmi ni rules types hargs good hrc d Γ htypes
    k us nl kf cv mI rP rls As hrr hlen hAs x hr
  subst hargs
  match Obs.«KernelWhnf::try_struct_eta_iota».obsx ev with
  | .Nil (he24 := he0) .. => exact (tag_zero_ne_one (he0.symm.trans hr)).elim
  | .Cons_Cons (he106 := he0) .. => exact (tag_zero_ne_one (he0.symm.trans hr)).elim
  | .Cons_Nil_n0_other (he232 := he0) .. => exact (tag_zero_ne_one (he0.symm.trans hr)).elim
  | .Cons_Nil_other_bind_Induct_n1_n0_n1 (he530 := he0) .. =>
    exact (tag_zero_ne_one (he0.symm.trans hr)).elim
  | .Cons_Nil_other_bind_Induct_n1_n0_other_other (he778 := he0) .. =>
    exact (tag_zero_ne_one (he0.symm.trans hr)).elim
  | .Cons_Nil_other_bind_Induct_n1_other (he815 := he0) .. =>
    exact (tag_zero_ne_one (he0.symm.trans hr)).elim
  | .Cons_Nil_other_bind_Induct_other (he852 := he0) .. =>
    exact (tag_zero_ne_one (he0.symm.trans hr)).elim
  | .Cons_Nil_other_bind_other (he889 := he0) .. =>
    exact (tag_zero_ne_one (he0.symm.trans hr)).elim
  | .Cons_Nil_other_bind_Induct_n1_n0_other_n1_bind
      w60 x_rest v142 x150 x158 m179 cs190 w267 x_parent m279 p287 cs293 x_ind_nl x_ind_ty
      x_ind_np x_ind_nidx x_num_ctors w310 x_block x_idx m352 x360 y361 m362 cs371 v374 cs393
      m409 cs420 v435 m436 cs446 v465 m466 cs477 v480 v481 m483 cs491 m503 cs511 m564 cs575
      x_fab cs671
      ld12 ld82 op173 op165 op157 ev192 ev295 ld289 op388 ev373 ev395 op367 ev422 ev448 ev493
      ev513 ev479 hne559 ev577 ev673 hc770 hnt0 =>
    subst hc770
    have hrr' := hrr
    obtain ⟨⟨hfind, u0, blk0, idx0, hci⟩, hus⟩ := hrr
    obtain ⟨p', i', m', mi', hval, hnp, hni, hnm, hnmi, hrP, hmI, -, hmIb, hrules⟩ :=
      CIRep.recr_fields hci
    obtain ⟨rl, rls1, hrl_cons, _, hrules1⟩ := RulesRep.cons_of_load hrules ld12
    have hrls1_nil := RulesRep.nil_of_load hrules1 ld82
    subst hrls1_nil hrl_cons
    have hv142 := major_idx_field hnp hni hnm hnmi hmI op173 op165 op157
    subst hv142
    -- parent address & MajorHead
    obtain ⟨tw, rfl⟩ := se_parent_addr_tag_field cs190.length (Nat.le_refl _) ev192
    have htw_ne : tw ≠ 0 := fun h0 => by subst h0; exact hnt0 x_parent rfl
    obtain ⟨p, us_p, hp, hpi_pos⟩ := ih.get (.whnf .se_parent_addr) (by lt_calls) ev192
      rt (.field (mI : F)) rfl (good.sub fun z hz => by simp [hz]) 0 Γ 0 _ (mI : F)
      (hval.2.2.2 0 Γ) rfl tw x_parent rfl htw_ne
    have hmIv : ZMod.val (mI : F) = mI := NatAux.val_natCast (by omega)
    rw [hmIv, Option.map_eq_some_iff] at hpi_pos
    obtain ⟨Dm_pos, hDm_pos, hDm_fn⟩ := hpi_pos
    have hmh : Specs.Whnf.MajorHead c cv mI p := WhnfAux.majorHead_of_pos hDm_pos hDm_fn
    obtain ⟨us_m, hmh0⟩ := hmh
    -- inductive load and counts
    have e192 := ObsFn.heap_extends ev192
    have e295 := ObsFn.heap_extends ev295
    have e373 := ObsFn.heap_extends ev373
    have e395 := ObsFn.heap_extends ev395
    have e422 := ObsFn.heap_extends ev422
    have e448 := ObsFn.heap_extends ev448
    have e493 := ObsFn.heap_extends ev493
    have e513 := ObsFn.heap_extends ev513
    have e479 := ObsFn.heap_extends ev479
    have e577 := ObsFn.heap_extends ev577
    have Y352 : Heap.Extends m179 m352 := e295.trans (e373.trans e395)
    have X352 : Heap.Extends h m352 := e192.trans Y352
    have X409 : Heap.Extends h m409 := X352.trans e422
    have Y466 : Heap.Extends m279 m466 :=
      e373.trans (e395.trans (e422.trans (e448.trans (e493.trans (e513.trans e479)))))
    have X466 : Heap.Extends h m466 := e192.trans (e295.trans Y466)
    have X564 : Heap.Extends h m564 := X466.trans e577
    obtain ⟨ici, hfindI, vI, hldI, hciI⟩ := ih.get (.callees .get_ci) (by lt_calls) ev295
      x_parent p rfl (good.sub fun z hz => by simp [hz]) hp
    rw [ld289] at hldI
    injection hldI with hvI
    subst hvI
    have hciI' := hciI
    obtain ⟨cvT, caps, nPT, nIT, nCT, rfl, ⟨hinl, -, -, hity⟩, rfl, rfl, rfl, hnPT, -, -,
      b, i, hb, rfl, -⟩ := WhnfAux.ind_inv hciI
    obtain rfl := NatAux.sub_ok op388
    obtain ⟨rfl, -⟩ := Lib.is_zero_field ev373
    obtain ⟨rfl, -⟩ := Lib.is_zero_field ev395
    have hmul367 := (NatAux.field_inj (NatAux.mul_ok op367)).symm
    have hnc1 : (nCT : F) = 1 :=
      sub_eq_zero.mp (WhnfAux.ite01 (left_ne_zero_of_mul_eq_one hmul367))
    have hni0 : (nIT : F) = 0 := WhnfAux.ite01 (right_ne_zero_of_mul_eq_one hmul367)
    -- inductRecord & recRules
    obtain ⟨cm, b0, i0, hcm, hb0, hidx0, hinfo⟩ := hc.loads.inductRecord
      x_parent p287 m179 m279 cs293 p x_ind_nl x_ind_ty (.field (nPT : F)) (.field (nIT : F))
      (.field (nCT : F)) w310 x_block (.field i) ev295 (good.sub fun z hz => by simp [hz]) hp ld289
    injection hidx0 with hi0
    subst hi0
    have hb0_eq := addr_det hb0 hb
    subst b0
    obtain ⟨-, hfire, hkeys⟩ := hc.env.recRules k cv mI rP [rl] hfind
    have hrl : rl ∈ [rl] := List.mem_singleton_self rl
    obtain ⟨-, cvj, cnF, hcj⟩ := hfire rl hrl
    have hctor := hkeys (ixAddr p) cm _ us_m hmh0 hcm hinfo 0 rl rfl
    simp only [val_toUInt64_toNat] at hctor
    obtain ⟨tus, htus⟩ :=
      hc.env.ruleCtorHead k cv mI rP [rl] rl cvj rl.ctorParams cnF (c.κ (ixAddr p)) us_m
        hfind hrl hcj hmh0
    -- unpack ev422 (struct_is_rec) to extract block_is_multi = 0
    have ev422_keep := ev422
    have hgood420 : Good c cs420 := good.sub fun z hz => by simp [hz]
    have hbm : ∃ (bq : SourceValue F) (h3 h4 : Heap F) (cs3 : List (Call F)),
        ObsFn W "KernelModeled::block_is_multi" [bq] h3 (.field 0) h4 cs3 ∧ Good c cs3 ∧
          Bytes.RepAddressRef addrTy h3 b bq := by
      match Obs.«KernelWhnf::struct_is_rec».obs ev422 with
      | .Induct_other (he173 := he1) .. => exact (NatAux.field_one_ne_zero he1.symm).elim
      | .other (he180 := he1) .. => exact (NatAux.field_one_ne_zero he1.symm).elim
      | .Induct_n0 m2_sr p9_sr cs15_sr w42 w43 w44 w45 w46 w47 x_block_sr w48 m90_sr cs101_sr
          _ _ _ _ ev17_sr ld11_sr ev103_sr _ _ hc168_sr =>
        have hgood15 : Good c cs15_sr := hgood420.sub fun z hz => by rw [hc168_sr]; simp [hz]
        have hgood101 : Good c cs101_sr := hgood420.sub fun z hz => by rw [hc168_sr]; simp [hz]
        obtain ⟨cm_sr, b_sr, _, hcm_sr, hb_sr, -, hinfo_sr⟩ := hc.loads.inductRecord
          x_parent p9_sr m352 m2_sr cs15_sr p w42 w43 w44 w45 w46 w47 x_block_sr w48
          ev17_sr hgood15 (Bytes.repAddressRef_heapMono₂ addrTy Y352 hp) ld11_sr
        rw [hcm] at hcm_sr
        injection hcm_sr with hcm_eq
        subst hcm_eq
        rw [hinfo] at hinfo_sr
        injection hinfo_sr with hip_eq
        injection hip_eq with _ hb_eq
        obtain rfl := ixAddr_inj hb_eq.symm
        exact ⟨x_block_sr, m2_sr, m90_sr, cs101_sr, ev103_sr, hgood101, hb_sr⟩
    -- major lookup
    obtain ⟨⟨A, hAs_idx, hAs_get⟩, rfl⟩ := Lib.Lists.lookup_spec
      (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := TmE c.κ d Γ)
      (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>».symbol]; exact ev448)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact tml_mono X409 hAs)
    rw [hmIv] at hAs_idx
    -- unpack ev577 (eta_iota_fab) to extract type_sort_never = 1
    have ev577_keep := ev577
    have hgood575 : Good c cs575 := good.sub fun z hz => by simp [hz]
    have ih575 : IH c cs575 := ih.mono (by simp)
    have hsort_obs : ∃ (ust : List KLevel) (l : KLevel),
        piSortAt (ZMod.val (nPT : F)) (posOf cvT.levelParams cvT.type) = some l ∧
          (Ix.Kernel.Level.subst (List.range ust.length) ust l).isNeverZero = true := by
      match Obs.«KernelWhnf::eta_iota_fab».obs ev577 with
      | .Const_n1_n1_n1_Ctor_other (he777 := he0) .. => exact (tag_zero_ne_one he0.symm).elim
      | .Const_n1_n1_n1_other (he802 := he0) .. => exact (tag_zero_ne_one he0.symm).elim
      | .Const_n1_n1_other (he826 := he0) .. => exact (tag_zero_ne_one he0.symm).elim
      | .Const_n1_other (he850 := he0) .. => exact (tag_zero_ne_one he0.symm).elim
      | .Const_other (he874 := he0) .. => exact (tag_zero_ne_one he0.symm).elim
      | .other (he898 := he0) .. => exact (tag_zero_ne_one he0.symm).elim
      | .Const_n1_n1_n1_Ctor_n1 v1_f m2_f cs12_f v16_f m26_f cs34_f m69_f cs80_f x_th_f x_targs_f
          x_taddr_f x_tus_f m137_f _ _ m147_f _ _ m155_f cs164_f cs186_f _ _ m198_f cs207_f
          cs222_f _ _ m234_f cs243_f m260_f cs271_f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ _ _ _ _ _ _
          ev36_f ev14_f ev82_f ld118_f ev166_f ev209_f _ ev188_f _ ev245_f _ ev224_f _ ev273_f
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc768_f =>
        subst hc768_f
        have e36_f := ObsFn.heap_extends ev36_f
        have e14_f := ObsFn.heap_extends ev14_f
        have e82_f := ObsFn.heap_extends ev82_f
        have Y137_f : Heap.Extends m69_f m137_f :=
          (ObsFn.heap_extends ev166_f).trans ((ObsFn.heap_extends ev209_f).trans
            ((ObsFn.heap_extends ev188_f).trans ((ObsFn.heap_extends ev245_f).trans
              (ObsFn.heap_extends ev224_f))))
        have Z137_f : Heap.Extends m466 m137_f := e36_f.trans (e14_f.trans (e82_f.trans Y137_f))
        obtain ⟨TM_f, hTM_f, -⟩ := ih575.get (.infer .k_infer) (by lt_calls) ev36_f
          rc v435 types rfl (hgood575.sub fun z hz => by simp [hz])
          (RCRep.mono X466 hrc) d Γ (types_mono X466 htypes) A
          (Tm.mono (e493.trans (e513.trans e479)) hAs_get)
        obtain ⟨TW_f, hTW_f, -⟩ := ih575.get (.whnf .whnf) (by lt_calls) ev14_f
          rc v16_f types rfl (hgood575.sub fun z hz => by simp [hz])
          (RCRep.mono (X466.trans e36_f) hrc) d Γ (types_mono (X466.trans e36_f) htypes) TM_f hTM_f
        obtain ⟨hd_f, sp_f, HT_f, _, he_f, hHT_f, -, -⟩ :=
          ih575.get (.subst .collect_spine) (by lt_calls) ev82_f v1_f rfl
            (hgood575.sub fun z hz => by simp [hz]) d Γ 0 TW_f hTW_f
        obtain ⟨rfl, rfl⟩ := tuple2_inj he_f
        obtain ⟨_, ust_f, rfl, -, hust_f⟩ := hHT_f.const_of_load ld118_f
        obtain ⟨l_f, hl_f, hnz_f⟩ := ih575.get (.whnf .type_sort_never) (by lt_calls) ev273_f
          x_ind_ty (.field (nPT : F)) x_tus_f rfl (hgood575.sub fun z hz => by simp [hz])
          0 Γ 0 _ (nPT : F) ust_f (Tm.mono (Y466.trans Z137_f) (hity 0 Γ)) rfl
          (LvListRep.mono Y137_f hust_f) NatAux.field_one_ne_zero
        exact ⟨ust_f, l_f, hl_f, hnz_f⟩
    obtain ⟨ust_f, l_f, hl_f, hnz_f⟩ := hsort_obs
    -- LoadFacts.etaIota + EnvFacts.recEta => rl.eta = true
    have ld289' : loadValue m279 p287 = .ok (.construct kciEnum "Induct"
        [x_ind_nl, x_ind_ty, .field (nPT : F), .field 0, .field 1, w310, x_block, .field i]) := by
      rw [← hni0, ← hnc1]; exact ld289
    have hcj_cprj : c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) =
        some (.ctorInfo cvj rl.ctorParams cnF) := by
      rw [← hctor]; exact hcj
    obtain ⟨heta, hetaCtor_cprj, -, -, -, hlp_eq⟩ := hc.loads.etaIota
      x_parent p287 x_ind_nl x_ind_ty w310 x_block m179 m279 cs293 p b i (nPT : F)
      cvT cvj caps rl.ctorParams cnF ust_f l_f
      ev295 (good.sub fun z hz => by simp [hz]) hp ld289' hb hfindI hcj_cprj hbm
      ⟨x_parent, .field 0, m352, m409, cs420, ev422_keep,
        fun h01 => NatAux.field_one_ne_zero h01.symm, hgood420,
        Bytes.repAddressRef_heapMono₂ addrTy Y352 hp⟩
      hl_f hnz_f
    rw [← hctor] at hetaCtor_cprj
    obtain ⟨a_rec, hcv_key⟩ := recr_key hci
    have hk_name : cv.name = k := WhnfAux.name_of_find hfind
    have hk_nproj : Ix.Kernel.Key.isProjFnShape k = false := by
      rw [← hk_name, hcv_key]; exact isProjFnShape_keyOf c.t a_rec
    have hrleta : rl.eta = true := by
      rw [hc.env.recEta k cv mI rP rl hfind]
      simp [Ix.Kernel.recRuleEtaOf, hcj, htus, hfindI, heta, hetaCtor_cprj, hk_nproj, hlp_eq]
    -- fire eta_iota_fab, then red_iota
    obtain ⟨FAB, hFAB, hredM⟩ := ih.get (.whnf .eta_iota_fab) (by lt_calls) ev577_keep
      rc x_ind_nl x_ind_ty (.field (nPT : F)) x_block (.field i) x_parent v435 types rfl
      hgood575 (RCRep.mono X466 hrc) d Γ (types_mono X466 htypes)
      k nl rt np ni nm nmi rules kf cv mI rP rl p (.indInfo cvT caps) (.field (nIT : F))
      (.field (nCT : F)) w310 A (RecRedHyps.mono X466 hrr').1 hrleta
      (Bytes.repAddressRef_heapMono₂ addrTy (e295.trans Y466) hp) hmh hfindI
      (CIRep.mono Y466 hciI') (Tm.mono (e493.trans (e513.trans e479)) hAs_get) x_fab rfl
    have hget : As.getD mI (.bvar 0) = A := by rw [List.getD_eq_getElem?_getD, hAs_idx]; rfl
    exact ih.get (.whnf .red_iota) (by lt_calls) ev673
      rc rt lvls sp np nm nmi ni rules x_parent x_fab types rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono X564 hrc) d Γ (types_mono X564 htypes)
      k us nl kf cv mI rP [rl] p As FAB (RecRedHyps.mono X564 hrr') hlen
      (Bytes.repAddressRef_heapMono₂ addrTy (e295.trans (Y466.trans e577)) hp) hmh
      (tml_mono X564 hAs) hFAB (by rw [hget]; exact hredM) x hr

/-! ## `red_rec` -/

/-- **`KernelWhnf::red_rec`**: checks the recursor's level count and dispatches to K-like ι
(`try_k_synth_iota`, tag `3`), ordinary ι (`try_iota`, tag `1` or stuck tag `2`), or structure-η ι
(`try_struct_eta_iota`, tag `1`). -/
theorem red_rec_step (c : Ctx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::red_rec" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.red_rec c args h r h' calls := by
  intro rc nl rt lvls hd sp np ni nm nmi rules kf types hargs good hrc d Γ htypes
    k us cv mI rP rls As hrr hhd hAs t x hr ht
  subst hargs
  have hrr' := hrr
  obtain ⟨⟨hfind, u0, blk0, idx0, hci⟩, hus⟩ := hrr
  obtain ⟨p', i', m', mi', ⟨hnl, hnl_lt, -, hrt⟩, hnp, hni, hnm, hnmi, -, hmI, -, hmIb, -⟩ :=
    CIRep.recr_fields hci
  -- Helper: check level count from ev23 and op17
  have hlen_of : ∀ {x10 : SourceValue F} {m12 : Heap F} {cs21 : List (Call F)},
      ObsFn W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [lvls] h x10 m12 cs21 →
      evalBinOp .sub x10 nl = .ok (.field 0) →
      (⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [lvls], h⟩ : Call F) ∈ calls →
      us.length = cv.levelParams.length := by
    intro x10 m12 cs21 ev23 op17 hmem
    obtain ⟨ls, hls, hlsEq⟩ := hus
    obtain ⟨rfl, -⟩ := WhnfAux.lv_length ev23 (by rw [klevelListEnum_eq]; exact hls)
    have hlenLS_lt : ls.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [lvls], h⟩) hmem (by simp) hls
    rw [hnl] at op17
    have hsub := NatAux.field_inj (NatAux.sub_ok op17)
    have hlslen : ls.length = cv.levelParams.length :=
      (NatAux.natCast_inj (by omega) (by omega)).mp (sub_eq_zero.mp hsub.symm)
    exact (WhnfAux.evalEqList_length us ls (hlsEq (fun _ => 0))).trans hlslen
  -- Helper: derive MajorHead from rec_to_parent_addr
  have hmh_of_rec : ∀ {m286 m449 : Heap F} {v370 : SourceValue F} {cs457 : List (Call F)},
      Heap.Extends h m286 →
      ObsFn W "KernelCheck::rec_to_parent_addr" [rt, np, nm, nmi, ni] m286 v370 m449 cs457 →
      cs457.length < calls.length →
      Good c cs457 →
      ∃ p : Bytes.Address, RepAddr m449 p v370 ∧ Specs.Whnf.MajorHead c cv mI p := by
    intro m286 m449 v370 cs457 ext286 ev459 hlt457 hgood457
    obtain ⟨p, dom, us_p, hp, hdom, hfn⟩ := ih.get (.callees .rec_to_parent_addr) hlt457 ev459
      rt p' m' mi' i' (by rw [hnp, hnm, hnmi, hni]) hgood457 _
      (fun d' Γ' => Tm.mono ext286 (hrt d' Γ'))
    rw [← hmI, NatAux.val_natCast (by omega)] at hdom
    exact ⟨p, hp, WhnfAux.majorHead_of_pos hdom hfn⟩
  match Obs.«KernelWhnf::red_rec».obsx ev with
  | .n0_other_other (he767 := he0) .. =>
    obtain ⟨ht0, -⟩ := tuple2_inj (hr.symm.trans he0)
    rcases ht with rfl | rfl | rfl
    · exact (NatAux.field_one_ne_zero ht0).elim
    · exact (field_two_ne_zero (Value.field.inj ht0)).elim
    · exact (field_three_ne_zero (Value.field.inj ht0)).elim
  | .other (he791 := he0) .. =>
    obtain ⟨ht0, -⟩ := tuple2_inj (hr.symm.trans he0)
    rcases ht with rfl | rfl | rfl
    · exact (NatAux.field_one_ne_zero ht0).elim
    · exact (field_two_ne_zero (Value.field.inj ht0)).elim
    · exact (field_three_ne_zero (Value.field.inj ht0)).elim
  | .n0_n1_bind x10 m12 cs21 m286 cs288 x_k_reduct ev23 op17 sg293 he326 he340 hc341 =>
    have hlen := hlen_of ev23 op17 (by rw [hc341]; simp)
    subst he340 hc341
    obtain ⟨-, rfl⟩ := tuple2_inj (hr.symm.trans he326)
    have e23 := ObsFn.heap_extends ev23
    rcases sg293 with
      ⟨_, _, _, _, _, _, _, _, _, _, _, he132, _, _⟩ |
      ⟨m52, cs63, v67, x81, x89, w154, x_rec_parent, cs168, hv50, op104, op96, op88, ev65,
        ev170, hc259, hnt0⟩ |
      ⟨_, he269, _, _⟩
    · exact (tag_zero_ne_one he132.symm).elim
    · subst hc259 hv50
      have hv67 := major_idx_field hnp hni hnm hnmi hmI op104 op96 op88
      subst hv67
      have e65 := ObsFn.heap_extends ev65
      have X52 : Heap.Extends h m52 := e23.trans e65
      obtain ⟨tw, rfl⟩ := se_parent_addr_tag_field cs63.length (Nat.le_refl _) ev65
      have htw_ne : tw ≠ 0 := fun h0 => by subst h0; exact hnt0 x_rec_parent rfl
      obtain ⟨p, us_p, hp, hpi_pos⟩ := ih.get (.whnf .se_parent_addr) (by lt_calls) ev65
        rt (.field (mI : F)) rfl (good.sub fun z hz => by simp [hz]) 0 Γ 0 _ (mI : F)
        (Tm.mono e23 (hrt 0 Γ)) rfl tw x_rec_parent rfl htw_ne
      rw [NatAux.val_natCast (n := mI) (by omega), Option.map_eq_some_iff] at hpi_pos
      obtain ⟨Dm_pos, hDm_pos, hDm_fn⟩ := hpi_pos
      have hmh : Specs.Whnf.MajorHead c cv mI p := WhnfAux.majorHead_of_pos hDm_pos hDm_fn
      exact ih.get (.whnf .try_k_synth_iota) (by lt_calls) ev170
        rc rt lvls sp np nm nmi ni rules x_rec_parent types rfl
        (good.sub fun z hz => by simp [hz]) (RCRep.mono X52 hrc) d Γ (types_mono X52 htypes)
        k us nl cv mI rP rls p As (RecRedHyps.mono X52 hrr') hlen hp hmh
        (tml_mono X52 hAs) x rfl
    · exact (tag_zero_ne_one he269.symm).elim
  | .n0_other_n1_bind x10 m12 cs21 v285 m286 cs288 m346 cs356 v370 m449 cs457 x_reduced
      ev23 op17 sg293 ev459 ev358 he532 he546 hc547 _ =>
    have hlen := hlen_of ev23 op17 (by rw [hc547]; simp)
    subst he546 hc547
    obtain ⟨-, rfl⟩ := tuple2_inj (hr.symm.trans he532)
    have X286 : Heap.Extends h m286 := (ObsFn.heap_extends ev23).trans (red_rec_seg1_ext sg293)
    have X449 : Heap.Extends h m449 := X286.trans (ObsFn.heap_extends ev459)
    obtain ⟨p, hp, hmh⟩ := hmh_of_rec X286 ev459 (by lt_calls) (good.sub fun z hz => by simp [hz])
    exact ih.get (.whnf .try_iota) (by lt_calls) ev358
      rc rt lvls sp np nm nmi ni rules types hd v370 rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono X449 hrc) d Γ (types_mono X449 htypes)
      k us nl kf cv mI rP rls p As (RecRedHyps.mono X449 hrr') hlen hp hmh
      (Tm.mono X449 hhd) (tml_mono X449 hAs) 1 x rfl (.inl rfl)
  | .n0_other_n2_bind_n1 x10 m12 cs21 v285 m286 cs288 m346 cs356 v370 m449 cs457 x_stuck
      ev23 op17 sg293 ev459 ev358 _ he584 he598 hc599 _ _ =>
    have hlen := hlen_of ev23 op17 (by rw [hc599]; simp)
    subst he598 hc599
    obtain ⟨-, rfl⟩ := tuple2_inj (hr.symm.trans he584)
    have X286 : Heap.Extends h m286 := (ObsFn.heap_extends ev23).trans (red_rec_seg1_ext sg293)
    have X449 : Heap.Extends h m449 := X286.trans (ObsFn.heap_extends ev459)
    obtain ⟨p, hp, hmh⟩ := hmh_of_rec X286 ev459 (by lt_calls) (good.sub fun z hz => by simp [hz])
    exact ih.get (.whnf .try_iota) (by lt_calls) ev358
      rc rt lvls sp np nm nmi ni rules types hd v370 rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono X449 hrc) d Γ (types_mono X449 htypes)
      k us nl kf cv mI rP rls p As (RecRedHyps.mono X449 hrr') hlen hp hmh
      (Tm.mono X449 hhd) (tml_mono X449 hAs) 2 x rfl (.inr rfl)
  | .n0_other_n2_bind_other_n1_bind x10 m12 cs21 v285 m286 cs288 m346 cs356 v370 m449 cs457
      x_stuck m605 cs616 x_r ev23 op17 sg293 ev459 ev358 _ ev618 he721 he735 hc736 _ _ =>
    have hlen := hlen_of ev23 op17 (by rw [hc736]; simp)
    subst he735 hc736
    obtain ⟨-, rfl⟩ := tuple2_inj (hr.symm.trans he721)
    have X346 : Heap.Extends h m346 :=
      (ObsFn.heap_extends ev23).trans ((red_rec_seg1_ext sg293).trans
        ((ObsFn.heap_extends ev459).trans (ObsFn.heap_extends ev358)))
    exact ih.get (.whnf .try_struct_eta_iota) (by lt_calls) ev618
      rc rt lvls sp np nm nmi ni rules types rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono X346 hrc) d Γ (types_mono X346 htypes)
      k us nl kf cv mI rP rls As (RecRedHyps.mono X346 hrr') hlen (tml_mono X346 hAs) x rfl
  | .n0_other_n2_bind_other_other x10 m12 cs21 v285 m286 cs288 m346 cs356 v370 m449 cs457
      x_stuck v604 m605 cs616 ev23 op17 sg293 ev459 ev358 _ ev618 he744 he758 hc759 _ _ _ =>
    have hlen := hlen_of ev23 op17 (by rw [hc759]; simp)
    subst he758 hc759
    obtain ⟨-, rfl⟩ := tuple2_inj (hr.symm.trans he744)
    have X286 : Heap.Extends h m286 := (ObsFn.heap_extends ev23).trans (red_rec_seg1_ext sg293)
    have X449 : Heap.Extends h m449 := X286.trans (ObsFn.heap_extends ev459)
    obtain ⟨p, hp, hmh⟩ := hmh_of_rec X286 ev459 (by lt_calls) (good.sub fun z hz => by simp [hz])
    obtain ⟨E, hE, hredE⟩ := ih.get (.whnf .try_iota) (by lt_calls) ev358
      rc rt lvls sp np nm nmi ni rules types hd v370 rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono X449 hrc) d Γ (types_mono X449 htypes)
      k us nl kf cv mI rP rls p As (RecRedHyps.mono X449 hrr') hlen hp hmh
      (Tm.mono X449 hhd) (tml_mono X449 hAs) 2 x rfl (.inr rfl)
    exact ⟨E, Tm.mono (ObsFn.heap_extends ev618) hE, hredE⟩

end IxVM.Refinement.Core
