import IxVMRefinement.Decl.LateNatRules
import IxVMRefinement.Decl.NativeRecFieldRange

/-! # The native recursor's rule generators over the stored constructor types

The specifications of `KernelCheck::nat_ctor`, `nat_minors`, `nat_rule_rhs` and
`nat_check_rules` in `LateNatRules.lean` take a load witness that fixes, per constructor, one raw
heap reading of its type (`NatCtorLoadI`), and well-formedness facts about that raw reading
(`NatCtorInfoWf`). Here the load witness gives only the stored type (`NatCtorLoadT`: a `Tm`, in
which a `let` cell reads as its instance) and the well-formedness facts speak only of it
(`NatCtorInfoWfT`). A raw reading is chosen at the load (`natT_tm_raw`, which keeps the stored
binder data on every binder the two readings share), and what the generators need of it is read
off the run:

* `peel_n_foralls` has only a `Forall` arm, so the first `nP + nF` binders are literal;
* `nat_positivity` answers `1` or `2` only on literal `Forall`s over a literal `Const`-headed
  spine, so every recursive field domain is a `RawRecSpine` (`natT_positivity_spine`,
  `natT_rec_idx_spine`).

The run does not fix the head of the return position. `nat_ctor` and `nat_minor_ty` read only
the arguments of its spine (`collect_spine`), and a `let` cell there is a spine without
arguments, while the stored type's spine carries the indices: on a constructor type stored as
`let x := v; T x` (no parameters, no fields, one index) the generated minor premise is
`motive c` where the kernel's is `motive v c`. The minor premises are therefore stated under
`NatCtorRetHeadT`: at every load, the `nP + nF` literal binders end in a literal application
spine over a literal `Const` cell. That is the shape `check_ctor_return_type` checks when the
constructor is admitted. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (Expr Level LevelParam ConstantVal ConstantInfo RecRule Declaration)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## The load witness and the well-formedness facts on the stored type -/

/-- Per-constructor `get_ci_cprj` load witness at member `idx` of the block `b₀`, on the stored
constructor type: each entry `(C, nF, R₀, C₀, recIdx)` carries the key of the constructor
projection `j` of the member, the field count, its bound below `2^56` (what `UInt64::to_field`
asserts when the record is converted, and the load contract keeps) and the stored type `C₀`
(`R₀` is not read). -/
def NatCtorLoadT (κ : _root_.Address → KKey) (b₀ : Bytes.Address) (idx k : Nat)
    (ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat))
    (x_block : SourceValue F) (calls_bound : List (Call F)) : Prop :=
  ∀ (j : Nat), j < ctors_info.length →
    ∀ (p9 : SourceValue F) (h m2 : Heap F) (cs15 : List (Call F))
      (w45 x_cty0 w46 w47 w48 w49 x_nf w50 : SourceValue F),
      (∀ x ∈ cs15, x ∈ calls_bound) →
      Bytes.RepAddressRef addrTy h b₀ x_block →
      ObsFn W "Ingress::get_ci_cprj" [x_block, .field (idx : F), .field (j : F)] h p9 m2 cs15 →
      loadValue m2 p9 = .ok (.construct kciEnum "Ctor"
        [w45, x_cty0, w46, w47, w48, w49, x_nf, w50]) →
      ∀ info, ctors_info[j]? = some info →
        info.1 = κ (cprjAddr (ixAddr b₀) idx j) ∧
        x_nf = .field (info.2.1 : F) ∧
        info.2.1 < 72057594037927936 ∧
        Tm κ 0 (fun _ => default) m2 0 (posOf (List.range k) info.2.2.2.1) x_cty0

theorem NatCtorLoadT.mono_calls {κ : _root_.Address → KKey} {b₀ : Bytes.Address} {idx k : Nat}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)} {x_block : SourceValue F}
    {cs₁ cs₂ : List (Call F)} (hsub : ∀ x ∈ cs₁, x ∈ cs₂)
    (h : NatCtorLoadT κ b₀ idx k ctors_info x_block cs₂) :
    NatCtorLoadT κ b₀ idx k ctors_info x_block cs₁ :=
  fun j hj p9 hp m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hs =>
    h j hj p9 hp m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 (fun x hx => hsub x (hs x hx))

/-- Well-formedness of a `ctors_info` entry for native recursor checking at
`(T, k, large, nP, nIdx, num_ctors)`, on the stored constructor type only: `NatCtorInfoWf`
without its raw-side fields `lps_R`, `strip_R` and `rec_spines`. -/
structure NatCtorInfoWfT (T : KKey) (k : Nat) (large : Bool) (nP nIdx num_ctors : Nat)
    (info : KKey × Nat × KExpr × KExpr × List Nat) : Prop where
  lps_C : info.2.2.2.1.allLevelParamsDefined (List.range k) = true
  noProj_C : noProjAt T info.2.2.2.1 = true
  strip_C : ∃ ecbs eus eargs,
    info.2.2.2.1.stripPis (nP + info.2.1) = some (ecbs, Expr.mkAppN (.const T eus) eargs)
  recIdx_eq : ∀ ecbs ebody,
    (posOf (if large then k :: List.range k else List.range k) info.2.2.2.1).stripPis
      (nP + info.2.1) = some (ecbs, ebody) →
    info.2.2.2.2 = recIdxFrom ecbs T nP info.2.1 0

theorem NatCtorInfoWf.toT {T : KKey} {k : Nat} {large : Bool} {nP nIdx num_ctors : Nat}
    {info : KKey × Nat × KExpr × KExpr × List Nat}
    (h : NatCtorInfoWf T k large nP nIdx num_ctors info) :
    NatCtorInfoWfT T k large nP nIdx num_ctors info :=
  ⟨h.lps_C, h.noProj_C, h.strip_C, h.recIdx_eq⟩

/-- The recursive field indices are field indices. -/
theorem NatCtorInfoWfT.recIdx_lt {T : KKey} {k : Nat} {large : Bool} {nP nIdx num_ctors : Nat}
    {info : KKey × Nat × KExpr × KExpr × List Nat}
    (hwf : NatCtorInfoWfT T k large nP nIdx num_ctors info) :
    ∀ i ∈ info.2.2.2.2, i < info.2.1 := by
  intro i hi
  obtain ⟨ecbs₀, eus₀, eargs₀, hsC₀⟩ := hwf.strip_C
  have hs := ilp_stripPis (if large then k :: List.range k else List.range k)
    (posLevels (if large then k :: List.range k else List.range k)) (nP + info.2.1) hsC₀
  change (posOf (if large then k :: List.range k else List.range k) info.2.2.2.1).stripPis
    (nP + info.2.1) = _ at hs
  rw [hwf.recIdx_eq _ _ hs, recIdxFrom_eq_filter_drop info.2.1 0 (Nat.zero_add _),
    List.drop_zero] at hi
  exact List.mem_range.mp (List.mem_filter.mp hi).1

/-- There are at most as many recursive field indices as fields. -/
theorem NatCtorInfoWfT.recIdx_length_le {T : KKey} {k : Nat} {large : Bool}
    {nP nIdx num_ctors : Nat} {info : KKey × Nat × KExpr × KExpr × List Nat}
    (hwf : NatCtorInfoWfT T k large nP nIdx num_ctors info) :
    info.2.2.2.2.length ≤ info.2.1 := by
  obtain ⟨ecbs₀, eus₀, eargs₀, hsC₀⟩ := hwf.strip_C
  have hs := ilp_stripPis (if large then k :: List.range k else List.range k)
    (posLevels (if large then k :: List.range k else List.range k)) (nP + info.2.1) hsC₀
  change (posOf (if large then k :: List.range k else List.range k) info.2.2.2.1).stripPis
    (nP + info.2.1) = _ at hs
  rw [hwf.recIdx_eq _ _ hs, recIdxFrom_eq_filter_drop info.2.1 0 (Nat.zero_add _),
    List.drop_zero]
  refine (List.length_filter_le _ _).trans ?_
  simp

/-! ## The return position as a heap shape -/

/-- A literal application spine over a literal `Const` cell. -/
inductive NatAppHeadConstT (h : Heap F) : SourceValue F → Prop where
  | const {addr : Nat} {ap lsp : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "Const" [ap, lsp])) :
      NatAppHeadConstT h (.ptr (.enum kexprEnum) addr)
  | app {addr : Nat} {fp ap : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "App" [fp, ap]))
      (rf : NatAppHeadConstT h fp) :
      NatAppHeadConstT h (.ptr (.enum kexprEnum) addr)

/-- `n` literal `Forall` cells, then a literal application spine over a literal `Const` cell. -/
inductive NatRetHeadT (h : Heap F) : Nat → SourceValue F → Prop where
  | zero {p : SourceValue F} (hhead : NatAppHeadConstT h p) : NatRetHeadT h 0 p
  | succ {n addr : Nat} {xt xb xm : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "Forall" [xt, xb, xm]))
      (hrest : NatRetHeadT h n xb) :
      NatRetHeadT h (n + 1) (.ptr (.enum kexprEnum) addr)

/-- At every `get_ci_cprj` load of constructor `j` of member `idx` of the block `b₀`, the loaded
type's first `nP + nF` binders are literal and end in a literal application spine over a literal
`Const` cell. -/
def NatCtorRetHeadT (b₀ : Bytes.Address) (idx nP : Nat)
    (ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat))
    (x_block : SourceValue F) (calls_bound : List (Call F)) : Prop :=
  ∀ (j : Nat), j < ctors_info.length →
    ∀ (p9 : SourceValue F) (h m2 : Heap F) (cs15 : List (Call F))
      (w45 x_cty0 w46 w47 w48 w49 x_nf w50 : SourceValue F),
      (∀ x ∈ cs15, x ∈ calls_bound) →
      Bytes.RepAddressRef addrTy h b₀ x_block →
      ObsFn W "Ingress::get_ci_cprj" [x_block, .field (idx : F), .field (j : F)] h p9 m2 cs15 →
      loadValue m2 p9 = .ok (.construct kciEnum "Ctor"
        [w45, x_cty0, w46, w47, w48, w49, x_nf, w50]) →
      ∀ info, ctors_info[j]? = some info →
        NatRetHeadT m2 (nP + info.2.1) x_cty0

theorem NatCtorRetHeadT.mono_calls {b₀ : Bytes.Address} {idx nP : Nat}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)} {x_block : SourceValue F}
    {cs₁ cs₂ : List (Call F)} (hsub : ∀ x ∈ cs₁, x ∈ cs₂)
    (h : NatCtorRetHeadT b₀ idx nP ctors_info x_block cs₂) :
    NatCtorRetHeadT b₀ idx nP ctors_info x_block cs₁ :=
  fun j hj p9 hp m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hs =>
    h j hj p9 hp m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 (fun x hx => hsub x (hs x hx))

private theorem natT_mkAppN_snoc :
    ∀ (as : List KExpr) (f a : KExpr), Expr.mkAppN f (as ++ [a]) = .app (Expr.mkAppN f as) a
  | [], _, _ => rfl
  | _ :: as, f, a => natT_mkAppN_snoc as (.app f _) a

private theorem natT_app_spine {f : KExpr}
    (hf : ∃ c us ras, f = Expr.mkAppN (.const c us) ras) (a : KExpr) :
    ∃ c us ras, Expr.app f a = Expr.mkAppN (.const c us) ras := by
  obtain ⟨c, us, ras, rfl⟩ := hf
  exact ⟨c, us, ras ++ [a], (natT_mkAppN_snoc ras _ a).symm⟩

/-- A raw reading of a pointer to a `Const` cell is the stored reading. -/
theorem natT_rawTm_eq_of_const_load {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p ap lsp : SourceValue F}
    (rep : RawTm κ d Γ h k R E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Const" [ap, lsp])) : R = E := by
  cases rep with
  | const cell _ _ _ => rfl
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell ld (by decide)).elim

/-- A raw reading of a literal application spine over a literal `Const` cell is one. -/
theorem natT_rawTm_appHeadConst {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {p : SourceValue F} (hp : NatAppHeadConstT h p) :
    ∀ {k : Nat} {R E : KExpr}, RawTm κ d Γ h k R E p →
      ∃ c us ras, R = Expr.mkAppN (.const c us) ras := by
  induction hp with
  | const cell =>
    intro k R E hR
    have ld := loadValue_enum_cell cell
    cases hR with
    | const _ _ _ _ => exact ⟨_, _, [], rfl⟩
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ | proj cell' _ _ =>
      exact (load_cell_ne cell' ld (by decide)).elim
  | app cell _ ih =>
    intro k R E hR
    have ld := loadValue_enum_cell cell
    cases hR with
    | app cell' rf _ =>
      obtain ⟨-, hxs⟩ := load_cell cell' ld
      injection hxs with h1 _
      subst h1
      exact natT_app_spine (ih rf) _
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ _ | const cell' _ _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ | proj cell' _ _ =>
      exact (load_cell_ne cell' ld (by decide)).elim

/-- A raw reading of a pointer of shape `NatRetHeadT h n` strips `n` binders down to an
application spine over a constant. -/
theorem natT_rawTm_retHead {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (n : Nat) {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F},
      NatRetHeadT h n p → RawTm κ d Γ h k R E p →
      ∃ rbs c us ras, R.stripPis n = some (rbs, Expr.mkAppN (.const c us) ras)
  | 0, h, k, R, E, p, hp, hR => by
    cases hp with
    | zero hhead =>
      obtain ⟨c, us, ras, rfl⟩ := natT_rawTm_appHeadConst hhead hR
      exact ⟨[], c, us, ras, rfl⟩
  | n + 1, h, k, R, E, p, hp, hR => by
    cases hp with
    | succ cell hrest =>
      have ld := loadValue_enum_cell cell
      obtain ⟨Rt, Rb, mR, T', B, ℓ, hReq, _, _, hb, _⟩ := hR.forallE_of_load ld
      subst hReq
      obtain ⟨rbs, c, us, ras, hs⟩ := natT_rawTm_retHead n hrest hb
      exact ⟨(Rt, mR) :: rbs, c, us, ras, by simp [Expr.stripPis, hs]⟩

private theorem natT_appHeadConst_const {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {c : KKey} {us : List KLevel} :
    ∀ {k : Nat} {E : KExpr} {p : SourceValue F},
      RawTm κ d Γ h k (.const c us) E p → NatAppHeadConstT h p := by
  intro k E p hR
  cases hR with
  | const cell _ _ _ => exact .const cell

private theorem natT_appHeadConst_app {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} :
    ∀ (ras : List KExpr) {f : KExpr},
      (∀ {k : Nat} {E : KExpr} {p : SourceValue F},
        RawTm κ d Γ h k f E p → NatAppHeadConstT h p) →
      ∀ {k : Nat} {E : KExpr} {p : SourceValue F},
        RawTm κ d Γ h k (Expr.mkAppN f ras) E p → NatAppHeadConstT h p
  | [], f, hf => fun hR => hf hR
  | a :: ras, f, hf => fun hR =>
    natT_appHeadConst_app ras (f := .app f a)
      (fun hR' => by
        cases hR' with
        | app cell rf _ => exact .app cell (hf rf))
      hR

/-- A raw reading that strips `n` binders down to an application spine over a constant is, in
the heap, of shape `NatRetHeadT h n`. -/
theorem natT_retHead_of_rawTm {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} :
    ∀ (n : Nat) {k : Nat} {R E : KExpr} {p : SourceValue F}
      {rbs : List (KExpr × Ix.Kernel.BinderMeta)} {c : KKey} {us : List KLevel}
      {ras : List KExpr},
      RawTm κ d Γ h k R E p →
      R.stripPis n = some (rbs, Expr.mkAppN (.const c us) ras) →
      NatRetHeadT h n p
  | 0, k, R, E, p, rbs, c, us, ras, hR, hs => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨_, rfl⟩ := hs
    exact .zero (natT_appHeadConst_app ras (fun hR' => natT_appHeadConst_const hR') hR)
  | n + 1, k, R, E, p, rbs, c, us, ras, hR, hs => by
    cases R with
    | forallE Rt Rb m =>
      rw [Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨rbs', rbody'⟩, hs', hp⟩ := hs
      simp only [Prod.mk.injEq] at hp
      obtain ⟨_, rfl⟩ := hp
      cases hR with
      | forallE cell _ rb _ => exact .succ cell (natT_retHead_of_rawTm n rb hs')
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
    | lit _ | proj _ _ _ => simp [Expr.stripPis] at hs

/-- The raw load witness and the raw well-formedness facts give the return-position shape: the
stored-type statements below specialize to the raw-reading ones. -/
theorem NatCtorRetHeadT.of_natCtorLoadI {κ : _root_.Address → KKey} {T : KKey}
    {b₀ : Bytes.Address} {idx k nP nIdx num_ctors : Nat} {large : Bool}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)} {x_block : SourceValue F}
    {cs : List (Call F)}
    (hload : NatCtorLoadI κ b₀ idx k ctors_info x_block cs)
    (hwf_all : ∀ info ∈ ctors_info, NatCtorInfoWf T k large nP nIdx num_ctors info) :
    NatCtorRetHeadT b₀ idx nP ctors_info x_block cs := by
  intro j hj p9 hp m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hs hb ev ld info hinfo
  obtain ⟨_, _, hRaw⟩ :=
    hload j hj p9 hp m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hs hb ev ld info hinfo
  obtain ⟨rcbs, rus, rargs, hsR⟩ := (hwf_all info (List.mem_of_getElem? hinfo)).strip_R
  rw [posOf_range] at hRaw
  exact natT_retHead_of_rawTm _ hRaw hsR

/-! ## Raw readings that keep the stored binder data -/

/-- At every binder the raw reading `R` shares with the stored reading `E` (each `∀` whose
counterpart is a `∀`), `R` carries `E`'s binder datum. -/
inductive NatMetaAgree : KExpr → KExpr → Prop where
  | forallE {Rt Rb Et Eb : KExpr} {m : Ix.Kernel.BinderMeta} :
      NatMetaAgree Rt Et → NatMetaAgree Rb Eb →
      NatMetaAgree (.forallE Rt Rb m) (.forallE Et Eb m)
  | other {R E : KExpr} :
      (∀ (t b : KExpr) (m : Ix.Kernel.BinderMeta), R ≠ .forallE t b m) → NatMetaAgree R E

/-- A term read through `Tm` has a raw reading that keeps the stored binder data. -/
theorem natT_tm_raw {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F}
    (rep : Tm κ d Γ h k E p) : ∃ R, RawTm κ d Γ h k R E p ∧ NatMetaAgree R E := by
  induction rep with
  | bvarLocal cell hs hi =>
    exact ⟨_, .bvarLocal cell hs hi, .other (by intro _ _ _ h; cases h)⟩
  | bvarFree cell hs hk hd =>
    exact ⟨_, .bvarFree cell hs hk hd, .other (by intro _ _ _ h; cases h)⟩
  | sort cell rl hu => exact ⟨_, .sort cell rl hu, .other (by intro _ _ _ h; cases h)⟩
  | const cell ra rls hus =>
    exact ⟨_, .const cell ra rls hus, .other (by intro _ _ _ h; cases h)⟩
  | app cell _ _ ihf iha =>
    obtain ⟨_, hf, _⟩ := ihf
    obtain ⟨_, ha, _⟩ := iha
    exact ⟨_, .app cell hf ha, .other (by intro _ _ _ h; cases h)⟩
  | @lam k addr tp bp lp T B ℓ cell _ _ rl iht ihb =>
    obtain ⟨_, ht, _⟩ := iht
    obtain ⟨_, hb, _⟩ := ihb
    exact ⟨_, .lam (mR := bmeta ℓ) cell ht hb rl, .other (by intro _ _ _ h; cases h)⟩
  | @forallE k addr tp bp lp T B ℓ cell _ _ rl iht ihb =>
    obtain ⟨_, ht, hat⟩ := iht
    obtain ⟨_, hb, hab⟩ := ihb
    exact ⟨_, .forallE (mR := bmeta ℓ) cell ht hb rl, .forallE hat hab⟩
  | letE cell _ _ _ iht ihv ihb =>
    obtain ⟨_, ht, _⟩ := iht
    obtain ⟨_, hv, _⟩ := ihv
    obtain ⟨_, hb, _⟩ := ihb
    exact ⟨_, .letE (mR := default) cell ht hv hb, .other (by intro _ _ _ h; cases h)⟩
  | litNat cell rl hc => exact ⟨_, .litNat cell rl hc, .other (by intro _ _ _ h; cases h)⟩
  | litStr cell rb hs => exact ⟨_, .litStr cell rb hs, .other (by intro _ _ _ h; cases h)⟩
  | proj cell ra _ ihe =>
    obtain ⟨_, he, _⟩ := ihe
    exact ⟨_, .proj cell ra he, .other (by intro _ _ _ h; cases h)⟩

theorem NatMetaAgree.ilp (ks : List LevelParam) (us : List KLevel) {R E : KExpr}
    (hag : NatMetaAgree R E) :
    NatMetaAgree (R.instantiateLevelParams ks us) (E.instantiateLevelParams ks us) := by
  induction hag with
  | forallE _ _ iht ihb =>
    simp only [Expr.instantiateLevelParams]
    exact .forallE iht ihb
  | @other R E hne =>
    refine .other ?_
    intro t b m h
    cases R
    case forallE t' b' m' => exact hne t' b' m' rfl
    all_goals simp [Expr.instantiateLevelParams] at h

theorem NatMetaAgree.stripPis :
    ∀ (n : Nat) {R E rbody ebody : KExpr} {rbs ebs : List (KExpr × Ix.Kernel.BinderMeta)},
      NatMetaAgree R E →
      R.stripPis n = some (rbs, rbody) →
      E.stripPis n = some (ebs, ebody) →
      (∀ i < n, NatMetaAgree (rbs.getD i default).1 (ebs.getD i default).1) ∧
        NatMetaAgree rbody ebody
  | 0, R, E, rbody, ebody, rbs, ebs, hag, hR, hE => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hR hE
    obtain ⟨_, rfl⟩ := hR
    obtain ⟨_, rfl⟩ := hE
    exact ⟨(fun _ hi => nomatch hi), hag⟩
  | n + 1, R, E, rbody, ebody, rbs, ebs, hag, hR, hE => by
    cases hag with
    | forallE hagt hagb =>
      rw [Expr.stripPis, Option.map_eq_some_iff] at hR
      rw [Expr.stripPis, Option.map_eq_some_iff] at hE
      obtain ⟨⟨rbs', rbody'⟩, hR', hpR⟩ := hR
      obtain ⟨⟨ebs', ebody'⟩, hE', hpE⟩ := hE
      simp only [Prod.mk.injEq] at hpR hpE
      obtain ⟨rfl, rfl⟩ := hpR
      obtain ⟨rfl, rfl⟩ := hpE
      obtain ⟨hdoms, hbody⟩ := NatMetaAgree.stripPis n hagb hR' hE'
      refine ⟨fun i hi => ?_, hbody⟩
      cases i with
      | zero => exact hagt
      | succ i' => simpa [List.getD_cons_succ] using hdoms i' (by omega)
    | other hne =>
      cases R
      case forallE t b m => exact absurd rfl (hne t b m)
      all_goals simp [Expr.stripPis] at hR

/-! ## Recursive field domains are read as `RawRecSpine`s -/

/-- `KernelCheck::nat_positivity` answering other than `3` reads literal `Forall`s over a
literal `Const`-headed spine of `T`: on a raw reading that keeps the stored binder data, a
`RawRecSpine`. -/
theorem natT_positivity_spine {κ : _root_.Address → KKey} {T : KKey} {bT : Bytes.Address}
    (hT : κ (ixAddr bT) = T) :
    ∀ (n : Nat) {d : Nat} {Γ : Nat → KExpr} {k : Nat} {R E : KExpr}
      {pe pt plps pnp pni po pk r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ n →
      r ≠ .field 3 →
      RawTm κ d Γ h k R E pe →
      NatMetaAgree R E →
      Bytes.RepAddressRef addrTy h bT pt →
      ObsFn W "KernelCheck::nat_positivity" [pe, pt, plps, pnp, pni, po, pk] h r h' cs →
      RawRecSpine T R E
  | n, d, Γ, k, R, E, pe, pt, plps, pnp, pni, po, pk, r, h, h', cs,
      hlen, hr3, hRE, hag, hpt, ev => by
    match Obs.«KernelCheck::nat_positivity».obs ev with
    | .Forall_n1 (he71 := hr) .. => exact absurd hr hr3
    | .Forall_other (ld12 := ld) (ev50 := ev_m) (ev83 := ev_p) (hc148 := hc) .. =>
      subst hc
      cases n with
      | zero => simp at hlen
      | succ n' =>
        obtain ⟨Rd, Rb, mR, Ed, Eb, ℓ, hR, hE, hd, hb, _⟩ := hRE.forallE_of_load ld
        subst hR hE
        obtain ⟨_, rfl⟩ := nat_mentions_ret_bit n' (by simp at hlen; omega) hd.toTm hpt ev_m
        cases hag with
        | forallE _ hagb =>
          exact .forallE
            (natT_positivity_spine hT n' (by simp at hlen; omega) hr3 hb hagb hpt ev_p)
        | other hne => exact (hne _ _ _ rfl).elim
    | .other_Const_n1_n1_n0 (x225 := x225) (y226 := y226) (y234 := y234)
        (ev166 := ev_sp) (ld199 := ld_h) (ev246 := ev_eq)
        (op240 := op_m1) (op232 := op_m2) .. =>
      obtain ⟨hd, _, Rh, Eh, Ras, Eas, htup, hH, _, _, hR_eq, hE_eq, _⟩ :=
        collect_spine_rawTm_spec hRE ev_sp
      injection htup with hl; injection hl with h1 _; subst h1
      obtain ⟨a, us, hEh, ra, _, _, _⟩ := hH.toTm.const_of_load ld_h
      have hRh : Rh = Eh := natT_rawTm_eq_of_const_load hH ld_h
      have hpt' := Bytes.repAddressRef_heapMono₂ addrTy ev_sp.heap_extends hpt
      obtain ⟨hx233, _⟩ := Lib.address_eq_spec ev_eq ra hpt'
      have hab : a = bT := by
        by_cases h_eq : a = bT
        · exact h_eq
        · rw [ite_eq_right h_eq] at hx233
          rw [hx233] at op_m1
          have hx225 : x225 = .field 0 := by
            cases y234 <;> simp [evalBinOp] at op_m1
            exact op_m1.symm
          rw [hx225] at op_m2
          cases y226 <;> simp [evalBinOp] at op_m2
      subst hab
      rw [hR_eq, hE_eq, hRh, hEh, hT]
      exact .app
    | .other_Const_n1_n1_other (x225 := x225) (y226 := y226) (y234 := y234)
        (ev166 := ev_sp) (ld199 := ld_h) (ev246 := ev_eq)
        (op240 := op_m1) (op232 := op_m2) .. =>
      obtain ⟨hd, _, Rh, Eh, Ras, Eas, htup, hH, _, _, hR_eq, hE_eq, _⟩ :=
        collect_spine_rawTm_spec hRE ev_sp
      injection htup with hl; injection hl with h1 _; subst h1
      obtain ⟨a, us, hEh, ra, _, _, _⟩ := hH.toTm.const_of_load ld_h
      have hRh : Rh = Eh := natT_rawTm_eq_of_const_load hH ld_h
      have hpt' := Bytes.repAddressRef_heapMono₂ addrTy ev_sp.heap_extends hpt
      obtain ⟨hx233, _⟩ := Lib.address_eq_spec ev_eq ra hpt'
      have hab : a = bT := by
        by_cases h_eq : a = bT
        · exact h_eq
        · rw [ite_eq_right h_eq] at hx233
          rw [hx233] at op_m1
          have hx225 : x225 = .field 0 := by
            cases y234 <;> simp [evalBinOp] at op_m1
            exact op_m1.symm
          rw [hx225] at op_m2
          cases y226 <;> simp [evalBinOp] at op_m2
      subst hab
      rw [hR_eq, hE_eq, hRh, hEh, hT]
      exact .app
    | .other_Const_n1_other (he509 := hr) .. => exact absurd hr hr3
    | .other_Const_other (he516 := hr) .. => exact absurd hr hr3
    | .other_other (he523 := hr) .. => exact absurd hr hr3

/-- `KernelCheck::nat_rec_idx` from field `i` upward reads every field it collects as a
`RawRecSpine`, on a raw reading whose field domains keep the stored binder data. -/
theorem natT_rec_idx_spine {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {T : KKey} {bT : Bytes.Address} {nP nIdx nF : Nat}
    {Rcty Ecty rbody ebody : KExpr} {rcbs ecbs : List (KExpr × Ix.Kernel.BinderMeta)}
    (hT : κ (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, κ (ixAddr a) = T → a = bT)
    (hnPF_lt : nP + nF < 18446744069414584321)
    (hsR : Rcty.stripPis (nP + nF) = some (rcbs, rbody))
    (hsE : Ecty.stripPis (nP + nF) = some (ecbs, ebody))
    (hnp_dom : ∀ idx < nF, noProjAt T (ecbs.getD (nP + idx) default).1 = true)
    (hag_dom : ∀ idx < nF,
      NatMetaAgree (rcbs.getD (nP + idx) default).1 (ecbs.getD (nP + idx) default).1) :
    ∀ (rem i : Nat) {pcty pt plps r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      i + rem = nF →
      RawTm κ 0 Γ₀ h 0 Rcty Ecty pcty →
      Bytes.RepAddressRef addrTy h bT pt →
      ObsFn W "KernelCheck::nat_rec_idx"
        [pcty, pt, plps, .field (nP : F), .field (nIdx : F), .field (nF : F), .field (i : F)]
        h r h' cs →
      ∀ idx ∈ recIdxFrom ecbs T nP nF i,
        RawRecSpine T (rcbs.getD (nP + idx) default).1 (ecbs.getD (nP + idx) default).1
  | 0, i, pcty, pt, plps, r, h, h', cs, hir, _, _, _ => by
    subst hir
    rw [recIdxFrom_ge (by omega)]
    intro idx hmem
    exact nomatch hmem
  | rem + 1, i, pcty, pt, plps, r, h, h', cs, hir, hRaw, hpt, ev => by
    have hi_lt : i < nF := by omega
    match Obs.«KernelCheck::nat_rec_idx».obs ev with
    | .n0 (op17 := op17) .. =>
      have hsub := evalBinOp_sub_nat (by omega : i ≤ nF) op17
      have hval := congrArg ZMod.val (Value.field.inj hsub.symm)
      have h1 : ZMod.val ((nF - i : Nat) : F) = nF - i :=
        ZMod.val_natCast_of_lt (by omega : nF - i < 18446744069414584321)
      rw [h1, ZMod.val_zero] at hval
      omega
    | .other_n0 (m38 := m38) (m180 := m180) (v213 := v213) (m202 := m202)
        (ev50 := ev_dom) (sg187 := sg) (op227 := op227) (ev212 := ev_iz)
        (op312 := op312) (ev249 := ev_rec) .. =>
      obtain ⟨hm38, hdom⟩ := nat_field_dom_rawTm_spec hi_lt (by omega) hRaw hsR hsE ev_dom
      rw [hm38] at sg
      have hsg : m180 = h ∧ (ecbs.getD (nP + i) default).1.mentionsConst T = false := by
        cases sg with
        | n0 _ cs87 ev89 _ hm76 _ =>
          subst hm76
          obtain ⟨hmen0, hm_eq⟩ := nat_mentions_zero_spec hκ_inj cs87.length (Nat.le_refl _)
            hdom.toTm hpt (hnp_dom i hi_lt) (fun _ hk => nomatch hk) ev89
          exact ⟨hm_eq, hmen0⟩
        | other v75 m76 cs87 cs120 ev89 _ ev122 _ =>
          obtain ⟨_, hm76_eq⟩ :=
            nat_mentions_ret_bit cs87.length (Nat.le_refl _) hdom.toTm hpt ev89
          rw [hm76_eq] at ev122
          have h0_ne_3 : (.field 0 : SourceValue F) ≠ .field 3 := by
            intro h03
            have hv := congrArg ZMod.val (Value.field.inj h03)
            rw [ZMod.val_zero, show (3 : F) = ((3 : Nat) : F) from rfl,
              ZMod.val_natCast_of_lt (by decide)] at hv
            exact absurd hv (by decide)
          obtain ⟨h012, _⟩ := nat_positivity_ok_spec hT cs120.length (Nat.le_refl _)
            h0_ne_3 hdom hpt ev122
          rcases h012 with h1 | h2
          · exact absurd (Value.field.inj h1).symm one_ne_zero
          · have hv := congrArg ZMod.val (Value.field.inj h2)
            rw [ZMod.val_zero, show (2 : F) = ((2 : Nat) : F) from rfl,
              ZMod.val_natCast_of_lt (by decide)] at hv
            exact absurd hv (by decide)
      obtain ⟨hm180_eq, hmenF⟩ := hsg
      rw [hm180_eq] at ev_iz
      have hv213 : ∃ f213 : F, v213 = .field f213 := by
        cases op227; exact ⟨_, rfl⟩
      obtain ⟨f213, rfl⟩ := hv213
      obtain ⟨_, hm202_eq⟩ := Lib.is_zero_spec ev_iz
      rw [hm202_eq, evalBinOp_add_one i op312] at ev_rec
      have htl := natT_rec_idx_spine hT hκ_inj hnPF_lt hsR hsE hnp_dom hag_dom rem (i + 1)
        (by omega) hRaw hpt ev_rec
      rw [recIdxFrom_lt hi_lt, hmenF]
      exact htl
    | .other_other (m38 := m38) (v179 := v179) (m180 := m180) (v199 := v199) (m202 := m202)
        (v213 := v213)
        (ev50 := ev_dom) (sg187 := sg) (op227 := op227) (ev212 := ev_iz) (heq235 := heq235)
        (op312 := op312) (ev249 := ev_rec) (hne332 := hne332) .. =>
      obtain ⟨hm38, hdom⟩ := nat_field_dom_rawTm_spec hi_lt (by omega) hRaw hsR hsE ev_dom
      rw [hm38] at sg
      have hv179_f : ∃ f179 : F, v179 = .field f179 ∧ v213 = .field (f179 - 3) := by
        cases v179 <;> simp [evalBinOp] at op227
        exact ⟨_, rfl, op227.symm⟩
      obtain ⟨f179, rfl, rfl⟩ := hv179_f
      obtain ⟨hv199, hm202_eq⟩ := Lib.is_zero_spec ev_iz
      have hne3 : (.field f179 : SourceValue F) ≠ .field 3 := by
        intro h3
        injection h3 with hf3
        subst hf3
        simp only [sub_self, ↓reduceIte] at hv199
        rw [heq235] at hv199
        exact absurd (Value.field.inj hv199.symm) one_ne_zero
      have hsg : Heap.Extends h m180 ∧
          (ecbs.getD (nP + i) default).1.mentionsConst T = true ∧
          RawRecSpine T (rcbs.getD (nP + i) default).1 (ecbs.getD (nP + i) default).1 := by
        cases sg with
        | n0 _ _ _ hv0 _ _ =>
          exact absurd hv0 hne332
        | other v75 m76 cs87 cs120 ev89 _ ev122 _ =>
          obtain ⟨_, hm76_eq⟩ :=
            nat_mentions_ret_bit cs87.length (Nat.le_refl _) hdom.toTm hpt ev89
          rw [hm76_eq] at ev122
          obtain ⟨_, hmenT⟩ :=
            nat_positivity_ok_spec hT cs120.length (Nat.le_refl _) hne3 hdom hpt ev122
          exact ⟨ev122.heap_extends, hmenT,
            natT_positivity_spine hT cs120.length (Nat.le_refl _) hne3 hdom (hag_dom i hi_lt)
              hpt ev122⟩
      rcases hsg with ⟨ext_180, hmenT, hspine⟩
      rw [hm202_eq, evalBinOp_add_one i op312] at ev_rec
      have htl := natT_rec_idx_spine hT hκ_inj hnPF_lt hsR hsE hnp_dom hag_dom rem (i + 1)
        (by omega) (hRaw.mono ext_180) (Bytes.repAddressRef_heapMono₂ addrTy ext_180 hpt) ev_rec
      rw [recIdxFrom_lt hi_lt, hmenT]
      simp only [↓reduceIte]
      intro idx hidx
      rcases List.mem_cons.mp hidx with rfl | hmem_tl
      · exact hspine
      · exact htl idx hmem_tl

/-! ## `nat_ctor` -/

/-- `KernelCheck::nat_ctor` at member `idx` on the stored constructor type: it instantiates the
type's universe parameters to the recursor's frame `rlps`, verifies that its return spine
mentions `T` nowhere in its indices, and computes its recursive field indices `recIdx` along
with `structUsedLater = false` on each. The run also fixes a raw reading `R` of the instantiated
type: its first `nP + nF` binders are literal, every recursive field domain is a `RawRecSpine`,
and under `NatCtorRetHeadT` its return position is an application spine over `T`. -/
theorem natT_ctor_spec {κ : _root_.Address → KKey}
    {T : KKey} {b₀ bT : Bytes.Address} {idx k nP nIdx num_ctors j : Nat} {large : Bool}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    {info : KKey × Nat × KExpr × KExpr × List Nat}
    {x_block x_t x_lps r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hT : κ (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, κ (ixAddr a) = T → a = bT)
    (hnP_lt : nP < 72057594037927936)
    (hj : j < ctors_info.length)
    (hinfo : ctors_info[j]? = some info)
    (hwf : NatCtorInfoWfT T k large nP nIdx num_ctors info)
    (hload : NatCtorLoadT κ b₀ idx k ctors_info x_block cs)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hb₀ : Bytes.RepAddressRef addrTy h b₀ x_block)
    (hbT : Bytes.RepAddressRef addrTy h bT x_t)
    (hlps : RepKLevelList h
      ((List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))) x_lps)
    (ev : ObsFn W "KernelCheck::nat_ctor"
      [x_block, .field (idx : F), .field (j : F), x_t, x_lps, .field (nP : F), .field (nIdx : F),
        .field ((if large then 1 else 0 : Nat) : F)]
      h r h' cs) :
    let rlps := if large then k :: List.range k else List.range k
    ∃ x_cty x_rec_idx R rcbs rbody,
      r = .tuple [x_cty, .field (info.2.1 : F), x_rec_idx] ∧
      RawTm κ 0 (fun _ => default) h' 0 R (posOf rlps info.2.2.2.1) x_cty ∧
      R.stripPis (nP + info.2.1) = some (rcbs, rbody) ∧
      (NatCtorRetHeadT b₀ idx nP ctors_info x_block cs →
        ∃ rus rargs, rbody = Expr.mkAppN (.const T rus) rargs) ∧
      (∀ ecbs ebody,
        (posOf rlps info.2.2.2.1).stripPis (nP + info.2.1) = some (ecbs, ebody) →
        ∀ i ∈ info.2.2.2.2,
          RawRecSpine T (rcbs.getD (nP + i) default).1 (ecbs.getD (nP + i) default).1) ∧
      RepList fieldListEnum (fun _ (i : Nat) v => v = .field (i : F)) h'
        info.2.2.2.2 x_rec_idx ∧
      (∀ i ∈ info.2.2.2.2, Ix.Kernel.structUsedLater info.2.2.2.1 nP i = false) ∧
      info.2.1 < 72057594037927936 := by
  intro rlps
  dsimp only [rlps]
  rcases Obs.«KernelCheck::nat_ctor».obs ev with
    ⟨m2, p9, cs15, w45, x_cty0, w46, w47, w48, w49, x_nf, w50,
      v136, m137, cs139, m146, cs156, v159, m161, cs169, v173, w200, x_rargs,
      v222, m225, cs233, v236, m239, cs247, v284, m301, cs309,
      ev17, ld11, sg144, op194, ev171, ev158, ev249, ev235, heq279, htup_out, ev311, hm_out, hc⟩
  subst hc htup_out hm_out
  obtain ⟨_, hnf_eq, hnf_lt, hTm0⟩ :=
    hload j hj p9 h m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50
      (fun x hx => by simp [hx]) hb₀ ev17 ld11 info hinfo
  subst hnf_eq
  have hnPF_lt : nP + info.2.1 < 18446744069414584321 := by omega
  -- Step 1: a raw reading of the loaded type, through `Seg1`
  obtain ⟨R0, hRaw0, hag0⟩ := natT_tm_raw hTm0
  have hRaw_rlps : ∃ R, RawTm κ 0 (fun _ => default) m137 0 R
        (posOf (if large then k :: List.range k else List.range k) info.2.2.2.1) v136 ∧
      NatMetaAgree R
        (posOf (if large then k :: List.range k else List.range k) info.2.2.2.1) ∧
      ((∃ rbs c us ras,
          R0.stripPis (nP + info.2.1) = some (rbs, Expr.mkAppN (.const c us) ras)) →
        ∃ rbs c us ras,
          R.stripPis (nP + info.2.1) = some (rbs, Expr.mkAppN (.const c us) ras)) ∧
      Heap.Extends m2 m137 := by
    cases sg144 with
    | n0 hv104 hv136 hm137 _ =>
      subst hv136 hm137
      cases large with
      | false => exact ⟨R0, hRaw0, hag0, id, Heap.Extends.refl _⟩
      | true =>
        simp only [↓reduceIte] at hv104
        exact absurd (Value.field.inj hv104) one_ne_zero
    | other cs116 hne109 ev118 hc_sg =>
      subst hc_sg
      cases large with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hne109
        exact absurd rfl hne109
      | true =>
        simp only [↓reduceIte] at hlps ⊢
        have hbnd_inst : IxVM.Consistency.Bounded cs116 :=
          RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
        have hlps_m2 := RepKLevelList.mono hlps ev17.heap_extends
        have hlv_rep : LvListRep m2 ((List.range k).map (fun i => Level.param (1 + i))) x_lps :=
          ⟨_, hlps_m2, LvEqList.refl _⟩
        have hinst := expr_inst_levels_rawTm hbnd_inst hRaw0 hlv_rep ev118
        have hag_inst := NatMetaAgree.ilp
          (List.range ((List.range k).map (fun i => Level.param (1 + i))).length)
          ((List.range k).map (fun i => Level.param (1 + i))) hag0
        simp only [List.length_map, List.length_range] at hinst hag_inst
        rw [posOf_range, ← posOf_large_eq_inst_shifted k hwf.lps_C] at hinst hag_inst
        refine ⟨_, hinst, hag_inst, ?_, ev118.heap_extends⟩
        rintro ⟨rbs, c, us, ras, hs⟩
        have hs' := ilp_stripPis (List.range k)
          ((List.range k).map (fun i => Level.param (1 + i))) (nP + info.2.1) hs
        rw [ilp_mkAppN] at hs'
        simp only [Expr.instantiateLevelParams] at hs'
        exact ⟨_, c, _, _, hs'⟩
  rcases hRaw_rlps with ⟨R, hRaw137, hag137, hhead137, ext_2_137⟩
  have ext_h_137 := ev17.heap_extends.trans ext_2_137
  -- Step 2: `peel_n_foralls`, `collect_spine`, `drop`, `nat_none_mention`
  rw [evalBinOp_add_nat nP info.2.1 op194] at ev171
  obtain ⟨hm161_eq, rcbs, ecbs, rbody, ebody, hsR, hsE, hmid⟩ :=
    peel_n_foralls_rawTm_bounded (nP + info.2.1) (by omega) hRaw137 ev171
  rw [hm161_eq] at ev158
  obtain ⟨hd_sp, sp_sp, Rh, Eh, Ras, Eas, htup_sp, hH, hEas, _, hR_sp, hE_sp, hnot_app⟩ :=
    collect_spine_rawTm_spec hmid ev158
  injection htup_sp with hsp_list
  injection hsp_list with _ hsp_tl
  injection hsp_tl with hsp_eq _
  subst hsp_eq
  rw [Nat.zero_add] at hEas
  obtain ⟨_, hdrop, hm239_eq⟩ := kexpr_list_drop_spec' (by omega) ev249 hEas
  rw [hm239_eq, heq279] at ev235
  have ext_h_146 := ext_h_137.trans ev158.heap_extends
  have hbT_146 := Bytes.repAddressRef_heapMono₂ addrTy ext_h_146 hbT
  have hm225 := nat_none_mention_one_spec hdrop hbT_146 ev235
  rw [hm225] at ev311
  -- Step 3: `nat_rec_idx`
  have hnp_pos : noProjAt T
      (posOf (if large then k :: List.range k else List.range k) info.2.2.2.1) = true := by
    unfold posOf
    rw [noProjAt_ilp]
    exact hwf.noProj_C
  obtain ⟨hnp_doms, _⟩ := noProjAt_stripPis_binder (nP + info.2.1) hnp_pos hsE
  have hnp_dom_f : ∀ i < info.2.1, noProjAt T (ecbs.getD (nP + i) default).1 = true :=
    fun i hi => hnp_doms (nP + i) (by omega)
  obtain ⟨hag_doms, _⟩ := NatMetaAgree.stripPis (nP + info.2.1) hag137 hsR hsE
  have hag_dom_f : ∀ i < info.2.1,
      NatMetaAgree (rcbs.getD (nP + i) default).1 (ecbs.getD (nP + i) default).1 :=
    fun i hi => hag_doms (nP + i) (by omega)
  have hbnd_rec : IxVM.Consistency.Bounded cs309 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have ev311' : ObsFn W "KernelCheck::nat_rec_idx"
      [v136, x_t, x_lps, .field (nP : F), .field (nIdx : F), .field (info.2.1 : F),
        .field ((0 : Nat) : F)]
      m146 v284 h' cs309 := by
    simpa using ev311
  obtain ⟨hrep_idx, hunused_idx⟩ :=
    nat_rec_idx_spec hT hκ_inj hnPF_lt hsR hsE hnp_dom_f info.2.1 0 (by omega) hbnd_rec
      (hRaw137.mono ev158.heap_extends) hbT_146 ev311'
  have hspine_idx := natT_rec_idx_spine hT hκ_inj hnPF_lt hsR hsE hnp_dom_f hag_dom_f
    info.2.1 0 (by omega) (hRaw137.mono ev158.heap_extends) hbT_146 ev311'
  have hrec_eq := hwf.recIdx_eq _ _ hsE
  rw [← hrec_eq] at hrep_idx hunused_idx hspine_idx
  refine ⟨v136, v284, R, rcbs, rbody, rfl,
    (hRaw137.mono ev158.heap_extends).mono ev311'.heap_extends, hsR, ?_, ?_, hrep_idx, ?_,
    hnf_lt⟩
  · -- the return position, under the head shape at the load
    intro hHT
    have hH0 := hHT j hj p9 h m2 cs15 _ _ _ _ _ _ _ _
      (fun x hx => by simp [hx]) hb₀ ev17 ld11 info hinfo
    obtain ⟨rbs', c, us, ras, hsR'⟩ := hhead137 (natT_rawTm_retHead _ hH0 hRaw0)
    rw [hsR] at hsR'
    injection hsR' with hp
    have hRb : rbody = Expr.mkAppN (.const c us) ras := (Prod.mk.inj hp).2
    have hRh_fn : Rh = .const c us := by
      have hfn := congrArg Expr.getAppFn (hR_sp.symm.trans hRb)
      rw [nat_getAppFn_mkAppN, nat_getAppFn_mkAppN] at hfn
      cases Rh with
      | app f a => exact (hnot_app f a rfl).elim
      | bvar _ | fvar _ _ | sort _ | const _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _ _
      | lit _ | proj _ _ _ => exact hfn
    rw [hRh_fn] at hH
    have hEh : Eh = .const c us := hH.const_left_inv
    obtain ⟨ecbs₀, eus₀, eargs₀, hsC₀⟩ := hwf.strip_C
    have hsE₀ := ilp_stripPis (if large then k :: List.range k else List.range k)
      (posLevels (if large then k :: List.range k else List.range k)) (nP + info.2.1) hsC₀
    change (posOf (if large then k :: List.range k else List.range k) info.2.2.2.1).stripPis
      (nP + info.2.1) = _ at hsE₀
    rw [hsE] at hsE₀
    injection hsE₀ with hpE
    have hEb := (Prod.mk.inj hpE).2
    rw [ilp_mkAppN, hE_sp, hEh] at hEb
    simp only [Expr.instantiateLevelParams] at hEb
    obtain ⟨hcT, _, _⟩ := mkAppN_const_inj hEb
    rw [hcT] at hRb
    exact ⟨us, ras, hRb⟩
  · -- the recursive field domains
    intro ecbs' ebody' hsE' i hi
    rw [hsE] at hsE'
    injection hsE' with hp
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    exact hspine_idx i hi
  · -- no later binder mentions a recursive field
    intro i hi
    have hi_lt : i < info.2.1 := hwf.recIdx_lt i hi
    obtain ⟨ebs₁, emid, hsE₁, hbvarF⟩ := hunused_idx i hi
    obtain ⟨ecbs₀, eus₀, eargs₀, hsC₀⟩ := hwf.strip_C
    have hsplit : nP + info.2.1 = (nP + i + 1) + (info.2.1 - 1 - i) := by omega
    have hsC₀' : info.2.2.2.1.stripPis ((nP + i + 1) + (info.2.1 - 1 - i)) =
        some (ecbs₀, Expr.mkAppN (.const T eus₀) eargs₀) := by
      rwa [← hsplit]
    obtain ⟨cbs₁, cbody₁, _, hsC₁, _, _, _⟩ :=
      stripPis_split (nP + i + 1) (info.2.1 - 1 - i) hsC₀'
    exact structUsedLater_false_of_posOf_stripPis hsC₁ hsE₁ hbvarF

/-- What the minor-premise and induction-hypothesis generators read of constructor `info`, from
its well-formedness and the recursive field domains its `nat_ctor` run reads. -/
theorem natT_ctor_inputs {T : KKey} {k nP nIdx num_ctors : Nat} {large : Bool}
    {info : KKey × Nat × KExpr × KExpr × List Nat} {rcbs : List (KExpr × Ix.Kernel.BinderMeta)}
    (hwf : NatCtorInfoWfT T k large nP nIdx num_ctors info)
    (hspine : ∀ ecbs ebody,
      (posOf (if large then k :: List.range k else List.range k) info.2.2.2.1).stripPis
        (nP + info.2.1) = some (ecbs, ebody) →
      ∀ i ∈ info.2.2.2.2,
        RawRecSpine T (rcbs.getD (nP + i) default).1 (ecbs.getD (nP + i) default).1) :
    ∃ ecbs eus eargs,
      (posOf (if large then k :: List.range k else List.range k) info.2.2.2.1).stripPis
        (nP + info.2.1) = some (ecbs, Expr.mkAppN (.const T eus) eargs) ∧
      ∀ i ∈ info.2.2.2.2, i < info.2.1 ∧
        RawRecSpine T (rcbs.getD (nP + i) default).1 (ecbs.getD (nP + i) default).1 := by
  obtain ⟨ecbs₀, eus₀, eargs₀, hsC₀⟩ := hwf.strip_C
  have hlt_all : ∀ i ∈ info.2.2.2.2, i < info.2.1 := hwf.recIdx_lt
  revert hspine
  generalize (if large then k :: List.range k else List.range k) = rlps
  intro hspine
  have hsE : (posOf rlps info.2.2.2.1).stripPis (nP + info.2.1) =
      some (ecbs₀.map (fun b => (posOf rlps b.1,
        { b.2 with pw := Level.substPW rlps (posLevels rlps) b.2.pw })),
        Expr.mkAppN (.const T (eus₀.map (Level.subst rlps (posLevels rlps))))
          (eargs₀.map (posOf rlps))) := by
    have hs := ilp_stripPis rlps (posLevels rlps) (nP + info.2.1) hsC₀
    unfold posOf at hs ⊢
    rwa [ilp_mkAppN, Expr.instantiateLevelParams] at hs
  exact ⟨_, _, _, hsE, fun i hi => ⟨hlt_all i hi, hspine _ _ hsE i hi⟩⟩

/-! ## `nat_minors`, `nat_rule_rhs`, `nat_check_rules` -/

/-- `KernelCheck::nat_minors` at member `idx` builds `cMinorsPis` (when `isLam = false`) or
`cMinorsLams` (when `isLam = true`) from constructor index `j` (`o = j + 1`) upward, on the
stored constructor types, when every loaded type's return position is a literal application
spine over a constant (`NatCtorRetHeadT`). -/
theorem natT_minors_spec {c : Ctx} {κ : _root_.Address → KKey}
    {T : KKey} {b₀ bT : Bytes.Address} {idx k nP nIdx : Nat} {large isLam : Bool} {ℓ : KLevel}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    (hT : κ (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, κ (ixAddr a) = T → a = bT)
    (hidx : idx < 72057594037927936)
    (hCres : ∀ i, i < ctors_info.length → κ (cprjAddr (ixAddr b₀) idx i) ≠ unresolvedKey)
    (hnCtors_lt : ctors_info.length < 72057594037927936)
    (hnP_lt : nP < 72057594037927936)
    (hwf_all : ∀ info ∈ ctors_info,
      NatCtorInfoWfT T k large nP nIdx ctors_info.length info) :
    ∀ (rem j : Nat) {body : KExpr}
      {x_block x_t x_lps x_pw x_body r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      j + rem = ctors_info.length →
      NatCtorLoadT κ b₀ idx k ctors_info x_block cs →
      NatCtorRetHeadT b₀ idx nP ctors_info x_block cs →
      Good c cs →
      IxVM.Consistency.Bounded cs →
      Bytes.RepAddressRef addrTy h b₀ x_block →
      Bytes.RepAddressRef addrTy h bT x_t →
      RepKLevelList h
        ((List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))) x_lps →
      RepKLevel h ℓ x_pw →
      Tm κ 0 (fun _ => default) h (nP + 1 + ctors_info.length) body x_body →
      ObsFn W "KernelCheck::nat_minors"
        [x_block, .field (idx : F), x_t, x_lps, .field (nP : F), .field (nIdx : F), x_pw,
          .field (ctors_info.length : F),
          .field ((if large then 1 else 0 : Nat) : F),
          .field (j : F), x_body,
          .field ((if isLam then 1 else 0 : Nat) : F)]
        h r h' cs →
      let rlps := if large then k :: List.range k else List.range k
      let clvls := (List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))
      let cs_tail := (ctors_info.drop j).map
        (fun info => (info.1, info.2.1, posOf rlps info.2.2.2.1, info.2.2.2.2))
      ∃ out,
        (if isLam then cMinorsLams clvls nP ℓ.zeronessOf cs_tail (j + 1) body
         else cMinorsPis clvls nP ℓ.zeronessOf cs_tail (j + 1) body) = some out ∧
        Tm κ 0 (fun _ => default) h' (nP + j + 1) out r
  | 0, j, body, x_block, x_t, x_lps, x_pw, x_body, r, h, h', cs,
      hjr, _, _, _, _, _, _, _, _, hbody, ev => by
    have hj_eq : j = ctors_info.length := by omega
    subst hj_eq
    match Obs.«KernelCheck::nat_minors».obs ev with
    | .n0 (he25 := hr) (he26 := hh) .. =>
      subst hr hh
      refine ⟨body, ?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using hbody⟩
      cases isLam <;> simp [List.drop_length, cMinorsPis, cMinorsLams]
    | .other_n0 (op17 := op17) (hne28 := hne28) .. =>
      rw [evalBinOp_sub_nat (Nat.le_refl ctors_info.length) op17] at hne28
      simp only [Nat.sub_self, Nat.cast_zero] at hne28
      exact (hne28 rfl).elim
    | .other_other (op17 := op17) (hne28 := hne28) .. =>
      rw [evalBinOp_sub_nat (Nat.le_refl ctors_info.length) op17] at hne28
      simp only [Nat.sub_self, Nat.cast_zero] at hne28
      exact (hne28 rfl).elim
  | rem + 1, j, body, x_block, x_t, x_lps, x_pw, x_body, r, h, h', cs,
      hjr, hload, hhead, hgood, hbnd, hb₀, hbT, hlps, hpw, hbody, ev => by
    have hj_lt : j < ctors_info.length := by omega
    let info := ctors_info[j]'hj_lt
    have hinfo_get : ctors_info[j]? = some info := List.getElem?_eq_getElem hj_lt
    have hwf_j : NatCtorInfoWfT T k large nP nIdx ctors_info.length info :=
      hwf_all info (List.mem_of_getElem? hinfo_get)
    have hdrop_j : ctors_info.drop j = info :: ctors_info.drop (j + 1) := by
      rw [← List.cons_getElem_drop_succ (h := hj_lt)]
    have hrecLen : info.2.2.2.2.length ≤ info.2.1 := hwf_j.recIdx_length_le
    match Obs.«KernelCheck::nat_minors».obs ev with
    | .n0 (op17 := op17) .. =>
      have hsub := evalBinOp_sub_nat (by omega : j ≤ ctors_info.length) op17
      have hval := congrArg ZMod.val (Value.field.inj hsub.symm)
      have h1 : ZMod.val ((ctors_info.length - j : Nat) : F) = ctors_info.length - j :=
        ZMod.val_natCast_of_lt
          (by omega : ctors_info.length - j < 18446744069414584321)
      rw [h1, ZMod.val_zero] at hval
      omega
    | .other_n0 (m33 := m33) (cs43 := cs_ctor) (x_cty := x_cty) (x_nf := x_nf)
        (x_rec_idx := x_rec_idx) (v128 := v128) (m129 := m129) (cs139 := cs_mty)
        (v142 := v142) (v146 := v146) (m151 := m151) (cs159 := cs_proj)
        (v243 := v243) (m244 := m244) (cs254 := cs_rec) (v266 := v266)
        (ev45 := ev_ctor) (ev161 := ev_proj) (op220 := op220) (ev141 := ev_mty)
        (op345 := op345) (ev256 := ev_rec) (hv374 := hv_lam) (he379 := hr)
        (hm378 := hm_end) (hc407 := hc) .. =>
      subst hc hr hm_end
      have hisLam : isLam = false := by
        cases isLam with
        | false => rfl
        | true =>
          simp only [↓reduceIte] at hv_lam
          exact absurd (Value.field.inj hv_lam) one_ne_zero
      subst hisLam
      have hbnd_ctor : IxVM.Consistency.Bounded cs_ctor :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hload_ctor : NatCtorLoadT κ b₀ idx k ctors_info x_block cs_ctor :=
        hload.mono_calls (fun x hx => by simp [hx])
      have hhead_ctor : NatCtorRetHeadT b₀ idx nP ctors_info x_block cs_ctor :=
        hhead.mono_calls (fun x hx => by simp [hx])
      obtain ⟨x_cty', x_rec_idx', Rc, rcbs, rbody, htup_c, hRaw_c, hsRc, hheadc, hspinec,
          hrec_c, _, hnf_lt⟩ :=
        natT_ctor_spec hT hκ_inj hnP_lt hj_lt hinfo_get hwf_j hload_ctor hbnd_ctor hb₀ hbT hlps
          ev_ctor
      have hbase_lt : nP + (j + 1) + info.2.1 + info.2.2.2.2.length < 2305843009213693952 := by
        omega
      obtain ⟨rus, rargs, hrbody⟩ := hheadc hhead_ctor
      subst hrbody
      obtain ⟨ecbs, eus, eargs, hsE_pos, hall_inp⟩ := natT_ctor_inputs hwf_j hspinec
      injection htup_c with hl_c
      injection hl_c with h1 hl_c; injection hl_c with h2 hl_c; injection hl_c with h3
      subst h1 h2 h3
      have hC_key : info.1 = κ (cprjAddr (ixAddr b₀) idx j) := by
        rcases Obs.«KernelCheck::nat_ctor».obs ev_ctor with ⟨m2_c, p9_c, cs15_c,
          w45_c, x_cty0_c, w46_c, w47_c, w48_c, w49_c, x_nf_c, w50_c, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, ev17_c, ld11_c, _, _, _, _, _, _, _, _, _, _, hc_c⟩
        subst hc_c
        exact (hload_ctor j hj_lt p9_c h m2_c cs15_c w45_c x_cty0_c w46_c w47_c w48_c w49_c
          x_nf_c w50_c (fun x hx => by simp [hx]) hb₀ ev17_c ld11_c info hinfo_get).1
      have hb₀_33 := Bytes.repAddressRef_heapMono₂ addrTy ev_ctor.heap_extends hb₀
      have hgood_proj : Good c cs_proj :=
        hgood.sub (fun x hx => by simp [hx])
      obtain ⟨bC, hbC, hbC_addr⟩ := projection_addr_ctor_bounded (by omega) (by omega) hb₀_33
        hgood_proj ev_proj
      have hres_C : Resolved (κ (ixAddr bC)) := ⟨by rw [hbC_addr]; exact hCres j hj_lt⟩
      rw [evalBinOp_add_one j op220] at ev_mty
      have ext_h_151 := ev_ctor.heap_extends.trans ev_proj.heap_extends
      have hbnd_mty : IxVM.Consistency.Bounded cs_mty :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      obtain ⟨mty, hmty_eq, hmty_tm⟩ :=
        natI_minor_ty_spec (κ := κ) (Γ₀ := fun _ => default) (bC := bC) (hC_res := hres_C)
          (by rw [hbC_addr, ← hC_key])
          (by omega : 1 ≤ j + 1) hsRc hsE_pos
          hall_inp
          hbase_lt hbnd_mty hbC
          (RepKLevelList.mono hlps ext_h_151)
          (repKLevel_heapMono₂ ext_h_151 hpw)
          (hRaw_c.mono ev_proj.heap_extends)
          (fieldRepList_mono ev_proj.heap_extends hrec_c) ev_mty
      rw [evalBinOp_add_one j op345] at ev_rec
      have ext_h_129 := ext_h_151.trans ev_mty.heap_extends
      have hbnd_rec : IxVM.Consistency.Bounded cs_rec :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hgood_rec : Good c cs_rec :=
        hgood.sub (fun x hx => by simp [hx])
      have hload_rec : NatCtorLoadT κ b₀ idx k ctors_info x_block cs_rec :=
        hload.mono_calls (fun x hx => by simp [hx])
      have hhead_rec : NatCtorRetHeadT b₀ idx nP ctors_info x_block cs_rec :=
        hhead.mono_calls (fun x hx => by simp [hx])
      obtain ⟨rest_out, hrest_eq, hrest_tm⟩ :=
        natT_minors_spec hT hκ_inj hidx hCres hnCtors_lt hnP_lt hwf_all rem (j + 1) (by omega)
          hload_rec hhead_rec hgood_rec hbnd_rec
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_129 hb₀)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_129 hbT)
          (RepKLevelList.mono hlps ext_h_129)
          (repKLevel_heapMono₂ ext_h_129 hpw)
          (hbody.mono ext_h_129) ev_rec
      simp only [Bool.false_eq_true, ↓reduceIte] at hrest_eq ⊢
      have ext_end : Heap.Extends m244
          (m244 ++ [.construct kexprEnum "Forall" [v128, v243, x_pw]]) :=
        Heap.Extends.snoc _ _
      refine ⟨.forallE mty rest_out { pw := ℓ.zeronessOf }, ?_, ?_⟩
      · rw [hdrop_j, List.map_cons, cMinorsPis, hmty_eq]
        dsimp only [Option.bind]
        rw [hrest_eq, Option.map_some]
      · have hmty_end : Tm κ 0 (fun _ => default)
            (m244 ++ [.construct kexprEnum "Forall" [v128, v243, x_pw]])
            (nP + j + 1) mty v128 := by
          rw [show nP + j + 1 = nP + (j + 1) by omega]
          exact (hmty_tm.mono ev_rec.heap_extends).mono ext_end
        have hrest_end : Tm κ 0 (fun _ => default)
            (m244 ++ [.construct kexprEnum "Forall" [v128, v243, x_pw]])
            ((nP + j + 1) + 1) rest_out v243 := by
          rw [show (nP + j + 1) + 1 = nP + (j + 1) + 1 by omega]
          exact hrest_tm.mono ext_end
        exact .forallE (by simp) hmty_end hrest_end
          (repKLevel_heapMono₂ (ext_h_129.trans (ev_rec.heap_extends.trans ext_end)) hpw)
    | .other_other (m33 := m33) (cs43 := cs_ctor) (x_cty := x_cty) (x_nf := x_nf)
        (x_rec_idx := x_rec_idx) (v128 := v128) (m129 := m129) (cs139 := cs_mty)
        (v142 := v142) (v146 := v146) (m151 := m151) (cs159 := cs_proj)
        (v243 := v243) (m244 := m244) (cs254 := cs_rec) (v266 := v266)
        (ev45 := ev_ctor) (ev161 := ev_proj) (op220 := op220) (ev141 := ev_mty)
        (op345 := op345) (ev256 := ev_rec) (hne408 := hne_lam) (he416 := hr)
        (hm415 := hm_end) (hc444 := hc) .. =>
      subst hc hr hm_end
      have hisLam : isLam = true := by
        cases isLam with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hne_lam
          exact absurd rfl hne_lam
        | true => rfl
      subst hisLam
      have hbnd_ctor : IxVM.Consistency.Bounded cs_ctor :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hload_ctor : NatCtorLoadT κ b₀ idx k ctors_info x_block cs_ctor :=
        hload.mono_calls (fun x hx => by simp [hx])
      have hhead_ctor : NatCtorRetHeadT b₀ idx nP ctors_info x_block cs_ctor :=
        hhead.mono_calls (fun x hx => by simp [hx])
      obtain ⟨x_cty', x_rec_idx', Rc, rcbs, rbody, htup_c, hRaw_c, hsRc, hheadc, hspinec,
          hrec_c, _, hnf_lt⟩ :=
        natT_ctor_spec hT hκ_inj hnP_lt hj_lt hinfo_get hwf_j hload_ctor hbnd_ctor hb₀ hbT hlps
          ev_ctor
      have hbase_lt : nP + (j + 1) + info.2.1 + info.2.2.2.2.length < 2305843009213693952 := by
        omega
      obtain ⟨rus, rargs, hrbody⟩ := hheadc hhead_ctor
      subst hrbody
      obtain ⟨ecbs, eus, eargs, hsE_pos, hall_inp⟩ := natT_ctor_inputs hwf_j hspinec
      injection htup_c with hl_c
      injection hl_c with h1 hl_c; injection hl_c with h2 hl_c; injection hl_c with h3
      subst h1 h2 h3
      have hC_key : info.1 = κ (cprjAddr (ixAddr b₀) idx j) := by
        rcases Obs.«KernelCheck::nat_ctor».obs ev_ctor with ⟨m2_c, p9_c, cs15_c,
          w45_c, x_cty0_c, w46_c, w47_c, w48_c, w49_c, x_nf_c, w50_c, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, ev17_c, ld11_c, _, _, _, _, _, _, _, _, _, _, hc_c⟩
        subst hc_c
        exact (hload_ctor j hj_lt p9_c h m2_c cs15_c w45_c x_cty0_c w46_c w47_c w48_c w49_c
          x_nf_c w50_c (fun x hx => by simp [hx]) hb₀ ev17_c ld11_c info hinfo_get).1
      have hb₀_33 := Bytes.repAddressRef_heapMono₂ addrTy ev_ctor.heap_extends hb₀
      have hgood_proj : Good c cs_proj :=
        hgood.sub (fun x hx => by simp [hx])
      obtain ⟨bC, hbC, hbC_addr⟩ := projection_addr_ctor_bounded (by omega) (by omega) hb₀_33
        hgood_proj ev_proj
      have hres_C : Resolved (κ (ixAddr bC)) := ⟨by rw [hbC_addr]; exact hCres j hj_lt⟩
      rw [evalBinOp_add_one j op220] at ev_mty
      have ext_h_151 := ev_ctor.heap_extends.trans ev_proj.heap_extends
      have hbnd_mty : IxVM.Consistency.Bounded cs_mty :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      obtain ⟨mty, hmty_eq, hmty_tm⟩ :=
        natI_minor_ty_spec (κ := κ) (Γ₀ := fun _ => default) (bC := bC) (hC_res := hres_C)
          (by rw [hbC_addr, ← hC_key])
          (by omega : 1 ≤ j + 1) hsRc hsE_pos
          hall_inp
          hbase_lt hbnd_mty hbC
          (RepKLevelList.mono hlps ext_h_151)
          (repKLevel_heapMono₂ ext_h_151 hpw)
          (hRaw_c.mono ev_proj.heap_extends)
          (fieldRepList_mono ev_proj.heap_extends hrec_c) ev_mty
      rw [evalBinOp_add_one j op345] at ev_rec
      have ext_h_129 := ext_h_151.trans ev_mty.heap_extends
      have hbnd_rec : IxVM.Consistency.Bounded cs_rec :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hgood_rec : Good c cs_rec :=
        hgood.sub (fun x hx => by simp [hx])
      have hload_rec : NatCtorLoadT κ b₀ idx k ctors_info x_block cs_rec :=
        hload.mono_calls (fun x hx => by simp [hx])
      have hhead_rec : NatCtorRetHeadT b₀ idx nP ctors_info x_block cs_rec :=
        hhead.mono_calls (fun x hx => by simp [hx])
      obtain ⟨rest_out, hrest_eq, hrest_tm⟩ :=
        natT_minors_spec hT hκ_inj hidx hCres hnCtors_lt hnP_lt hwf_all rem (j + 1) (by omega)
          hload_rec hhead_rec hgood_rec hbnd_rec
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_129 hb₀)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_129 hbT)
          (RepKLevelList.mono hlps ext_h_129)
          (repKLevel_heapMono₂ ext_h_129 hpw)
          (hbody.mono ext_h_129) ev_rec
      simp only [↓reduceIte] at hrest_eq ⊢
      have ext_end : Heap.Extends m244
          (m244 ++ [.construct kexprEnum "Lam" [v128, v243, x_pw]]) :=
        Heap.Extends.snoc _ _
      refine ⟨.lam mty rest_out { pw := ℓ.zeronessOf }, ?_, ?_⟩
      · rw [hdrop_j, List.map_cons, cMinorsLams, hmty_eq]
        dsimp only [Option.bind]
        rw [hrest_eq, Option.map_some]
      · have hmty_end : Tm κ 0 (fun _ => default)
            (m244 ++ [.construct kexprEnum "Lam" [v128, v243, x_pw]])
            (nP + j + 1) mty v128 := by
          rw [show nP + j + 1 = nP + (j + 1) by omega]
          exact (hmty_tm.mono ev_rec.heap_extends).mono ext_end
        have hrest_end : Tm κ 0 (fun _ => default)
            (m244 ++ [.construct kexprEnum "Lam" [v128, v243, x_pw]])
            ((nP + j + 1) + 1) rest_out v243 := by
          rw [show (nP + j + 1) + 1 = nP + (j + 1) + 1 by omega]
          exact hrest_tm.mono ext_end
        exact .lam (by simp) hmty_end hrest_end
          (repKLevel_heapMono₂ (ext_h_129.trans (ev_rec.heap_extends.trans ext_end)) hpw)

/-- `KernelCheck::nat_rule_rhs` at member `idx` builds the circuit-frame generated rule right-hand
side `cRuleRhs` for constructor `j`, on the stored constructor types, at a keying under which the
recursor's key and the member's constructor projections resolve, when every loaded type's return
position is a literal application spine over a constant (`NatCtorRetHeadT`). -/
theorem natT_rule_rhs_spec {c : Ctx} {κ : _root_.Address → KKey}
    {T recC : KKey} {b₀ bT bRec : Bytes.Address} {idx k nP nIdx j : Nat} {large : Bool}
    {ℓ : KLevel} {rlvls_c : List KLevel} {tty₀ motiveTy : KExpr}
    {tbsP : List (KExpr × Ix.Kernel.BinderMeta)} {itele_pos : KExpr}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    {x_block x_t x_lps x_pw x_tty x_motive_ty x_rec x_rlvls r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    [Resolved (κ (ixAddr bRec))]
    (hT : κ (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, κ (ixAddr a) = T → a = bT)
    (hRec : κ (ixAddr bRec) = recC)
    (hidx : idx < 72057594037927936)
    (hCres : ∀ i, i < ctors_info.length → κ (cprjAddr (ixAddr b₀) idx i) ≠ unresolvedKey)
    (hnCtors_lt : ctors_info.length < 72057594037927936)
    (hnP_lt : nP < 72057594037927936)
    (hj : j < ctors_info.length)
    (hwf_all : ∀ info ∈ ctors_info,
      NatCtorInfoWfT T k large nP nIdx ctors_info.length info)
    (hsT_pos : (posOf (if large then k :: List.range k else List.range k) tty₀).stripPis nP =
      some (tbsP, itele_pos))
    (hmot_eq : cMotiveTyI T
      ((List.range k).map (fun i => Level.param ((if large then 1 else 0) + i)))
      ℓ nP nIdx itele_pos = some motiveTy)
    (hload : NatCtorLoadT κ b₀ idx k ctors_info x_block cs)
    (hhead : NatCtorRetHeadT b₀ idx nP ctors_info x_block cs)
    (hgood : Good c cs)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hb₀ : Bytes.RepAddressRef addrTy h b₀ x_block)
    (hbT : Bytes.RepAddressRef addrTy h bT x_t)
    (hbRec : Bytes.RepAddressRef addrTy h bRec x_rec)
    (hlps : RepKLevelList h
      ((List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))) x_lps)
    (hrlvls : RepKLevelList h rlvls_c x_rlvls)
    (hpw : RepKLevel h ℓ x_pw)
    (htty : Tm κ 0 (fun _ => default) h 0
      (posOf (if large then k :: List.range k else List.range k) tty₀) x_tty)
    (hmotive : Tm κ 0 (fun _ => default) h nP motiveTy x_motive_ty)
    (ev : ObsFn W "KernelCheck::nat_rule_rhs"
      [x_block, .field (idx : F), x_t, x_lps, .field (nP : F), .field (nIdx : F), x_pw,
        .field (ctors_info.length : F),
        .field ((if large then 1 else 0 : Nat) : F),
        x_tty, x_motive_ty, x_rec, x_rlvls, .field (j : F)]
      h r h' cs) :
    let rlps := if large then k :: List.range k else List.range k
    let clvls := (List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))
    let cs_pos := ctors_info.map (fun info => (info.1, info.2.1, posOf rlps info.2.2.2.1, info.2.2.2.2))
    ∃ rhs_c,
      cRuleRhs T clvls ℓ nP nIdx (posOf rlps tty₀) cs_pos recC rlvls_c j = some rhs_c ∧
      Tm κ 0 (fun _ => default) h' 0 rhs_c r := by
  intro rlps clvls cs_pos
  dsimp only [rlps, clvls, cs_pos]
  let n := ctors_info.length
  let info := ctors_info[j]'hj
  have hinfo_get : ctors_info[j]? = some info := List.getElem?_eq_getElem hj
  have hwf_j : NatCtorInfoWfT T k large nP nIdx n info :=
    hwf_all info (List.mem_of_getElem? hinfo_get)
  let nF := info.2.1
  let C₀ := info.2.2.2.1
  let recIdx := info.2.2.2.2
  rcases Obs.«KernelCheck::nat_rule_rhs».obs ev with
    ⟨m2, cs12, x_cty, x_nf, x_rec_idx, v97, m98, cs108, v112, m114, v126, x133, x141,
      m161, cs169, v172, v173, m175, cs183, m202, cs210, v277, m278, cs288, v293, m311,
      cs319, v322, v323, m326, cs334, v387, m388, cs398, cs498, m528,
      ev14, hm122, op156, op148, op140, ev185, ev212, ev171, ev110, ev336, op366, ev321,
      ev290, ev400, hm536, ev500, hc⟩
  subst hc
  -- Step 1: `nat_ctor`
  have hbnd_ctor : IxVM.Consistency.Bounded cs12 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hload_ctor : NatCtorLoadT κ b₀ idx k ctors_info x_block cs12 :=
    hload.mono_calls (fun x hx => by simp [hx])
  obtain ⟨x_cty', x_rec_idx', Rc, rcbs, rbody, htup_c, hRaw_c, hsRc, _, hspinec, hrec_c, _,
      hnf_lt⟩ :=
    natT_ctor_spec hT hκ_inj hnP_lt hj hinfo_get hwf_j hload_ctor hbnd_ctor hb₀ hbT hlps ev14
  have hbase_lt : nP + 1 + n + nF < 2305843009213693952 := by
    dsimp only [n, nF]
    omega
  obtain ⟨ecbs, eus, eargs, hsE_pos, hall_inp⟩ := natT_ctor_inputs hwf_j hspinec
  injection htup_c with hl_c
  injection hl_c with h1 hl_c; injection hl_c with h2 hl_c; injection hl_c with h3
  subst h1 h2 h3
  -- Step 2: `structRuleBodyR` via `BVar`, `nat_ps_at`, `nat_ih_apps`, `concat`, `nat_app_n`
  rw [evalBinOp_add_nat nF n op156] at op148
  rw [evalBinOp_sub_nat (by omega : 1 ≤ nF + n) op148] at op140
  rw [evalBinOp_sub_nat (by omega : j ≤ nF + n - 1) op140] at hm122
  have ext_2_114 : Heap.Extends m2 m114 := by rw [hm122]; exact Heap.Extends.snoc _ _
  have hbvar_min : Tm κ 0 (fun _ => default) m114 (nP + 1 + n + nF)
      (.bvar (nF + n - 1 - j)) (.ptr (.enum kexprEnum) m2.length) := by
    rw [hm122]
    exact tm_bvarLocal_nat_bounded (by simp) (by omega) (by omega)
  have hps_f := nat_ps_at_bounded (κ := κ) (d := 0) (Γ := fun _ => default)
    nF 0 (nP + 1 + n + nF) (by omega) (by omega) ev185
  have hps_f' : RepList kexprListEnum
      (fun h E p => Tm κ 0 (fun _ => default) h (nP + 1 + n + nF) E p)
      m175 ((List.range nF).map fun i => Expr.bvar (nF - 1 - i)) v172 := by
    rw [structPsAt_zero_eq_structTeleVars] at hps_f
    exact hps_f
  let rlps' := if large then k :: List.range k else List.range k
  have hall_ih := hall_inp
  have ext_2_175 := ext_2_114.trans ev185.heap_extends
  have ext_h_175 := ev14.heap_extends.trans ext_2_175
  have hbnd_ih : IxVM.Consistency.Bounded cs210 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hih_apps := natI_ih_apps_spec hRec hsRc hsE_pos hall_ih hbase_lt hbnd_ih
    (Bytes.repAddressRef_heapMono₂ addrTy ext_h_175 hbRec)
    (RepKLevelList.mono hrlvls ext_h_175)
    (repKLevel_heapMono₂ ext_h_175 hpw)
    (fieldRepList_mono ext_2_175 hrec_c)
    (hRaw_c.mono ext_2_175) ev212
  have hcat := kexpr_list_concat_spec' ev171 (tmRepList_mono ev212.heap_extends hps_f') hih_apps
  have ext_114_161 := ev185.heap_extends.trans (ev212.heap_extends.trans ev171.heap_extends)
  have hbody := nat_app_n_spec (hbvar_min.mono ext_114_161) hcat ev110
  change Tm κ 0 (fun _ => default) m98 (nP + 1 + n + nF)
    (Ix.Kernel.structRuleBodyR recC rlvls_c ℓ.zeronessOf nP n nF j recIdx
      (Ix.Kernel.structFieldTeleOf (posOf rlps' C₀) nP nF)
      (Ix.Kernel.structFieldIdxOf (posOf rlps' C₀) nP nF)) v97 at hbody
  -- Step 3: `peel_n_foralls`, `expr_lift`, `nat_replace_pis` (fields -> `inner`)
  have ext_2_98 := ext_2_114.trans (ext_114_161.trans ev110.heap_extends)
  obtain ⟨hm326_eq, _, ecbsP, _, ecrest, _, hsCP_pos, hcrest_raw⟩ :=
    peel_n_foralls_rawTm_bounded nP (by omega) (hRaw_c.mono ext_2_98) ev336
  rw [hm326_eq, evalBinOp_add_one n op366] at ev321
  have hbnd_lift : IxVM.Consistency.Bounded cs319 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hcrest_tm : Tm κ 0 (fun _ => default) m98 nP ecrest v322 := by
    simpa [Nat.zero_add] using hcrest_raw.toTm
  have hcrest_lift := expr_lift_local_bounded (Nat.zero_le nP) (by omega) (by decide)
    hbnd_lift hcrest_tm ev321
  have hcrest_lift' : Tm κ 0 (fun _ => default) m311 (nP + 1 + n)
      (ecrest.liftLooseBVars (n + 1) 0) v293 := by
    rw [show nP + (n + 1) = nP + 1 + n by omega] at hcrest_lift
    exact hcrest_lift
  have ext_h_311 := ev14.heap_extends.trans (ext_2_98.trans ev321.heap_extends)
  obtain ⟨inner, hinner_ite, hinner_tm⟩ :=
    nat_replace_pis_bounded nF (by omega) (repKLevel_heapMono₂ ext_h_311 hpw)
      hcrest_lift' (hbody.mono ev321.heap_extends) ev290
  have h1_ne_0 : (.field 1 : SourceValue F) ≠ .field 0 := by
    intro h01; exact absurd (Value.field.inj h01) one_ne_zero
  rw [ite_eq_right h1_ne_0] at hinner_ite
  -- Step 4: `nat_minors` (`isLam = true`) and outer `Lam` + `nat_replace_pis`
  have ext_h_278 := ext_h_311.trans ev290.heap_extends
  have hload_min : NatCtorLoadT κ b₀ idx k ctors_info x_block cs398 :=
    hload.mono_calls (fun x hx => by simp [hx])
  have hhead_min : NatCtorRetHeadT b₀ idx nP ctors_info x_block cs398 :=
    hhead.mono_calls (fun x hx => by simp [hx])
  have hgood_min : Good c cs398 := hgood.sub (fun x hx => by simp [hx])
  have hbnd_min : IxVM.Consistency.Bounded cs398 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have ev400' : ObsFn W "KernelCheck::nat_minors"
      [x_block, .field (idx : F), x_t, x_lps, .field (nP : F), .field (nIdx : F), x_pw,
        .field (n : F), .field ((if large then 1 else 0 : Nat) : F),
        .field ((0 : Nat) : F), v277, .field ((if true then 1 else 0 : Nat) : F)]
      m278 v387 m388 cs398 := by
    simpa using ev400
  obtain ⟨minors, hmin_eq, hmin_tm⟩ :=
    natT_minors_spec hT hκ_inj hidx hCres (by omega) hnP_lt hwf_all n 0 (by omega)
      hload_min hhead_min hgood_min hbnd_min
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_278 hb₀)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_278 hbT)
      (RepKLevelList.mono hlps ext_h_278)
      (repKLevel_heapMono₂ ext_h_278 hpw)
      hinner_tm ev400'
  simp only [↓reduceIte, List.drop_zero, Nat.add_zero] at hmin_eq hmin_tm
  have ext_388_528 : Heap.Extends m388 m528 := by rw [hm536]; exact Heap.Extends.snoc _ _
  have ext_h_528 := ext_h_278.trans (ev400.heap_extends.trans ext_388_528)
  have hlam_mot : Tm κ 0 (fun _ => default) m528 (0 + nP)
      (.lam motiveTy minors { pw := ℓ.zeronessOf }) (.ptr (.enum kexprEnum) m388.length) := by
    rw [Nat.zero_add]
    exact .lam (by rw [hm536]; simp)
      (hmotive.mono ext_h_528)
      (hmin_tm.mono ext_388_528)
      (repKLevel_heapMono₂ ext_h_528 hpw)
  obtain ⟨rhs_c, hrhs_ite, hrhs_tm⟩ :=
    nat_replace_pis_bounded nP (by omega) (repKLevel_heapMono₂ ext_h_528 hpw)
      (htty.mono ext_h_528) hlam_mot ev500
  rw [ite_eq_right h1_ne_0] at hrhs_ite
  refine ⟨rhs_c, ?_, hrhs_tm⟩
  unfold cRuleRhs
  dsimp only
  have hcj_pos :
      (ctors_info.map fun info => (info.1, info.2.1, posOf rlps' info.2.2.2.1, info.2.2.2.2))[j]? =
        some (info.1, nF, posOf rlps' C₀, recIdx) := by
    simp [List.getElem?_map, hinfo_get, nF, C₀, recIdx]
  rw [hcj_pos]
  dsimp only [Option.bind]
  rw [hsT_pos]
  dsimp only [Option.bind]
  rw [hmot_eq]
  dsimp only [Option.bind]
  rw [hsCP_pos]
  dsimp only [Option.bind]
  simp only [List.length_map]
  change Expr.pisToLamsPw ℓ.zeronessOf nF (ecrest.liftLooseBVars (n + 1) 0) _ = some inner
    at hinner_ite
  rw [hinner_ite]
  dsimp only [Option.bind]
  rw [hmin_eq]
  dsimp only [Option.bind]
  exact hrhs_ite

/-- `KernelCheck::nat_check_rules` at member `idx` verifies each rule's field count `nF` and
establishes `WrapRelSem find?` between the generated rule right-hand side `structRecRhsR` and the
declared one, under `WrapLoads` at the keying `κ`, on the stored constructor types, when every
loaded type's return position is a literal application spine over a constant
(`NatCtorRetHeadT`). -/
theorem natT_check_rules_spec {c : Ctx} {κ : _root_.Address → KKey}
    {find? : KKey → Option (ConstantInfo .anon)}
    {T recC : KKey} {b₀ bT bRec : Bytes.Address} {idx k nP nIdx : Nat}
    {large : Bool} {tty₀ motiveTy : KExpr}
    {tbs₀ : List (KExpr × Ix.Kernel.BinderMeta)} {tsort₀ : KExpr}
    {tbsP : List (KExpr × Ix.Kernel.BinderMeta)} {itele_pos : KExpr}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    [Resolved (κ (ixAddr bRec))]
    (hlf : WrapLoads c κ find?)
    (hT : κ (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, κ (ixAddr a) = T → a = bT)
    (hRec : κ (ixAddr bRec) = recC)
    (hidx : idx < 72057594037927936)
    (hCres : ∀ i, i < ctors_info.length → κ (cprjAddr (ixAddr b₀) idx i) ≠ unresolvedKey)
    (hnCtors_lt : ctors_info.length < 72057594037927936)
    (hnP_lt : nP < 72057594037927936)
    (hwf_all : ∀ info ∈ ctors_info,
      NatCtorInfoWfT T k large nP nIdx ctors_info.length info)
    (hsT₀ : tty₀.stripPis (nP + nIdx) = some (tbs₀, tsort₀))
    (hsT_pos : (posOf (if large then k :: List.range k else List.range k) tty₀).stripPis nP =
      some (tbsP, itele_pos))
    (hmot_eq : cMotiveTyI T
      ((List.range k).map (fun i => Level.param ((if large then 1 else 0) + i)))
      (if large then Level.param 0 else Level.zero) nP nIdx itele_pos = some motiveTy) :
    ∀ {rls_tail : List (RecRule .anon)} (j : Nat)
      {x_rules x_block x_t x_lps x_pw x_tty x_motive_ty x_rec x_rlvls r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      j + rls_tail.length = ctors_info.length →
      RulesRep κ h (if large then k :: List.range k else List.range k) j x_rules rls_tail →
      NatCtorLoadT κ b₀ idx k ctors_info x_block cs →
      NatCtorRetHeadT b₀ idx nP ctors_info x_block cs →
      Good c cs →
      IxVM.Consistency.Bounded cs →
      Bytes.RepAddressRef addrTy h b₀ x_block →
      Bytes.RepAddressRef addrTy h bT x_t →
      Bytes.RepAddressRef addrTy h bRec x_rec →
      RepKLevelList h
        ((List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))) x_lps →
      RepKLevelList h
        ((List.range ((if large then k :: List.range k else List.range k).length)).map Level.param)
        x_rlvls →
      RepKLevel h (if large then Level.param 0 else Level.zero) x_pw →
      Tm κ 0 (fun _ => default) h 0
        (posOf (if large then k :: List.range k else List.range k) tty₀) x_tty →
      Tm κ 0 (fun _ => default) h nP motiveTy x_motive_ty →
      ObsFn W "KernelCheck::nat_check_rules"
        [x_rules, x_block, .field (idx : F), x_t, x_lps, .field (nP : F), .field (nIdx : F), x_pw,
          .field (ctors_info.length : F),
          .field ((if large then 1 else 0 : Nat) : F),
          x_tty, x_motive_ty, x_rec, x_rlvls, .field (j : F)]
        h r h' cs →
      let rlps := if large then k :: List.range k else List.range k
      let elim := if large then k else 0
      let ctors₀ := ctors_info.map (fun info => (info.1, info.2.1, info.2.2.2.1, info.2.2.2.2))
      ∀ i (hlt : i < rls_tail.length) (hj_i : j + i < ctors_info.length),
        (rls_tail[i]'hlt).nfields = (ctors_info[j + i]'hj_i).2.1 ∧
        ∃ rhsG,
          Ix.Kernel.structRecRhsR T (List.range k) elim large nP nIdx tty₀ ctors₀
            recC (rlps.map .param) (j + i) = some rhsG ∧
          WrapRelSem find? rhsG (rls_tail[i]'hlt).rhs := by
  intro rls_tail
  induction rls_tail with
  | nil =>
    intro j x_rules x_block x_t x_lps x_pw x_tty x_motive_ty x_rec x_rlvls r h h' cs
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i hlt
    exact absurd hlt (Nat.not_lt_zero _)
  | cons rl rls_rest ih =>
    intro j x_rules x_block x_t x_lps x_pw x_tty x_motive_ty x_rec x_rlvls r h h' cs
      hj_len hrules hload hhead hgood hbnd hb₀ hbT hbRec hlps hrlvls hpw htty hmotive ev
    have hj : j < ctors_info.length := by
      simp only [List.length_cons] at hj_len
      omega
    have hj_rest : (j + 1) + rls_rest.length = ctors_info.length := by
      simp only [List.length_cons] at hj_len
      omega
    match Obs.«KernelCheck::nat_check_rules».obs ev with
    | .Nil (ld12 := ld0) .. =>
      have ld0' : loadValue h x_rules = .ok (.construct krrListEnum "Nil" []) := ld0
      cases hrules with | cons cell _ _ => exact (load_cell_ne cell ld0' (by decide)).elim
    | .Cons (x_rest := x_rest) (x_cidx := x_cidx) (x_rnf := x_rnf) (x_rhs := x_rhs)
        (m98 := m98) (p105 := p105) (cs111 := cs_cprj)
        (w141 := w141) (w142 := w142) (w143 := w143) (w144 := w144)
        (w145 := w145) (w146 := w146) (x_c_nf := x_c_nf) (w147 := w147)
        (v227 := v227) (m230 := m230) (cs238 := cs_wrap)
        (v241 := v241) (m244 := m244) (cs252 := cs_rhs)
        (cs384 := cs_rec) (v401 := v401)
        (ld12 := ld0) (ev113 := ev_cprj) (ld107 := ld_ctor) (heq215 := heq_nf)
        (ev254 := ev_rhs) (ev240 := ev_wrap) (heq380 := heq_w1)
        (op513 := op_j1) (ev386 := ev_rec) (hc515 := hc) .. =>
      subst hc heq_w1
      cases hrules with
      | cons cell hr hrules_rest =>
        have ld0' : loadValue h _ = .ok (.construct krrListEnum "Cons"
            [.construct krrEnum "Mk" [x_cidx, x_rnf, x_rhs], x_rest]) := ld0
        obtain ⟨-, hxs⟩ := load_cell cell ld0'
        injection hxs with hmk hxs; injection hxs with hrest_eq; subst hrest_eq
        obtain ⟨rhs_p, hmk_eq, hrnf_lt, hrhs_tmC⟩ := hr
        rw [hmk] at hmk_eq
        injection hmk_eq with _ _ hmk_args
        injection hmk_args with _ hmk_args
        injection hmk_args with hrnf_eq hmk_args
        injection hmk_args with hrhs_eq
        subst hrnf_eq hrhs_eq
        -- Step 1: constructor `j` field count from `NatCtorLoadT`
        let info := ctors_info[j]'hj
        have hinfo_get : ctors_info[j]? = some info := List.getElem?_eq_getElem hj
        have hwf_j : NatCtorInfoWfT T k large nP nIdx ctors_info.length info :=
          hwf_all info (List.mem_of_getElem? hinfo_get)
        have ld_ctor' : loadValue m98 p105 = .ok (.construct kciEnum "Ctor"
            [w141, w142, w143, w144, w145, w146, x_c_nf, w147]) := ld_ctor
        obtain ⟨_, hcnf_eq, hcnf_lt, _⟩ :=
          hload j hj p105 h m98 cs_cprj w141 w142 w143 w144 w145 w146 x_c_nf w147
            (fun x hx => by simp [hx]) hb₀ ev_cprj ld_ctor' info hinfo_get
        have hnf_val : rl.nfields = info.2.1 := by
          rw [hcnf_eq] at heq_nf
          have hv := congrArg ZMod.val (Value.field.inj heq_nf)
          have h1 : ZMod.val (rl.nfields : F) = rl.nfields :=
            ZMod.val_natCast_of_lt (Nat.lt_trans hrnf_lt (by decide))
          have h2 : ZMod.val (info.2.1 : F) = info.2.1 :=
            ZMod.val_natCast_of_lt (Nat.lt_trans hcnf_lt (by decide))
          omega
        -- Step 2: `nat_rule_rhs` + `posOf_structRecRhsR` + `wrap_rel`
        have ext_h_98 := ev_cprj.heap_extends
        have hload_rhs : NatCtorLoadT κ b₀ idx k ctors_info x_block cs_rhs :=
          hload.mono_calls (fun x hx => by simp [hx])
        have hhead_rhs : NatCtorRetHeadT b₀ idx nP ctors_info x_block cs_rhs :=
          hhead.mono_calls (fun x hx => by simp [hx])
        have hgood_rhs : Good c cs_rhs := hgood.sub (fun x hx => by simp [hx])
        have hbnd_rhs : IxVM.Consistency.Bounded cs_rhs :=
          RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
        obtain ⟨rhs_c, hrhs_c, hrhs_c_tm⟩ :=
          natT_rule_rhs_spec hT hκ_inj hRec hidx hCres hnCtors_lt hnP_lt hj hwf_all hsT_pos
            hmot_eq hload_rhs hhead_rhs hgood_rhs hbnd_rhs
            (Bytes.repAddressRef_heapMono₂ addrTy ext_h_98 hb₀)
            (Bytes.repAddressRef_heapMono₂ addrTy ext_h_98 hbT)
            (Bytes.repAddressRef_heapMono₂ addrTy ext_h_98 hbRec)
            (RepKLevelList.mono hlps ext_h_98)
            (RepKLevelList.mono hrlvls ext_h_98)
            (repKLevel_heapMono₂ ext_h_98 hpw)
            (htty.mono ext_h_98)
            (hmotive.mono ext_h_98)
            ev_rhs
        let rlps := if large then k :: List.range k else List.range k
        let elim := if large then k else 0
        let ctors₀ := ctors_info.map (fun info => (info.1, info.2.1, info.2.2.2.1, info.2.2.2.2))
        have hj₀ : j < ctors₀.length := by simp [ctors₀, hj]
        have hcs₀ : ∀ entry ∈ ctors₀,
            (∃ cbs cbody, entry.2.2.1.stripPis (nP + entry.2.1) = some (cbs, cbody)) ∧
            ∀ i ∈ entry.2.2.2, i < entry.2.1 := by
          intro entry hentry
          simp only [ctors₀, List.mem_map] at hentry
          obtain ⟨inf, hinf_mem, rfl⟩ := hentry
          have hwf_inf := hwf_all inf hinf_mem
          obtain ⟨cbs, _, cbody, hsC⟩ := hwf_inf.strip_C
          exact ⟨⟨cbs, _, hsC⟩, fun i hi => hwf_inf.recIdx_lt i hi⟩
        have hpos_rhs := posOf_structRecRhsR k large T nP nIdx tty₀ ctors₀ recC j
          hj₀ ⟨tbs₀, tsort₀, hsT₀⟩ hcs₀
        dsimp only at hpos_rhs
        rw [← clvls_eq_subst_params k large, ← rlvls_eq_subst_params k large] at hpos_rhs
        have hmap_cs :
            (ctors₀.map fun entry => (entry.1, entry.2.1, posOf rlps entry.2.2.1, entry.2.2.2)) =
            (ctors_info.map fun inf => (inf.1, inf.2.1, posOf rlps inf.2.2.2.1, inf.2.2.2.2)) := by
          simp [ctors₀, List.map_map, Function.comp_def]
        rw [hmap_cs, hrhs_c] at hpos_rhs
        rw [Option.map_eq_some_iff] at hpos_rhs
        obtain ⟨rhsG, hrhsG, hpos_rhsG⟩ := hpos_rhs
        rw [← hpos_rhsG] at hrhs_c_tm
        have ext_h_244 := ext_h_98.trans ev_rhs.heap_extends
        have hgood_wrap : Good c cs_wrap := hgood.sub (fun x hx => by simp [hx])
        have hrhs_decl_tm : Tm κ 0 (fun _ => default) m244 0 (posOf rlps rl.rhs) x_rhs :=
          (hrhs_tmC 0 (fun _ => default)).mono ext_h_244
        have hwrap_pos := wrapL_rel_spec hlf hgood_wrap hrhs_c_tm hrhs_decl_tm ev_wrap
        have hwrap_j : WrapRelSem find? rhsG rl.rhs :=
          WrapRelSem.of_posOf_perm (rlps_perm k large) hwrap_pos
        -- Step 3: recursive tail `rls_rest` at `j + 1`
        rw [evalBinOp_add_one j op_j1] at ev_rec
        have ext_h_230 := ext_h_244.trans ev_wrap.heap_extends
        have hload_rec : NatCtorLoadT κ b₀ idx k ctors_info x_block cs_rec :=
          hload.mono_calls (fun x hx => by simp [hx])
        have hhead_rec : NatCtorRetHeadT b₀ idx nP ctors_info x_block cs_rec :=
          hhead.mono_calls (fun x hx => by simp [hx])
        have hgood_rec : Good c cs_rec := hgood.sub (fun x hx => by simp [hx])
        have hbnd_rec : IxVM.Consistency.Bounded cs_rec :=
          RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
        have htail := ih (j + 1) hj_rest
          (hrules_rest.mono ext_h_230)
          hload_rec hhead_rec hgood_rec hbnd_rec
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_230 hb₀)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_230 hbT)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_230 hbRec)
          (RepKLevelList.mono hlps ext_h_230)
          (RepKLevelList.mono hrlvls ext_h_230)
          (repKLevel_heapMono₂ ext_h_230 hpw)
          (htty.mono ext_h_230)
          (hmotive.mono ext_h_230)
          ev_rec
        intro _ _ _ i hlt hj_i
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero, Nat.add_zero]
          exact ⟨hnf_val, rhsG, hrhsG, hwrap_j⟩
        | succ i' =>
          have hlt' : i' < rls_rest.length := Nat.lt_of_succ_lt_succ hlt
          have hj_i' : (j + 1) + i' < ctors_info.length := by omega
          obtain ⟨hnf', rhsG', hrhsG', hwrap'⟩ := htail i' hlt' hj_i'
          have hadd : j + (i' + 1) = (j + 1) + i' := by omega
          simp only [List.getElem_cons_succ, hadd]
          exact ⟨hnf', rhsG', hrhsG', hwrap'⟩

end IxVM.Refinement.Decl
