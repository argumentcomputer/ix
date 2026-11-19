import IxVMRefinement.Binding.FamilyReconFlat
import IxVMRefinement.Binding.FamilyReconAnswers
import IxVMRefinement.Decl.NativeFront
import IxVMRefinement.Obs.KernelCheck1
import IxVMRefinement.Obs.KernelModeled3
import IxVMRefinement.Obs.KernelModeled4
import IxVMRefinement.Obs.KernelModeled6

/-! # The flattened family's derivation: the nested walk on `TmOExact`

`KernelModeled::check_nested_aux` derives a block's flattened family from its constructors
(`nested_walk` and its helpers) and compares it with the family record's entries. This module
refines the derivation, function by function, against the model of `FamilyFlat`: an observed call
on represented inputs returns the model function's value, represented.

* Model facts: `exprSize` of a spine's head and arguments, `occScanF_fuel` (the scan of a term is
  one at every fuel from the term's size on), and the scans only append (`occScanF_prefix`,
  `ctorsLoop_prefix`).
* The store answers the derivation reads, among the calls of a run: `FlatAddrOf`,
  `FlatIndAnswersIn` (`Ingress::get_ci`), `FlatCtorAnswersIn` (`Ingress::get_ci_cprj`),
  `FlatMembersAnswersIn` (`KernelCheck::build_flat_originals`); the specification of the
  membership test the walk calls and this module does not refine (`AuxEntryInSpecIn`); and the
  bound on the binder depth the scan's calls carry (`ScanDepthIn`).
* `occ_params_lower_spec` (`occParamsLower`), `add_block_members_spec` (`addBlockMembers`),
  `inst_ctor_params_spec` (`instCtorParams`), `occ_mentions_block_spec` (`mentions`),
  `occ_any_mentions_block_spec` (`mentionsList`), `occ_scan_spec` and `occ_scan_list_spec`
  (`occScanF`, `scanList`), `ctors_scan_spec` (`ctorsLoop`), **`nested_walk_spec`**
  (`nestedWalk`), **`nested_walk_derivedFlatAt`** (`derivedFlatAt`), `aux_count_spec`.
* `aux_already_in_spec`: `KernelCheck::aux_already_in`, the record side's membership test,
  decides `auxEntryIn`.
* At a store: `flatAddrOf_ofStore`, `flatIndAnswersIn_ofStore` (from the reconstruction's
  `IndAnswers`). -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Core (W KExpr KLevel KKey kexprEnum kexprListEnum addrListEnum addrTy ixAddr)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM (F)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The model: sizes, fuel, and appending -/

theorem exprSize_pos (e : KExpr) : 0 < exprSize e := by
  cases e <;> simp [exprSize]

theorem exprSize_getAppFn_le (e : KExpr) : exprSize e.getAppFn ≤ exprSize e := by
  induction e with
  | app f a ihf _ =>
    have h : exprSize (Ix.Kernel.Expr.app f a).getAppFn = exprSize f.getAppFn := rfl
    rw [h]
    simp only [exprSize]
    omega
  | _ => exact Nat.le_refl _

theorem exprSize_getAppArgs_lt (e : KExpr) : ∀ x ∈ e.getAppArgs, exprSize x < exprSize e := by
  induction e with
  | app f a ihf _ =>
    intro x hx
    have hx' : x ∈ f.getAppArgs ++ [a] := hx
    rcases List.mem_append.mp hx' with h | h
    · have := ihf x h
      simp only [exprSize]
      omega
    · obtain rfl : x = a := by simpa using h
      simp only [exprSize]
      omega
  | _ => intro x hx; cases (show x ∈ ([] : List KExpr) from hx)

theorem scanList_congr {rec rec' : KExpr → List FlatEntry → Option (List FlatEntry)} :
    ∀ (l : List KExpr), (∀ x ∈ l, ∀ acc, rec x acc = rec' x acc) →
      ∀ acc, scanList rec l acc = scanList rec' l acc
  | [], _, _ => rfl
  | x :: xs, h, acc => by
    simp only [scanList]
    rw [h x (by simp)]
    cases rec' x acc with
    | none => rfl
    | some a => exact scanList_congr xs (fun y hy => h y (by simp [hy])) a

theorem appCase_congr {rec rec' : KExpr → Nat → List FlatEntry → Option (List FlatEntry)}
    (V : FlatView) (B : _root_.Address) (hd : KExpr) (args : List KExpr) (d : Nat)
    (hhd : ∀ acc, rec hd d acc = rec' hd d acc)
    (hargs : ∀ x ∈ args, ∀ acc, rec x d acc = rec' x d acc) (acc : List FlatEntry) :
    appCase rec V B hd args d acc = appCase rec' V B hd args d acc := by
  have hs : ∀ acc, scanList (fun x acc => rec x d acc) args acc =
      scanList (fun x acc => rec' x d acc) args acc :=
    scanList_congr args (fun x hx acc => hargs x hx acc)
  unfold appCase
  cases hk : constOf hd with
  | none =>
    simp only [hhd acc]
    cases h1 : rec' hd d acc with
    | none => rfl
    | some a => exact hs a
  | some p =>
    obtain ⟨c, us⟩ := p
    simp only
    cases ha : V.addr c with
    | none => rfl
    | some ca =>
      simp only
      cases hc : V.ci ca with
      | none => rfl
      | some x =>
        cases x with
        | none => exact hs acc
        | some i =>
          simp only
          cases hn : nestedAt V B i args with
          | none => rfl
          | some b =>
            cases b with
            | false => exact hs acc
            | true => rfl

/-- **The scan of a term is one at every fuel from the term's size on.** -/
theorem occScanF_fuel (V : FlatView) (B : _root_.Address) :
    ∀ (n m : Nat) (e : KExpr), exprSize e ≤ n → exprSize e ≤ m →
      ∀ d acc, occScanF V B n e d acc = occScanF V B m e d acc := by
  intro n
  induction n with
  | zero => intro m e hn; have := exprSize_pos e; omega
  | succ n ih =>
    intro m e hn hm d acc
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := exprSize_pos e; omega⟩
    simp only [occScanF]
    cases hmen : mentions V B e with
    | none => rfl
    | some b =>
      cases b with
      | false => rfl
      | true =>
        cases e with
        | app f a =>
          simp only
          have hfn := exprSize_getAppFn_le (Ix.Kernel.Expr.app f a)
          have hfn' : exprSize (Ix.Kernel.Expr.app f a).getAppFn ≤ exprSize f :=
            exprSize_getAppFn_le f
          have hsz : exprSize (Ix.Kernel.Expr.app f a) = exprSize f + exprSize a + 1 := rfl
          exact appCase_congr V B _ _ d
            (fun acc => ih m _ (by omega) (by omega) d acc)
            (fun x hx acc => by
              have := exprSize_getAppArgs_lt _ x hx
              exact ih m x (by omega) (by omega) d acc) acc
        | lam t b l =>
          have hsz : exprSize (Ix.Kernel.Expr.lam t b l) = exprSize t + exprSize b + 1 := rfl
          simp only
          rw [ih m t (by omega) (by omega) d acc]
          cases occScanF V B m t d acc with
          | none => rfl
          | some a1 => exact ih m b (by omega) (by omega) (d + 1) a1
        | forallE t b l =>
          have hsz : exprSize (Ix.Kernel.Expr.forallE t b l) = exprSize t + exprSize b + 1 := rfl
          simp only
          rw [ih m t (by omega) (by omega) d acc]
          cases occScanF V B m t d acc with
          | none => rfl
          | some a1 => exact ih m b (by omega) (by omega) (d + 1) a1
        | letE t v b l =>
          have hsz : exprSize (Ix.Kernel.Expr.letE t v b l) =
              exprSize t + exprSize v + exprSize b + 1 := rfl
          simp only
          rw [ih m t (by omega) (by omega) d acc]
          cases occScanF V B m t d acc with
          | none => rfl
          | some a1 =>
            simp only
            rw [ih m v (by omega) (by omega) d a1]
            cases occScanF V B m v d a1 with
            | none => rfl
            | some a2 => exact ih m b (by omega) (by omega) (d + 1) a2
        | proj s i x =>
          have hsz : exprSize (Ix.Kernel.Expr.proj s i x) = exprSize x + 1 := rfl
          simp only
          exact ih m x (by omega) (by omega) d acc
        | bvar _ => rfl
        | fvar _ _ => rfl
        | sort _ => rfl
        | const _ _ => rfl
        | lit _ => rfl

theorem addBlockMembers_prefix :
    ∀ (ms : List _root_.Address) (sp : List KExpr) (us : List KLevel) (acc : List FlatEntry),
      acc <+: addBlockMembers ms sp us acc
  | [], _, _, acc => List.prefix_refl acc
  | m :: ms, sp, us, acc => by
    simp only [addBlockMembers]
    split
    · exact addBlockMembers_prefix ms sp us acc
    · exact (List.prefix_append acc _).trans (addBlockMembers_prefix ms sp us _)

theorem scanList_prefix {rec : KExpr → List FlatEntry → Option (List FlatEntry)}
    (hr : ∀ x acc r, rec x acc = some r → acc <+: r) :
    ∀ (l : List KExpr) (acc r : List FlatEntry), scanList rec l acc = some r → acc <+: r := by
  intro l
  induction l with
  | nil => intro acc r h; cases h; exact List.prefix_refl _
  | cons x xs ih =>
    intro acc r h
    simp only [scanList] at h
    cases hx : rec x acc with
    | none => simp [hx] at h
    | some a =>
      simp only [hx] at h
      exact (hr x acc a hx).trans (ih a r h)

theorem appCase_prefix {rec : KExpr → Nat → List FlatEntry → Option (List FlatEntry)}
    (hr : ∀ e d acc r, rec e d acc = some r → acc <+: r)
    {V : FlatView} {B : _root_.Address} {hd : KExpr} {args : List KExpr} {d : Nat}
    {acc r : List FlatEntry} (h : appCase rec V B hd args d acc = some r) : acc <+: r := by
  have hs : ∀ acc r, scanList (fun x acc => rec x d acc) args acc = some r → acc <+: r :=
    scanList_prefix (fun x acc r => hr x d acc r) args
  unfold appCase at h
  cases hk : constOf hd with
  | none =>
    simp only [hk] at h
    cases h1 : rec hd d acc with
    | none => simp [h1] at h
    | some a =>
      simp only [h1] at h
      exact (hr hd d acc a h1).trans (hs a r h)
  | some p =>
    obtain ⟨c, us⟩ := p
    simp only [hk] at h
    cases ha : V.addr c with
    | none => simp [ha] at h
    | some ca =>
      simp only [ha] at h
      cases hc : V.ci ca with
      | none => simp [hc] at h
      | some x =>
        cases x with
        | none =>
          simp only [hc] at h
          exact hs acc r h
        | some i =>
          simp only [hc] at h
          cases hn : nestedAt V B i args with
          | none => simp [hn] at h
          | some b =>
            cases b with
            | false =>
              simp only [hn] at h
              exact hs acc r h
            | true =>
              simp only [hn] at h
              cases hm : V.members i.blk with
              | none => simp [hm] at h
              | some ms =>
                simp only [hm] at h
                cases ho : occParamsLower (args.take i.np) d with
                | none => simp [ho] at h
                | some sp =>
                  simp only [ho] at h
                  cases h
                  exact addBlockMembers_prefix ms sp us acc

/-- **A scan only appends entries.** -/
theorem occScanF_prefix (V : FlatView) (B : _root_.Address) :
    ∀ (n : Nat) (e : KExpr) (d : Nat) (acc r : List FlatEntry),
      occScanF V B n e d acc = some r → acc <+: r := by
  intro n
  induction n with
  | zero => intro e d acc r h; simp [occScanF] at h
  | succ n ih =>
    intro e d acc r h
    simp only [occScanF] at h
    cases hm : mentions V B e with
    | none => simp [hm] at h
    | some b =>
      cases b with
      | false =>
        simp only [hm] at h
        cases h
        exact List.prefix_refl _
      | true =>
        simp only [hm] at h
        cases e with
        | app f a =>
          simp only at h
          exact appCase_prefix ih h
        | lam t b m =>
          simp only at h
          cases h1 : occScanF V B n t d acc with
          | none => simp [h1] at h
          | some a1 =>
            simp only [h1] at h
            exact (ih t d acc a1 h1).trans (ih b (d + 1) a1 r h)
        | forallE t b m =>
          simp only at h
          cases h1 : occScanF V B n t d acc with
          | none => simp [h1] at h
          | some a1 =>
            simp only [h1] at h
            exact (ih t d acc a1 h1).trans (ih b (d + 1) a1 r h)
        | letE t v b l =>
          simp only at h
          cases h1 : occScanF V B n t d acc with
          | none => simp [h1] at h
          | some a1 =>
            simp only [h1] at h
            cases h2 : occScanF V B n v d a1 with
            | none => simp [h2] at h
            | some a2 =>
              simp only [h2] at h
              exact (ih t d acc a1 h1).trans ((ih v d a1 a2 h2).trans (ih b (d + 1) a2 r h))
        | proj s i x =>
          simp only at h
          exact ih x d acc r h
        | bvar _ => cases h; exact List.prefix_refl _
        | fvar _ _ => cases h; exact List.prefix_refl _
        | sort _ => cases h; exact List.prefix_refl _
        | const _ _ => cases h; exact List.prefix_refl _
        | lit _ => cases h; exact List.prefix_refl _

/-- **The constructors' scan only appends entries.** -/
theorem ctorsLoop_prefix (V : FlatView) (B : _root_.Address) (i : IndInfo) (aux : Bool)
    (sp : List KExpr) (us : List KLevel) :
    ∀ (cs : List Nat) (acc r : List FlatEntry), ctorsLoop V B i aux sp us cs acc = some r →
      acc <+: r := by
  intro cs
  induction cs with
  | nil => intro acc r h; cases h; exact List.prefix_refl _
  | cons c cs ih =>
    intro acc r h
    simp only [ctorsLoop] at h
    cases h1 : ctorScan V B i aux sp us acc c with
    | none => simp [h1] at h
    | some a =>
      simp only [h1] at h
      refine List.IsPrefix.trans ?_ (ih a r h)
      unfold ctorScan at h1
      cases hc : V.ctorType i.blk i.idx c with
      | none => simp [hc] at h1
      | some cty =>
        simp only [hc] at h1
        cases hb : ctorBody aux i.np sp (exprInstLevels us cty) with
        | none => simp [hb] at h1
        | some body =>
          simp only [hb] at h1
          exact occScanF_prefix V B _ body 0 acc a h1

/-! ## What the derivation asks of the run -/

/-- The view's key-address map inverts `κ`. -/
def FlatAddrOf (κ : _root_.Address → KKey) (Vf : FlatView) : Prop :=
  ∀ a : _root_.Address, Vf.addr (κ a) = some a

/-- **`Ingress::get_ci` matches `Vf.ci` on `Induct` vs non-`Induct`**, for a load that is one of
the calls `root` and whose own calls are among them, with the bounds a load gives (the counts and
the position below `2^56`). -/
def FlatIndAnswersIn (root : List (Call F)) (Vf : FlatView) : Prop :=
  ∀ {xa p ci : SourceValue F} {h m : Heap F} {cs : List (Call F)} {a : Bytes.Address},
    Bytes.RepAddressRef addrTy h a xa →
    ObsFn W "Ingress::get_ci" [xa] h p m cs →
    (⟨"Ingress::get_ci", [xa], h⟩ : Call F) ∈ root → (∀ c ∈ cs, c ∈ root) →
    loadValue m p = .ok ci →
    (∀ xnl xty xnp xni xnc xrec xblk xidx,
      ci = .construct "KernelTypes::KConstantInfo" "Induct"
        [xnl, xty, xnp, xni, xnc, xrec, xblk, xidx] →
      ∃ (d : IndInfo) (ba : Bytes.Address),
        Vf.ci (ixAddr a) = some (some d) ∧
        d.np < 72057594037927936 ∧ d.nctors < 72057594037927936 ∧ d.idx < 72057594037927936 ∧
        xnp = .field (d.np : F) ∧ xnc = .field (d.nctors : F) ∧
        ixAddr ba = d.blk ∧ Bytes.RepAddressRef addrTy m ba xblk ∧ xidx = .field (d.idx : F)) ∧
    ((∀ vs : List (SourceValue F), vs.length = 8 →
        ci ≠ .construct "KernelTypes::KConstantInfo" "Induct" vs) →
      Vf.ci (ixAddr a) = some none)

/-- **`Ingress::get_ci_cprj` loads the constructor type `Vf.ctorType` reads, among the calls
`root` and at the blocks of `S`**, represented exactly. -/
def FlatCtorAnswersIn (root : List (Call F)) (S : _root_.Address → Prop)
    (κ : _root_.Address → KKey) (Vf : FlatView) : Prop :=
  ∀ {xblk p ci : SourceValue F} {h m : Heap F} {cs : List (Call F)} {ba : Bytes.Address}
    {i c : Nat},
    Bytes.RepAddressRef addrTy h ba xblk →
    ObsFn W "Ingress::get_ci_cprj" [xblk, .field (i : F), .field (c : F)] h p m cs →
    (∀ c ∈ cs, c ∈ root) → S (ixAddr ba) →
    i < 72057594037927936 → c < 72057594037927936 → loadValue m p = .ok ci →
    ∀ xnl xty xblk' xind xcidx xnp xnf xuns,
      ci = .construct "KernelTypes::KConstantInfo" "Ctor"
        [xnl, xty, xblk', xind, xcidx, xnp, xnf, xuns] →
      ∃ ty : KExpr, Vf.ctorType (ixAddr ba) i c = some ty ∧ TmOExact κ m ty xty

/-- An entry of `build_flat_originals`, read for its type's address alone. -/
def MemberAddrRep (h : Heap F) (a : _root_.Address) (p : SourceValue F) : Prop :=
  ∃ (xa x2 x3 x4 : SourceValue F) (ba : Bytes.Address), p = .tuple [xa, x2, x3, x4] ∧
    Bytes.RepAddressRef addrTy h ba xa ∧ ixAddr ba = a

theorem memberAddrRep_heapMono₂ : HeapMono₂ MemberAddrRep :=
  fun _ _ _ _ ext ⟨xa, x2, x3, x4, ba, hp, ra, ha⟩ =>
    ⟨xa, x2, x3, x4, ba, hp, Bytes.repAddressRef_heapMono₂ addrTy ext ra, ha⟩

/-- **`KernelCheck::build_flat_originals(blk, 0)` lists the types `Vf.members` reads, among the
calls `root`**, at the block of an inductive type the view reads. -/
def FlatMembersAnswersIn (root : List (Call F)) (Vf : FlatView) : Prop :=
  ∀ {xblk r : SourceValue F} {h m : Heap F} {cs : List (Call F)} {ba : Bytes.Address}
    {a : _root_.Address} {d : IndInfo},
    Bytes.RepAddressRef addrTy h ba xblk →
    ObsFn W "KernelCheck::build_flat_originals" [xblk, .field 0] h r m cs →
    (∀ c ∈ cs, c ∈ root) → Vf.ci a = some (some d) → ixAddr ba = d.blk →
    ∃ ms, Vf.members d.blk = some ms ∧ RepList flatListEnum MemberAddrRep m ms r

/-- **`KernelModeled::occ_mentions_block` at the one block `B` computes `mentions`, among the
calls `root`.** -/
def OccMentionsSpecIn (root : List (Call F)) (κ : _root_.Address → KKey) (Vf : FlatView)
    (B : _root_.Address) : Prop :=
  ∀ {E : KExpr} {pe xbs r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {bb : Bytes.Address},
    ObsFn W "KernelModeled::occ_mentions_block" [pe, xbs] h r h' cs →
    IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
    TmOExact κ h E pe → RepList addrListEnum (Bytes.RepAddressRef addrTy) h [bb] xbs →
    ixAddr bb = B →
    ∃ b : Bool, mentions Vf B E = some b ∧ r = .field (if b then 1 else 0)

/-- **`KernelModeled::aux_entry_in` decides `auxEntryIn`, among the calls `root`.** -/
def AuxEntryInSpecIn (root : List (Call F)) (κ : _root_.Address → KKey) : Prop :=
  ∀ {es : List FlatEntry} {a : Bytes.Address} {sp : List KExpr} {us : List KLevel}
    {xflat xa xsp xus r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
    ObsFn W "KernelModeled::aux_entry_in" [xflat, xa, xsp, xus] h r h' cs →
    IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
    RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
    Bytes.RepAddressRef addrTy h a xa →
    RepList kexprListEnum (TmOExact κ) h sp xsp → RepKLevelList h us xus →
    r = .field (if auxEntryIn es (ixAddr a) sp us then 1 else 0)

/-- **Every `KernelModeled::occ_scan` among the calls `root` is under fewer than `2^62`
binders.** The circuit counts the binders in a field element and the model in a natural. -/
def ScanDepthIn (root : List (Call F)) : Prop :=
  ∀ {xb xe xacc : SourceValue F} {d : F} {h : Heap F},
    (⟨"KernelModeled::occ_scan", [xb, xe, .field d, xacc], h⟩ : Call F) ∈ root →
    ZMod.val d < 4611686018427387904

/-! ## Flags and entry lists -/

theorem bit_eq_one {b : Bool}
    (h : (.field (if b then 1 else 0) : SourceValue F) = .field 1) : b = true := by
  cases b
  · exact absurd (Value.field.inj h) (by decide)
  · rfl

theorem bit_ne_one {b : Bool}
    (h : (.field (if b then 1 else 0) : SourceValue F) ≠ .field 1) : b = false := by
  cases b
  · rfl
  · exact (h (by simp)).elim

theorem bit_eq_zero {b : Bool}
    (h : (.field (if b then 1 else 0) : SourceValue F) = .field 0) : b = false := by
  cases b
  · rfl
  · exact absurd (Value.field.inj h) (by decide)

theorem bit_ne_zero {b : Bool}
    (h : (.field (if b then 1 else 0) : SourceValue F) ≠ .field 0) : b = true := by
  cases b
  · exact (h (by simp)).elim
  · rfl

/-- The type of a flattened family's entry. -/
abbrev flatEntryTy : Generic.Ty :=
  .tuple [(.ptr (.array .field 32)), .field,
    (.ptr (.named "Lists::Node" [(.ptr (.named "KernelTypes::KExprNode" []))])),
    (.ptr (.named "Lists::Node" [(.ptr (.named "KernelTypes::KLevelNode" []))]))]

theorem flat_length {α : Type} {R : Heap F → α → SourceValue F → Prop} {xs : List α}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>» [l] h r h' cs)
    (hl : RepList flatListEnum R h xs l) : r = .field (xs.length : F) ∧ h' = h :=
  Lib.Lists.length_spec (t := flatEntryTy) (R := R)
    (by rw [Obs.Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact hl)

theorem flat_lookup {α : Type} {R : Heap F → α → SourceValue F → Prop} {xs : List α}
    {l r : SourceValue F} {i : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::lookup<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>» [l, .field i] h r h' cs)
    (hl : RepList flatListEnum R h xs l) : (∃ x, xs[i.val]? = some x ∧ R h x r) ∧ h' = h :=
  Lib.Lists.lookup_spec (t := flatEntryTy) (R := R)
    (by rw [Obs.Names.«Lists::lookup<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact hl)

theorem flat_snoc {κ : _root_.Address → KKey} {es : List FlatEntry} {e : FlatEntry}
    {l v r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::snoc<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>» [l, v] h r h' cs)
    (hl : RepList flatListEnum (FlatEntryRepExact κ) h es l) (he : FlatEntryRepExact κ h e v) :
    RepList flatListEnum (FlatEntryRepExact κ) h' (es ++ [e]) r := by
  have hs := Lib.Lists.snoc_spec (t := flatEntryTy) (flatEntryRepExact_heapMono₂ (κ := κ))
    (by rw [Obs.Names.«Lists::snoc<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact hl) he
  rwa [Obs.Names.«Lists::Node<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol] at hs

theorem kexpr_take {κ : _root_.Address → KKey} {xs : List KExpr} {l r : SourceValue F} {n : F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::take<&KernelTypes::KExprNode>» [l, .field n] h r h' cs)
    (hl : RepList kexprListEnum (TmOExact κ) h xs l) :
    RepList kexprListEnum (TmOExact κ) h' (xs.take n.val) r := by
  have ht := (Lib.Lists.take_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
    (tmOExact_heapMono₂ (κ := κ))
    (by rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)).2
  rwa [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at ht

/-! ## `occ_params_lower` -/

/-- **`KernelModeled::occ_params_lower(ds, d)`** is `occParamsLower ds d`: the parameters
lowered past the `d` binders, none of which they mention. -/
theorem occ_params_lower_spec {κ : _root_.Address → KKey} {root : List (Call F)} {d : Nat}
    (hd : d < 4611686018427387904) :
    ∀ (ds : List KExpr) {xds r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelModeled::occ_params_lower" [xds, .field (d : F)] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
      RepList kexprListEnum (TmOExact κ) h ds xds →
      Heap.Extends h h' ∧ ∃ sp, occParamsLower ds d = some sp ∧
        RepList kexprListEnum (TmOExact κ) h' sp r := by
  intro ds
  induction ds with
  | nil =>
    intro xds r h h' cs ev hbnd hroot hds
    match Obs.«KernelModeled::occ_params_lower».obs ev with
    | .Nil (he24 := hr) (hm23 := hm) .. =>
      subst hr hm
      exact ⟨Heap.Extends.snoc _ _, [], rfl, .nil (by simp)⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hds ld
      cases hcons
  | cons x xs ih =>
    intro xds r h h' cs ev hbnd hroot hds
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelModeled::occ_params_lower».obs ev with
    | .Nil (ld12 := ld) .. =>
      cases IxVM.Refinement.Core.RepList.nil_of_load hds ld
    | .Cons (x_x := xx) (x_rest := xrest) (v57 := v57) (m60 := m60) (cs68 := cs1) (v109 := vl)
        (v110 := vr) (m112 := m112) (cs120 := cs2) (m147 := m147) (cs155 := cs3) (ld12 := ld)
        (ev70 := evh) (heq100 := heq) (he105 := hr) (hm104 := hm) (ev122 := evl)
        (ev157 := evrec) (hc174 := hc) .. =>
      subst hr hm heq
      obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hds ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      have evh' : ObsFn W "KernelSubst::has_bvar_in_range"
          [xx, .field ((0 : Nat) : F), .field (d : F)] h (.field 0) m60 cs1 := by
        simpa using evh
      obtain ⟨hh, hnoidx, hbv⟩ := has_bvar_in_range_zero_tmOExact (by decide) hd
        (sub fun c hc' => by rw [hc]; simp [hc']) hz evh'
      subst hh
      have evl' : ObsFn W "KernelSubst::expr_lower"
          [xx, .field (d : F), .field ((0 : Nat) : F)] m60 vl m112 cs2 := by simpa using evl
      have hvl := expr_lower_tmOExact hd (by decide) (sub fun c hc' => by rw [hc]; simp [hc']) hz
        (by simpa using hnoidx) evl'
      obtain ⟨ext3, sp, hsp, hrep⟩ := ih evrec (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc']))
        (tmOExactList_mono evl.heap_extends hzs')
      refine ⟨evl.heap_extends.trans (ext3.trans (Heap.Extends.snoc _ _)),
        Ix.Kernel.Expr.lowerBVars d 0 x :: sp, by simp [occParamsLower, hbv, hsp], ?_⟩
      exact Lib.rep_store_cons tmOExact_heapMono₂ (hvl.mono ext3) hrep

/-! ## `add_block_members` -/

/-- **`KernelModeled::add_block_members(members, sp, us, acc)`** is `addBlockMembers`: every
type of the occurrence's block at its parameters and levels, unless already an entry. -/
theorem add_block_members_spec {κ : _root_.Address → KKey} {root : List (Call F)}
    (aux_entry_in : AuxEntryInSpecIn root κ) {sp : List KExpr} {us : List KLevel} :
    ∀ (ms : List _root_.Address) {acc : List FlatEntry} {xms xsp xus xacc r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelModeled::add_block_members" [xms, xsp, xus, xacc] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
      RepList flatListEnum MemberAddrRep h ms xms →
      RepList kexprListEnum (TmOExact κ) h sp xsp → RepKLevelList h us xus →
      RepList flatListEnum (FlatEntryRepExact κ) h acc xacc →
      Heap.Extends h h' ∧
        RepList flatListEnum (FlatEntryRepExact κ) h' (addBlockMembers ms sp us acc) r := by
  intro ms
  induction ms with
  | nil =>
    intro acc xms xsp xus xacc r h h' cs ev hbnd hroot hms hsp hus hacc
    match Obs.«KernelModeled::add_block_members».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. =>
      subst hr hh
      exact ⟨Heap.Extends.refl _, hacc⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hms ld
      cases hcons
  | cons m ms ih =>
    intro acc xms xsp xus xacc r h h' cs ev hbnd hroot hms hsp hus hacc
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelModeled::add_block_members».obs ev with
    | .Nil (ld12 := ld) .. =>
      cases IxVM.Refinement.Core.RepList.nil_of_load hms ld
    | .Cons (x_rest := xrest) (x_maddr := xmaddr) (v194 := vacc) (m195 := m1) (cs197 := cs1)
        (cs206 := cs2) (ld12 := ld) (sg202 := sg) (ev208 := evrec) (hc241 := hc) .. =>
      obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hms ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      obtain ⟨xa, x2, x3, x4, ba, htup, rba, hba⟩ := hz
      injection htup with hl
      injection hl with h1 _
      subst h1 hba
      have hseg : Heap.Extends h m1 ∧ RepList flatListEnum (FlatEntryRepExact κ) m1
          (if auxEntryIn acc (ixAddr ba) sp us then acc
            else acc ++ [⟨ixAddr ba, true, sp, us⟩]) vacc := by
        cases sg with
        | n1 m81 cs92 ev94 he132 he133 hc134 =>
          subst he132 he133
          have hin := bit_eq_one (aux_entry_in ev94
            (sub fun c hc' => by rw [hc, hc134]; simp [hc'])
            (fun c hc' => hroot c (by rw [hc, hc134]; simp [hc'])) hacc rba hsp hus).symm
          rw [ite_eq_left hin]
          exact ⟨ev94.heap_extends, flatList_mono ev94.heap_extends hacc⟩
        | other v80 m81 cs92 cs142 ev94 hne135 ev144 hc193 =>
          have hv := aux_entry_in ev94
            (sub fun c hc' => by rw [hc, hc193]; simp [hc'])
            (fun c hc' => hroot c (by rw [hc, hc193]; simp [hc'])) hacc rba hsp hus
          subst hv
          have hin := bit_ne_one hne135
          rw [ite_eq_right (by simp [hin])]
          have ext1 := ev94.heap_extends
          have hentry : FlatEntryRepExact κ m81 ⟨ixAddr ba, true, sp, us⟩
              (.tuple [xmaddr, .field 1, xsp, xus]) :=
            ⟨xmaddr, xsp, xus, ba, by simp [auxVal], Bytes.repAddressRef_heapMono₂ addrTy ext1 rba,
              rfl, tmOExactList_mono ext1 hsp, hus.mono ext1⟩
          exact ⟨ext1.trans ev144.heap_extends,
            flat_snoc ev144 (flatList_mono ext1 hacc) hentry⟩
      obtain ⟨ext1, hacc1⟩ := hseg
      obtain ⟨ext2, hres⟩ := ih evrec (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc']))
        (repList_heapMono₂ flatListEnum memberAddrRep_heapMono₂ ext1 hzs')
        (tmOExactList_mono ext1 hsp) (hus.mono ext1) hacc1
      exact ⟨ext1.trans ext2, by simpa [addBlockMembers] using hres⟩

/-! ## `inst_ctor_params` -/

/-- **`KernelModeled::inst_ctor_params(t, sp)`** is `instCtorParams`: the leading binders
instantiated by `sp`, stepping through any `Let` cells. -/
theorem inst_ctor_params_spec {κ : _root_.Address → KKey} {root : List (Call F)}
    {sp : List KExpr} {E : KExpr} {xt xsp r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelModeled::inst_ctor_params" [xt, xsp] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hE : TmOExact κ h E xt) (hsp : RepList kexprListEnum (TmOExact κ) h sp xsp) :
    Heap.Extends h h' ∧ ∃ T, instCtorParams E sp = some T ∧ TmOExact κ h' T r := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  match Obs.«KernelModeled::inst_ctor_params».obs ev with
  | .Nil (ld12 := ld) (he21 := hr) (he22 := hh) .. =>
    subst hr hh
    obtain rfl := IxVM.Refinement.Core.RepList.nil_of_load hsp ld
    exact ⟨Heap.Extends.refl _, E, by cases E <;> rfl, hE⟩
  | .Cons_Forall (x_v := xv) (x_rest := xrest) (x_body := xbody) (cs_mfoyspyn := cs2)
      (v_mduynwuw := v') (m_ilqodeif := m') (cs_wqqnejsp := cs1) (ld12 := ld)
      (ld_txwzgqvr := ldt) (ev_moovuzip := e1) (ev_bvxpnrar := e2) (hc_ufdvkrjv := hc) .. =>
    obtain ⟨z, zs, rfl, hz, hzs⟩ := IxVM.Refinement.Core.RepList.cons_of_load hsp ld
    obtain ⟨D, Bd, ℓ, rfl, -, hB, -⟩ := TmOExact.forallE_of_load hE ldt
    have hv' := expr_inst1_tmOExact (sub fun c hc' => by rw [hc]; simp [hc']) hB hz e1
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨ext2, T, hT, hrep⟩ := inst_ctor_params_spec e2
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      hv' (tmOExactList_mono e1.heap_extends hzs)
    exact ⟨e1.heap_extends.trans ext2, T, by simpa [instCtorParams] using hT, hrep⟩
  | .Cons_Let (x_v := xv) (x_rest := xrest) (x_lv := xlv) (x_lb := xlb) (cs_jrhgsmcn := cs2)
      (v_rfetjdue := v') (m_vtoiutgh := m') (cs_pshylesg := cs1) (ld12 := ld)
      (ld_txwzgqvr := ldt) (ev_cnnmbauo := e1) (ev_ttnheqnu := e2) (hc_qxidxcae := hc) .. =>
    obtain ⟨T0, V0, B0, rfl, -, hv, hb⟩ := TmOExact.letE_of_load hE ldt
    have hv' := expr_inst1_tmOExact (sub fun c hc' => by rw [hc]; simp [hc']) hb hv e1
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨ext2, res⟩ := inst_ctor_params_spec e2
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      hv' (tmOExactList_mono e1.heap_extends hsp)
    exact ⟨e1.heap_extends.trans ext2, res⟩
termination_by cs.length

/-! ## `occ_mentions_block` -/

/-- **`KernelModeled::occ_mentions_block(e, [block])`** is `mentions`: the term names an
inductive type of the block (stepping through any `Let` cells). -/
theorem occ_mentions_block_spec {κ : _root_.Address → KKey} {root : List (Call F)}
    {Vf : FlatView} {B : _root_.Address} (hA : FlatAddrOf κ Vf) (hI : FlatIndAnswersIn root Vf)
    {E : KExpr} {pe xbs r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {bb : Bytes.Address}
    (ev : ObsFn W "KernelModeled::occ_mentions_block" [pe, xbs] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hE : TmOExact κ h E pe)
    (hbs : RepList addrListEnum (Bytes.RepAddressRef addrTy) h [bb] xbs) (hbb : ixAddr bb = B) :
    ∃ b : Bool, mentions Vf B E = some b ∧ r = .field (if b then 1 else 0) := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  have mbs : ∀ {m : Heap F}, Heap.Extends h m →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) m [bb] xbs :=
    fun e => repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) e hbs
  match Obs.«KernelModeled::occ_mentions_block».obs ev with
  | .BVar (ld_bolbylmd := ld) (he_njbtkguh := hr) .. =>
    obtain ⟨i, -, -, rfl⟩ := TmOExact.bvar_of_load hE ld
    exact ⟨false, rfl, by simp [hr]⟩
  | .Srt (ld_bolbylmd := ld) (he_etzrxboe := hr) .. =>
    obtain ⟨l, rfl, -⟩ := TmOExact.sort_of_load hE ld
    exact ⟨false, rfl, by simp [hr]⟩
  | .Const (x_caddr := xc) (cs_anabekbn := cs1) (ld_bolbylmd := ld) (ev_okamjwqm := evp)
      (hc_atlxlyhr := hc) .. =>
    obtain ⟨ca, ls, rfl, rca, -⟩ := TmOExact.const_of_load hE ld
    have hroot1 : ∀ c ∈ cs1, c ∈ root := fun c hc' => hroot c (by rw [hc]; simp [hc'])
    match Obs.«KernelCheck::caddr_is_peer».obs evp with
    | .Induct (cs15 := csci) (x_ba := xba) (cs92 := csin) (ev17 := evci) (ld11 := ldci)
        (ev94 := evin) (hc111 := hc1) .. =>
      obtain ⟨info, ba, hci, -, -, -, -, -, hba, rba, -⟩ :=
        (hI rca evci (hroot1 _ (by rw [hc1]; simp))
        (fun c hc' => hroot1 c (by rw [hc1]; simp [hc'])) ldci).1
          _ _ _ _ _ _ _ _ rfl
      obtain ⟨-, hres⟩ := IxVM.Refinement.Decl.addr_list_contains_singleton_spec
        (mbs evci.heap_extends) rba evin
      rcases hres with ⟨hr, heq⟩ | ⟨hr, hne⟩
      · refine ⟨true, ?_, by simp [hr]⟩
        simp [mentions, peer, hA (ixAddr ca), hci, ← hba, ← hbb, heq]
      · refine ⟨false, ?_, by simp [hr]⟩
        simp [mentions, peer, hA (ixAddr ca), hci, ← hba, ← hbb, hne]
    | .other (ev17 := evci) (ld11 := ldci) (hne112 := hni) (he116 := hr) (hc118 := hc1) .. =>
      have hci := (hI rca evci (hroot1 _ (by rw [hc1]; simp))
        (fun c hc' => hroot1 c (by rw [hc1]; simp [hc'])) ldci).2 hni
      exact ⟨false, by simp [mentions, peer, hA (ixAddr ca), hci], by simp [hr]⟩
  | .App_n1 (cs_nlxcjtbe := cs1) (ld_bolbylmd := ld) (ev_cwxibbky := ev1) (he_sqbyfahs := hr)
      (hc_gmeblcmg := hc) .. =>
    obtain ⟨Ef, Ea, rfl, hf, -⟩ := TmOExact.app_of_load hE ld
    have hlt : cs1.length < cs.length := by rw [hc]; simp
    obtain ⟨b, hb, hv⟩ := occ_mentions_block_spec hA hI ev1
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      hf hbs hbb
    obtain rfl := bit_eq_one hv.symm
    exact ⟨true, by simp [mentions, orB, hb], by simp [hr]⟩
  | .App_other (cs_nlxcjtbe := cs1) (cs_jlnluzll := cs2) (ld_bolbylmd := ld)
      (ev_cwxibbky := ev1) (hne_rvlihvhx := hne) (ev_cgdhukiy := ev2) (hc_imahflfm := hc) .. =>
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := TmOExact.app_of_load hE ld
    have hlt1 : cs1.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨b, hb, hv⟩ := occ_mentions_block_spec hA hI ev1
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      hf hbs hbb
    subst hv
    obtain rfl := bit_ne_one hne
    have hlt2 : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨b', hb', hr⟩ := occ_mentions_block_spec hA hI ev2
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      (ha.mono ev1.heap_extends) (mbs ev1.heap_extends) hbb
    exact ⟨b', by simp [mentions, orB, hb, hb'], hr⟩
  | .Lam_n1 (cs_sdfuhkpl := cs1) (ld_bolbylmd := ld) (ev_ulwgmnpt := ev1) (he_opcvlshe := hr)
      (hc_sgloqhqt := hc) .. =>
    obtain ⟨T, Bd, ℓ, rfl, hT, -, -⟩ := TmOExact.lam_of_load hE ld
    have hlt : cs1.length < cs.length := by rw [hc]; simp
    obtain ⟨b, hb, hv⟩ := occ_mentions_block_spec hA hI ev1
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      hT hbs hbb
    obtain rfl := bit_eq_one hv.symm
    exact ⟨true, by simp [mentions, orB, hb], by simp [hr]⟩
  | .Lam_other (cs_sdfuhkpl := cs1) (cs_yskgpazx := cs2) (ld_bolbylmd := ld)
      (ev_ulwgmnpt := ev1) (hne_puvcobve := hne) (ev_dizlvils := ev2) (hc_kjyrsefa := hc) .. =>
    obtain ⟨T, Bd, ℓ, rfl, hT, hBd, -⟩ := TmOExact.lam_of_load hE ld
    have hlt1 : cs1.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨b, hb, hv⟩ := occ_mentions_block_spec hA hI ev1
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      hT hbs hbb
    subst hv
    obtain rfl := bit_ne_one hne
    have hlt2 : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨b', hb', hr⟩ := occ_mentions_block_spec hA hI ev2
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      (hBd.mono ev1.heap_extends) (mbs ev1.heap_extends) hbb
    exact ⟨b', by simp [mentions, orB, hb, hb'], hr⟩
  | .Forall_n1 (cs_jnsilbfh := cs1) (ld_bolbylmd := ld) (ev_jphceggz := ev1)
      (he_aimigplr := hr) (hc_gwofqrgs := hc) .. =>
    obtain ⟨T, Bd, ℓ, rfl, hT, -, -⟩ := TmOExact.forallE_of_load hE ld
    have hlt : cs1.length < cs.length := by rw [hc]; simp
    obtain ⟨b, hb, hv⟩ := occ_mentions_block_spec hA hI ev1
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      hT hbs hbb
    obtain rfl := bit_eq_one hv.symm
    exact ⟨true, by simp [mentions, orB, hb], by simp [hr]⟩
  | .Forall_other (cs_jnsilbfh := cs1) (cs_gnwuatpb := cs2) (ld_bolbylmd := ld)
      (ev_jphceggz := ev1) (hne_oaofvnuw := hne) (ev_dbsnzmoy := ev2) (hc_hkhtpxta := hc) .. =>
    obtain ⟨T, Bd, ℓ, rfl, hT, hBd, -⟩ := TmOExact.forallE_of_load hE ld
    have hlt1 : cs1.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨b, hb, hv⟩ := occ_mentions_block_spec hA hI ev1
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      hT hbs hbb
    subst hv
    obtain rfl := bit_ne_one hne
    have hlt2 : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨b', hb', hr⟩ := occ_mentions_block_spec hA hI ev2
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      (hBd.mono ev1.heap_extends) (mbs ev1.heap_extends) hbb
    exact ⟨b', by simp [mentions, orB, hb, hb'], hr⟩
  | .Let (cs_wjijdite := cs2) (cs_yqrxeseo := cs1) (ld_bolbylmd := ld) (ev_gemvpjgn := e1)
      (ev_rbprmbdg := ev2) (hc_qubwlzze := hc) .. =>
    obtain ⟨T0, V0, B0, rfl, -, hv0, hb0⟩ := TmOExact.letE_of_load hE ld
    have hv' := expr_inst1_tmOExact (sub fun c hc' => by rw [hc]; simp [hc']) hb0 hv0 e1
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    exact occ_mentions_block_spec hA hI ev2
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      hv' (mbs e1.heap_extends) hbb
  | .Lit (ld_bolbylmd := ld) (he_pgejtxya := hr) .. =>
    obtain ⟨k, ht⟩ := hE
    have tag : ∀ {addr : Nat} {c : String} {xs : List (SourceValue F)},
        h[addr]? = some (.construct kexprEnum c xs) →
        pe = .ptr (.enum kexprEnum) addr → c = "Lit" := by
      intro addr c xs cell hp
      subst hp
      have hld := Lib.load_enum_cell cell
      rw [ld] at hld
      injection hld with hv
      injection hv with _ htag _
      exact htag.symm
    cases ht with
    | bvarFree _ _ _ hd0 => omega
    | litNat _ _ _ => exact ⟨false, rfl, by simp [hr]⟩
    | litStr _ _ _ => exact ⟨false, rfl, by simp [hr]⟩
    | bvarLocal cell _ _ => exact absurd (tag cell rfl) (by decide)
    | sort cell _ => exact absurd (tag cell rfl) (by decide)
    | const cell _ _ => exact absurd (tag cell rfl) (by decide)
    | app cell _ _ => exact absurd (tag cell rfl) (by decide)
    | lam cell _ _ _ => exact absurd (tag cell rfl) (by decide)
    | forallE cell _ _ _ => exact absurd (tag cell rfl) (by decide)
    | letE cell _ _ _ => exact absurd (tag cell rfl) (by decide)
    | proj cell _ _ => exact absurd (tag cell rfl) (by decide)
  | .Proj (cs_yblrkquu := cs1) (ld_bolbylmd := ld) (ev_fnwcywxx := ev1) (hc_rksetomy := hc) .. =>
    obtain ⟨pa, pi, Es, rfl, rfl, -, hEs⟩ := TmOExact.proj_of_load hE ld
    have hlt : cs1.length < cs.length := by rw [hc]; simp
    obtain ⟨b, hb, hr⟩ := occ_mentions_block_spec hA hI ev1
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      hEs hbs hbb
    exact ⟨b, hb, hr⟩
termination_by cs.length

/-- **The mention test's specification holds where the view answers `Ingress::get_ci`.** -/
theorem occMentionsSpecIn_of_answers {κ : _root_.Address → KKey} {root : List (Call F)}
    {Vf : FlatView} {B : _root_.Address} (hA : FlatAddrOf κ Vf)
    (hI : FlatIndAnswersIn root Vf) : OccMentionsSpecIn root κ Vf B :=
  fun ev hbnd hroot hE hbs hbb => occ_mentions_block_spec hA hI ev hbnd hroot hE hbs hbb

/-! ## `occ_any_mentions_block` -/

/-- **`KernelModeled::occ_any_mentions_block`** at the one block `B` is `mentionsList`. -/
theorem occ_any_mentions_block_spec {κ : _root_.Address → KKey} {root : List (Call F)}
    {Vf : FlatView} {B : _root_.Address} (occ_mentions_block : OccMentionsSpecIn root κ Vf B) :
    ∀ (es : List KExpr) {xes xbs r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
      {bb : Bytes.Address},
      ObsFn W "KernelModeled::occ_any_mentions_block" [xes, xbs] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
      RepList kexprListEnum (TmOExact κ) h es xes →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h [bb] xbs → ixAddr bb = B →
      ∃ b : Bool, mentionsList Vf B es = some b ∧ r = .field (if b then 1 else 0) := by
  intro es
  induction es with
  | nil =>
    intro xes xbs r h h' cs bb ev hbnd hroot hes hbs hbb
    match Obs.«KernelModeled::occ_any_mentions_block».obs ev with
    | .Nil (he_szuveosd := hr) .. => exact ⟨false, rfl, by simp [hr]⟩
    | .Cons_n1 (ld_bolbylmd := ld) .. | .Cons_other (ld_bolbylmd := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e es ih =>
    intro xes xbs r h h' cs bb ev hbnd hroot hes hbs hbb
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelModeled::occ_any_mentions_block».obs ev with
    | .Nil (ld_bolbylmd := ld) .. =>
      cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons_n1 (ld_bolbylmd := ld) (ev_bibwviky := ev1) (he_gwkmofqm := hr)
        (hc_gsysyyvr := hc) .. =>
      obtain ⟨z, zs, hzs, hz, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      obtain ⟨b, hb, hv⟩ := occ_mentions_block ev1 (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hz hbs hbb
      obtain rfl := bit_eq_one hv.symm
      exact ⟨true, by simp [mentionsList, orB, hb], by simp [hr]⟩
    | .Cons_other (ld_bolbylmd := ld) (ev_bibwviky := ev1) (hne_ubqoerny := hne)
        (ev_cpwcgvda := ev2) (hc_tmxzbzju := hc) .. =>
      obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      obtain ⟨b, hb, hv⟩ := occ_mentions_block ev1 (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hz hbs hbb
      subst hv
      obtain rfl := bit_ne_one hne
      obtain ⟨b', hb', hr⟩ := ih ev2 (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc']))
        (tmOExactList_mono ev1.heap_extends hzs')
        (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
          ev1.heap_extends hbs) hbb
      exact ⟨b', by simp [mentionsList, orB, hb, hb'], hr⟩

/-! ## `aux_count` -/

/-- **`KernelModeled::aux_count(flat)`** counts the auxiliary entries; no allocation. -/
theorem aux_count_spec {κ : _root_.Address → KKey} {root : List (Call F)} :
    ∀ (es : List FlatEntry) {xflat r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelModeled::aux_count" [xflat] h r h' cs → (∀ c ∈ cs, c ∈ root) →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      r = .field ((es.countP (·.aux) : Nat) : F) ∧ h' = h := by
  intro es
  induction es with
  | nil =>
    intro xflat r h h' cs ev hroot hes
    match Obs.«KernelModeled::aux_count».obs ev with
    | .Nil (he20 := hr) (he21 := hh) .. => exact ⟨by simp [hr], hh⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e es ih =>
    intro xflat r h h' cs ev hroot hes
    match Obs.«KernelModeled::aux_count».obs ev with
    | .Nil (ld12 := ld) .. =>
      cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons (ld12 := ld) (ev92 := ev1) (he102 := hh) (op86 := op) (hc103 := hc) .. =>
      obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      obtain ⟨xa, xps, xls, a, htup, -, -, -, -⟩ := hz
      injection htup with hl
      injection hl with _ hl
      injection hl with h2 _
      subst h2
      obtain ⟨hx, hm⟩ := ih ev1 (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hzs'
      subst hx hm
      refine ⟨?_, hh⟩
      simp only [evalBinOp] at op
      injection op with hv
      rw [← hv]
      cases haux : e.aux <;> simp [List.countP_cons, haux]

/-! ## `occ_scan`, `occ_scan_list` -/

/-- The one-block list `occ_scan` allocates. -/
theorem blocks_rep {h : Heap F} {xblock : SourceValue F} {bb : Bytes.Address}
    (hblock : Bytes.RepAddressRef addrTy h bb xblock) :
    RepList addrListEnum (Bytes.RepAddressRef addrTy)
      ((h ++ [(.construct addrListEnum "Nil" [] : SourceValue F)]) ++
        [.construct addrListEnum "Cons" [xblock, .ptr (.enum addrListEnum) h.length]])
      [bb] (.ptr (.enum addrListEnum)
        (h ++ [(.construct addrListEnum "Nil" [] : SourceValue F)]).length) :=
  Lib.rep_store_cons (Bytes.repAddressRef_heapMono₂ addrTy)
    (Bytes.repAddressRef_heapMono₂ addrTy (Heap.Extends.snoc _ _) hblock) (Lib.rep_store_nil h)

/-- **`occ_scan`'s test of a nested occurrence** is `nestedAt`: the inductive is outside the
block, applied to at least its parameters, and its parameters mention the block. -/
theorem occ_scan_nested_seg {κ : _root_.Address → KKey} {root : List (Call F)} {Vf : FlatView}
    {B : _root_.Address} (occ_mentions_block : OccMentionsSpecIn root κ Vf B)
    {info : IndInfo} {args : List KExpr}
    {xcblk xc xus xhead xargs xblocks xblock xe xd xacc v : SourceValue F} {m m' : Heap F}
    {cs : List (Call F)} {ba bb : Bytes.Address}
    (sg : Obs.«KernelModeled::occ_scan».Seg1 (.field (info.np : F)) xcblk xc xus xhead xargs
      xblocks xblock xe xd xacc m v m' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hnp : info.np < 72057594037927936)
    (rba : Bytes.RepAddressRef addrTy m ba xcblk) (hba : ixAddr ba = info.blk)
    (hblock : Bytes.RepAddressRef addrTy m bb xblock) (hbb : ixAddr bb = B)
    (hargs : RepList kexprListEnum (TmOExact κ) m args xargs)
    (hblocks : RepList addrListEnum (Bytes.RepAddressRef addrTy) m [bb] xblocks) :
    Heap.Extends m m' ∧ ∃ b : Bool, nestedAt Vf B info args = some b ∧
      v = .field (if b then 1 else 0) := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  cases sg with
  | n1 m255 cs266 ev268 he289 he290 hc291 =>
    subst he289 he290
    obtain ⟨hv, rfl⟩ := Lib.address_eq_spec ev268 rba hblock
    have hab : ba = bb := by
      by_contra hne
      rw [ite_eq_right hne] at hv
      exact absurd (Value.field.inj hv) (by decide)
    refine ⟨Heap.Extends.refl _, false, ?_, by simp⟩
    have hblk : (info.blk == B) = true := by rw [← hba, ← hbb, hab]; simp
    unfold nestedAt
    simp [hblk]
  | other_n1 v254 m255 cs266 m297 cs308 v311 m314 cs322 ev268 hne292 ev324 ev310 he344 he345
      hc346 =>
    subst he344 he345
    obtain ⟨hv, rfl⟩ := Lib.address_eq_spec ev268 rba hblock
    obtain ⟨rfl, rfl⟩ := kexpr_length ev324 hargs
    have hlen : args.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbnd
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [xargs], m314⟩)
        (by rw [hc346]; simp) (by simp) hargs
    obtain ⟨hiff, rfl⟩ := ltf_nat (by omega) (by omega) ev310
    have hlt : args.length < info.np := hiff.mp rfl
    refine ⟨Heap.Extends.refl _, false, ?_, by simp⟩
    unfold nestedAt
    simp [hlt]
  | other_other v254 m255 cs266 v296 m297 cs308 v311 m314 cs322 cs_any v_take m360 cs368 ev268
      hne292 ev324 ev310 hne347 ev370 ev_any hc394 =>
    obtain ⟨hv, rfl⟩ := Lib.address_eq_spec ev268 rba hblock
    subst hv
    have hab : ba ≠ bb := fun hab => hne292 (by rw [ite_eq_left hab])
    have hblk : (info.blk == B) = false := by
      rw [← hba, ← hbb]
      exact beq_eq_false_iff_ne.mpr fun heq => hab (ixAddr_inj heq)
    obtain ⟨rfl, rfl⟩ := kexpr_length ev324 hargs
    have hlen : args.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbnd
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [xargs], m314⟩)
        (by rw [hc394]; simp) (by simp) hargs
    obtain ⟨hiff, rfl⟩ := ltf_nat (by omega) (by omega) ev310
    have hnlt : ¬ args.length < info.np := fun hlt => hne347 (hiff.mpr hlt)
    have htk := kexpr_take ev370 hargs
    rw [fval_natCast (by omega)] at htk
    obtain ⟨b, hb, hr⟩ := occ_any_mentions_block_spec occ_mentions_block _ ev_any
      (sub fun c hc' => by rw [hc394]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc394]; simp [hc'])) htk
      (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
        ev370.heap_extends hblocks) hbb
    refine ⟨ev370.heap_extends.trans ev_any.heap_extends, b, ?_, hr⟩
    unfold nestedAt
    simp [hblk, hnlt, hb]

mutual

/-- **`KernelModeled::occ_scan(block, e, d, acc)`** is `occScanF` at every large enough fuel:
the nested occurrences of the term, under `d` binders, added to the entries (stepping through
any `Let` cells). -/
theorem occ_scan_spec {κ : _root_.Address → KKey} {root : List (Call F)} {Vf : FlatView}
    {B : _root_.Address} (hA : FlatAddrOf κ Vf) (hI : FlatIndAnswersIn root Vf)
    (hMem : FlatMembersAnswersIn root Vf) (occ_mentions_block : OccMentionsSpecIn root κ Vf B)
    (aux_entry_in : AuxEntryInSpecIn root κ) (hdepth : ScanDepthIn root)
    {E : KExpr} {d : Nat} {acc : List FlatEntry} {xblock xe xacc r : SourceValue F}
    {bb : Bytes.Address} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelModeled::occ_scan" [xblock, xe, .field (d : F), xacc] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hd : d < 4611686018427387904)
    (hblock : Bytes.RepAddressRef addrTy h bb xblock) (hbb : ixAddr bb = B)
    (hE : TmOExact κ h E xe)
    (hacc : RepList flatListEnum (FlatEntryRepExact κ) h acc xacc) :
    Heap.Extends h h' ∧ ∃ acc', RepList flatListEnum (FlatEntryRepExact κ) h' acc' r ∧
      Eventually fun n => occScanF Vf B n E d acc = some acc' := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  have pre : ∀ {m2 m26 m39 : Heap F} {v38 : SourceValue F} {cs0 : List (Call F)},
      m2 = (m26 ++ [(.construct addrListEnum "Cons"
        [xblock, (.ptr (.enum addrListEnum) (h).length)])]) →
      m26 = (h ++ [(.construct addrListEnum "Nil" [])]) →
      ObsFn W "KernelModeled::occ_mentions_block"
        [xe, (.ptr (.enum addrListEnum) (m26).length)] m2 v38 m39 cs0 →
      (∀ c ∈ cs0, c ∈ cs) →
      Heap.Extends h m39 ∧
        RepList addrListEnum (Bytes.RepAddressRef addrTy) m39 [bb]
          (.ptr (.enum addrListEnum) m26.length) ∧
        ∃ b : Bool, mentions Vf B E = some b ∧ v38 = .field (if b then 1 else 0) := by
    intro m2 m26 m39 v38 cs0 hm12 hm34 evm hsub
    subst hm12
    subst hm34
    have ext0 : Heap.Extends h ((h ++ [(.construct addrListEnum "Nil" [] : SourceValue F)]) ++
        [.construct addrListEnum "Cons" [xblock, .ptr (.enum addrListEnum) h.length]]) :=
      (Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)
    have hbl := blocks_rep hblock
    obtain ⟨b, hb, hv⟩ := occ_mentions_block evm (sub hsub) (fun c hc' => hroot c (hsub c hc'))
      (hE.mono ext0) hbl hbb
    exact ⟨ext0.trans evm.heap_extends,
      repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) evm.heap_extends hbl,
      b, hb, hv⟩
  match Obs.«KernelModeled::occ_scan».obs ev with
  | .n0 (cs_ejheattv := cs0) (hm12 := hm12) (hm34 := hm34) (ev_yanxknqt := evm) (he74 := hr)
      (he75 := hh) (hc76 := hc) .. =>
    obtain ⟨ext0, -, b, hb, hv⟩ := pre hm12 hm34 evm (fun c hc' => by rw [hc]; simp [hc'])
    subst hr hh
    obtain rfl := bit_eq_zero hv.symm
    exact ⟨ext0, acc, flatList_mono ext0 hacc, 1, fun f hf => by
      obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
      simp only [occScanF, hb]⟩
  | .other_App_Const_Induct_n1 (m39 := m39) (cs_ejheattv := cs0) (m113 := m113)
      (cs_lffdlqmw := cssp) (x_head := xhead) (x_args := xargs) (x_c := xc) (x_us := xus)
      (m177 := m177) (p185 := pci) (cs191 := csci) (x_cnp := xcnp) (x_cblk := xcblk)
      (m396 := m396) (cs398 := csseg) (cs421 := csabm) (v424 := vms) (v425 := vsp)
      (m429 := m429) (cs437 := csbfo) (m456 := m456) (cs464 := csopl) (v467 := vtake)
      (m470 := m470) (cs478 := cstake) (hm12 := hm12) (hm34 := hm34) (ev_yanxknqt := evm)
      (hne77 := hne) (ld92 := ld) (ev_catkzrqk := evsp) (ld158 := ldh) (ev193 := evci)
      (ld187 := ldci) (sg403 := sg) (ev439 := evbfo) (ev480 := evtake) (ev466 := evopl)
      (ev423 := evabm) (hc518 := hc) .. =>
    obtain ⟨ext0, hbl, b, hb, hv⟩ := pre hm12 hm34 evm (fun c hc' => by rw [hc]; simp [hc'])
    subst hv
    obtain rfl := bit_ne_zero hne
    obtain ⟨Ef, Ea, rfl, -, -⟩ := TmOExact.app_of_load (hE.mono ext0) ld
    obtain ⟨hfn, hnl, hargs⟩ := collect_spine_zeta_spec (hE.mono ext0)
      (sub fun c hc' => by rw [hc]; simp [hc']) evsp
    obtain ⟨ca, us, hfn_eq, rca, rus⟩ := TmOExact.const_of_load hfn ldh
    obtain ⟨info, ba, hci, hnp, hnct, hidx, rfl, -, hba, rba, -⟩ :=
      (hI rca evci (hroot _ (by rw [hc]; simp))
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ldci).1 _ _ _ _ _ _ _ _ rfl
    have ext1 := evsp.heap_extends
    have ext2 := evci.heap_extends
    have mb : ∀ {m : Heap F}, Heap.Extends h m → Bytes.RepAddressRef addrTy m bb xblock :=
      fun e => Bytes.repAddressRef_heapMono₂ addrTy e hblock
    obtain ⟨ext3, b', hnest, hv'⟩ := occ_scan_nested_seg occ_mentions_block sg
      (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hnp rba hba
      (mb (ext0.trans (ext1.trans ext2))) hbb (tmOExactList_mono ext2 hargs)
      (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
        (ext1.trans ext2) hbl)
    obtain rfl := bit_eq_one hv'.symm
    obtain ⟨ms, hms, hrms⟩ := hMem (Bytes.repAddressRef_heapMono₂ addrTy ext3 rba) evbfo
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hci hba
    have ext4 := evbfo.heap_extends
    have htk := kexpr_take evtake (tmOExactList_mono (ext2.trans (ext3.trans ext4)) hargs)
    rw [fval_natCast (by omega)] at htk
    have ext5 := evtake.heap_extends
    obtain ⟨ext6, sp, hsp, hrsp⟩ := occ_params_lower_spec hd _ evopl
      (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) htk
    have extA : Heap.Extends h m456 :=
      ext0.trans (ext1.trans (ext2.trans (ext3.trans (ext4.trans (ext5.trans ext6)))))
    obtain ⟨ext7, hres⟩ := add_block_members_spec aux_entry_in ms evabm
      (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      (repList_heapMono₂ flatListEnum memberAddrRep_heapMono₂ (ext5.trans ext6) hrms) hrsp
      (rus.mono (ext2.trans (ext3.trans (ext4.trans (ext5.trans ext6)))))
      (flatList_mono extA hacc)
    exact ⟨extA.trans ext7, _, hres, 1, fun f hf => by
      obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
      simp only [occScanF, hb, appCase, hfn_eq, constOf, hA (ixAddr ca), hci, hnest, hms, hsp]⟩
  | .other_App_Const_Induct_other (m39 := m39) (cs_ejheattv := cs0) (m113 := m113)
      (cs_lffdlqmw := cssp) (x_head := xhead) (x_args := xargs) (x_c := xc) (x_us := xus)
      (m177 := m177) (p185 := pci) (cs191 := csci) (x_cnp := xcnp) (x_cblk := xcblk)
      (v395 := vn) (m396 := m396) (cs398 := csseg) (cs526 := cs2) (hm12 := hm12)
      (hm34 := hm34) (ev_yanxknqt := evm) (hne77 := hne) (ld92 := ld) (ev_catkzrqk := evsp)
      (ld158 := ldh) (ev193 := evci) (ld187 := ldci) (sg403 := sg) (hne519 := hnn)
      (ev528 := ev2) (hc561 := hc) .. =>
    obtain ⟨ext0, hbl, b, hb, hv⟩ := pre hm12 hm34 evm (fun c hc' => by rw [hc]; simp [hc'])
    subst hv
    obtain rfl := bit_ne_zero hne
    obtain ⟨Ef, Ea, rfl, -, -⟩ := TmOExact.app_of_load (hE.mono ext0) ld
    obtain ⟨hfn, hnl, hargs⟩ := collect_spine_zeta_spec (hE.mono ext0)
      (sub fun c hc' => by rw [hc]; simp [hc']) evsp
    obtain ⟨ca, us, hfn_eq, rca, rus⟩ := TmOExact.const_of_load hfn ldh
    obtain ⟨info, ba, hci, hnp, hnct, hidx, rfl, -, hba, rba, -⟩ :=
      (hI rca evci (hroot _ (by rw [hc]; simp))
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ldci).1 _ _ _ _ _ _ _ _ rfl
    have ext1 := evsp.heap_extends
    have ext2 := evci.heap_extends
    have mb : ∀ {m : Heap F}, Heap.Extends h m → Bytes.RepAddressRef addrTy m bb xblock :=
      fun e => Bytes.repAddressRef_heapMono₂ addrTy e hblock
    obtain ⟨ext3, b', hnest, hv'⟩ := occ_scan_nested_seg occ_mentions_block sg
      (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hnp rba hba
      (mb (ext0.trans (ext1.trans ext2))) hbb (tmOExactList_mono ext2 hargs)
      (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
        (ext1.trans ext2) hbl)
    subst hv'
    obtain rfl := bit_ne_one hnn
    have extA : Heap.Extends h m396 := ext0.trans (ext1.trans (ext2.trans ext3))
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨ext4, a2, ha2, n2, hn2⟩ := occ_scan_list_spec hA hI hMem occ_mentions_block
      aux_entry_in hdepth ev2 (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hd (mb extA) hbb
      (tmOExactList_mono (ext2.trans ext3) hargs) (flatList_mono extA hacc)
    exact ⟨extA.trans ext4, a2, ha2, n2 + 1, fun f hf => by
      obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
      simp only [occScanF, hb, appCase, hfn_eq, constOf, hA (ixAddr ca), hci, hnest,
        hn2 n (by omega)]⟩
  | .other_App_Const_other (m39 := m39) (cs_ejheattv := cs0) (m113 := m113)
      (cs_lffdlqmw := cssp) (x_head := xhead) (x_args := xargs) (x_c := xc) (x_us := xus)
      (m177 := m177) (p185 := pci) (cs191 := csci) (cs569 := cs2) (hm12 := hm12)
      (hm34 := hm34) (ev_yanxknqt := evm) (hne77 := hne) (ld92 := ld) (ev_catkzrqk := evsp)
      (ld158 := ldh) (ev193 := evci) (ld187 := ldci) (hne562 := hni) (ev571 := ev2)
      (hc604 := hc) .. =>
    obtain ⟨ext0, hbl, b, hb, hv⟩ := pre hm12 hm34 evm (fun c hc' => by rw [hc]; simp [hc'])
    subst hv
    obtain rfl := bit_ne_zero hne
    obtain ⟨Ef, Ea, rfl, -, -⟩ := TmOExact.app_of_load (hE.mono ext0) ld
    obtain ⟨hfn, hnl, hargs⟩ := collect_spine_zeta_spec (hE.mono ext0)
      (sub fun c hc' => by rw [hc]; simp [hc']) evsp
    obtain ⟨ca, us, hfn_eq, rca, rus⟩ := TmOExact.const_of_load hfn ldh
    have hci := (hI rca evci (hroot _ (by rw [hc]; simp))
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ldci).2 hni
    have extA : Heap.Extends h m177 := ext0.trans (evsp.heap_extends.trans evci.heap_extends)
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨ext4, a2, ha2, n2, hn2⟩ := occ_scan_list_spec hA hI hMem occ_mentions_block
      aux_entry_in hdepth ev2 (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hd
      (Bytes.repAddressRef_heapMono₂ addrTy extA hblock) hbb
      (tmOExactList_mono evci.heap_extends hargs) (flatList_mono extA hacc)
    exact ⟨extA.trans ext4, a2, ha2, n2 + 1, fun f hf => by
      obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
      simp only [occScanF, hb, appCase, hfn_eq, constOf, hA (ixAddr ca), hci,
        hn2 n (by omega)]⟩
  | .other_App_other (m39 := m39) (cs_ejheattv := cs0) (m113 := m113) (cs_lffdlqmw := cssp)
      (x_head := xhead) (x_args := xargs) (cs612 := cs2) (v618 := vacc1) (m641 := m1)
      (cs649 := cs1) (hm12 := hm12) (hm34 := hm34) (ev_yanxknqt := evm) (hne77 := hne)
      (ld92 := ld) (ev_catkzrqk := evsp) (ld158 := ldh) (hne605 := hnc) (ev651 := ev1)
      (ev614 := ev2) (hc684 := hc) .. =>
    obtain ⟨ext0, hbl, b, hb, hv⟩ := pre hm12 hm34 evm (fun c hc' => by rw [hc]; simp [hc'])
    subst hv
    obtain rfl := bit_ne_zero hne
    obtain ⟨Ef, Ea, rfl, -, -⟩ := TmOExact.app_of_load (hE.mono ext0) ld
    obtain ⟨hfn, hnl, hargs⟩ := collect_spine_zeta_spec (hE.mono ext0)
      (sub fun c hc' => by rw [hc]; simp [hc']) evsp
    have hnotc := tmOExact_not_const hfn hnl ldh hnc
    have hconst : constOf (Ix.Kernel.Expr.app Ef Ea).getAppFn = none := by
      cases hf : (Ix.Kernel.Expr.app Ef Ea).getAppFn with
      | const c ls => exact (hnotc c ls hf).elim
      | _ => rfl
    have extA : Heap.Extends h m113 := ext0.trans evsp.heap_extends
    have hlt1 : cs1.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨ext1, a1, ha1, n1, hn1⟩ := occ_scan_spec hA hI hMem occ_mentions_block
      aux_entry_in hdepth ev1 (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hd
      (Bytes.repAddressRef_heapMono₂ addrTy extA hblock) hbb hfn (flatList_mono extA hacc)
    have hlt2 : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨ext2, a2, ha2, n2, hn2⟩ := occ_scan_list_spec hA hI hMem occ_mentions_block
      aux_entry_in hdepth ev2 (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hd
      (Bytes.repAddressRef_heapMono₂ addrTy (extA.trans ext1) hblock) hbb
      (tmOExactList_mono ext1 hargs) ha1
    exact ⟨extA.trans (ext1.trans ext2), a2, ha2, max n1 n2 + 1, fun f hf => by
      obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
      simp only [occScanF, hb, appCase, hconst, hn1 n (by omega), hn2 n (by omega)]⟩
  | .other_Lam (m39 := m39) (cs_ejheattv := cs0) (x_t := xt) (x_b := xb) (cs711 := cs2)
      (v716 := vd) (v717 := vacc1) (m748 := m1) (cs756 := cs1) (hm12 := hm12) (hm34 := hm34)
      (ev_yanxknqt := evm) (hne77 := hne) (ld92 := ld) (op745 := op) (ev758 := ev1)
      (ev713 := ev2) (hc791 := hc) .. =>
    obtain ⟨ext0, -, b, hb, hv⟩ := pre hm12 hm34 evm (fun c hc' => by rw [hc]; simp [hc'])
    subst hv
    obtain rfl := bit_ne_zero hne
    obtain ⟨T, Bd, ℓ, rfl, hT, hBd, -⟩ := TmOExact.lam_of_load (hE.mono ext0) ld
    obtain rfl := binop_add_one_nat op
    have hlt1 : cs1.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨ext1, a1, ha1, n1, hn1⟩ := occ_scan_spec hA hI hMem occ_mentions_block
      aux_entry_in hdepth ev1 (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hd
      (Bytes.repAddressRef_heapMono₂ addrTy ext0 hblock) hbb hT (flatList_mono ext0 hacc)
    have hd1 : d + 1 < 4611686018427387904 := by
      have := hdepth (xb := xblock) (xe := xb) (xacc := vacc1) (d := ((d + 1 : Nat) : F))
        (h := m1) (hroot _ (by rw [hc]; simp))
      rwa [fval_natCast (by omega)] at this
    have hlt2 : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨ext2, a2, ha2, n2, hn2⟩ := occ_scan_spec hA hI hMem occ_mentions_block
      aux_entry_in hdepth ev2 (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hd1
      (Bytes.repAddressRef_heapMono₂ addrTy (ext0.trans ext1) hblock) hbb (hBd.mono ext1) ha1
    exact ⟨ext0.trans (ext1.trans ext2), a2, ha2, max n1 n2 + 1, fun f hf => by
      obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
      simp only [occScanF, hb, hn1 n (by omega), hn2 n (by omega)]⟩
  | .other_Forall (m39 := m39) (cs_ejheattv := cs0) (x_t := xt) (x_b := xb) (cs818 := cs2)
      (v823 := vd) (v824 := vacc1) (m855 := m1) (cs863 := cs1) (hm12 := hm12) (hm34 := hm34)
      (ev_yanxknqt := evm) (hne77 := hne) (ld92 := ld) (op852 := op) (ev865 := ev1)
      (ev820 := ev2) (hc898 := hc) .. =>
    obtain ⟨ext0, -, b, hb, hv⟩ := pre hm12 hm34 evm (fun c hc' => by rw [hc]; simp [hc'])
    subst hv
    obtain rfl := bit_ne_zero hne
    obtain ⟨T, Bd, ℓ, rfl, hT, hBd, -⟩ := TmOExact.forallE_of_load (hE.mono ext0) ld
    obtain rfl := binop_add_one_nat op
    have hlt1 : cs1.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨ext1, a1, ha1, n1, hn1⟩ := occ_scan_spec hA hI hMem occ_mentions_block
      aux_entry_in hdepth ev1 (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hd
      (Bytes.repAddressRef_heapMono₂ addrTy ext0 hblock) hbb hT (flatList_mono ext0 hacc)
    have hd1 : d + 1 < 4611686018427387904 := by
      have := hdepth (xb := xblock) (xe := xb) (xacc := vacc1) (d := ((d + 1 : Nat) : F))
        (h := m1) (hroot _ (by rw [hc]; simp))
      rwa [fval_natCast (by omega)] at this
    have hlt2 : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨ext2, a2, ha2, n2, hn2⟩ := occ_scan_spec hA hI hMem occ_mentions_block
      aux_entry_in hdepth ev2 (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hd1
      (Bytes.repAddressRef_heapMono₂ addrTy (ext0.trans ext1) hblock) hbb (hBd.mono ext1) ha1
    exact ⟨ext0.trans (ext1.trans ext2), a2, ha2, max n1 n2 + 1, fun f hf => by
      obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
      simp only [occScanF, hb, hn1 n (by omega), hn2 n (by omega)]⟩
  | .other_Let (m39 := m39) (cs_ejheattv := cs0) (x_v := xv) (x_b := xb) (cs924 := cs2)
      (v_bscvpeug := v') (m_zpsiogvj := m1) (cs_kvpezkmc := cs1) (hm12 := hm12)
      (hm34 := hm34) (ev_yanxknqt := evm) (hne77 := hne) (ld92 := ld) (ev_kgfsfvov := e1)
      (ev926 := ev2) (hc1041 := hc) .. =>
    obtain ⟨ext0, -, b, hb, hv⟩ := pre hm12 hm34 evm (fun c hc' => by rw [hc]; simp [hc'])
    obtain ⟨T0, V0, B0, rfl, -, hv0, hb0⟩ := TmOExact.letE_of_load (hE.mono ext0) ld
    have hv' := expr_inst1_tmOExact (sub fun c hc' => by rw [hc]; simp [hc']) hb0 hv0 e1
    have extA : Heap.Extends h m1 := ext0.trans e1.heap_extends
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨ext2, res⟩ := occ_scan_spec hA hI hMem occ_mentions_block
      aux_entry_in hdepth ev2 (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hd
      (Bytes.repAddressRef_heapMono₂ addrTy extA hblock) hbb hv' (flatList_mono extA hacc)
    exact ⟨extA.trans ext2, res⟩
  | .other_Proj (m39 := m39) (cs_ejheattv := cs0) (x_x := xx) (cs1069 := cs1) (hm12 := hm12)
      (hm34 := hm34) (ev_yanxknqt := evm) (hne77 := hne) (ld92 := ld) (ev1071 := ev1)
      (hc1104 := hc) .. =>
    obtain ⟨ext0, -, b, hb, hv⟩ := pre hm12 hm34 evm (fun c hc' => by rw [hc]; simp [hc'])
    subst hv
    obtain rfl := bit_ne_zero hne
    obtain ⟨pa, pi, Es, rfl, rfl, -, hEs⟩ := TmOExact.proj_of_load (hE.mono ext0) ld
    have hlt : cs1.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨ext1, a1, ha1, n1, hn1⟩ := occ_scan_spec hA hI hMem occ_mentions_block
      aux_entry_in hdepth ev1 (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hd
      (Bytes.repAddressRef_heapMono₂ addrTy ext0 hblock) hbb hEs (flatList_mono ext0 hacc)
    exact ⟨ext0.trans ext1, a1, ha1, n1 + 1, fun f hf => by
      obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
      simp only [occScanF, hb, hn1 n (by omega)]⟩
  | .other_other (m39 := m39) (cs_ejheattv := cs0) (v81 := v81) (hm12 := hm12) (hm34 := hm34)
      (ev_yanxknqt := evm) (hne77 := hne) (ld92 := ld) (hne685 := hnApp) (hne792 := hnLam)
      (hne899 := hnAll) (hne1042 := hnLet) (hne1105 := hnProj) (he1110 := hr) (he1111 := hh)
      (hc1112 := hc) .. =>
    obtain ⟨ext0, -, b, hb, hv⟩ := pre hm12 hm34 evm (fun c hc' => by rw [hc]; simp [hc'])
    subst hv hr hh
    obtain rfl := bit_ne_zero hne
    have hacc' := flatList_mono ext0 hacc
    obtain ⟨k, ht⟩ := hE.mono ext0
    have fin : ∀ {P : Prop}, (∀ n, P) → P := fun hP => hP 0
    cases ht with
    | bvarFree _ _ _ hd0 => omega
    | app cell _ _ =>
      have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
      exact (hnApp _ rfl hv).elim
    | lam cell _ _ _ =>
      have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
      exact (hnLam _ rfl hv).elim
    | forallE cell _ _ _ =>
      have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
      exact (hnAll _ rfl hv).elim
    | letE cell _ _ _ =>
      have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
      exact (hnLet _ rfl hv).elim
    | proj cell _ _ =>
      have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
      exact (hnProj _ rfl hv).elim
    | _ =>
      exact ⟨ext0, acc, hacc', 1, fun f hf => by
        obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
        simp only [occScanF, hb]⟩
termination_by cs.length

/-- **`KernelModeled::occ_scan_list(block, es, d, acc)`** is `scanList` over `occScanF` at
every large enough fuel. -/
theorem occ_scan_list_spec {κ : _root_.Address → KKey} {root : List (Call F)} {Vf : FlatView}
    {B : _root_.Address} (hA : FlatAddrOf κ Vf) (hI : FlatIndAnswersIn root Vf)
    (hMem : FlatMembersAnswersIn root Vf) (occ_mentions_block : OccMentionsSpecIn root κ Vf B)
    (aux_entry_in : AuxEntryInSpecIn root κ) (hdepth : ScanDepthIn root)
    {es : List KExpr} {d : Nat} {acc : List FlatEntry} {xblock xes xacc r : SourceValue F}
    {bb : Bytes.Address} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelModeled::occ_scan_list" [xblock, xes, .field (d : F), xacc] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hd : d < 4611686018427387904)
    (hblock : Bytes.RepAddressRef addrTy h bb xblock) (hbb : ixAddr bb = B)
    (hes : RepList kexprListEnum (TmOExact κ) h es xes)
    (hacc : RepList flatListEnum (FlatEntryRepExact κ) h acc xacc) :
    Heap.Extends h h' ∧ ∃ acc', RepList flatListEnum (FlatEntryRepExact κ) h' acc' r ∧
      Eventually fun n => scanList (fun x acc => occScanF Vf B n x d acc) es acc = some acc' := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  match Obs.«KernelModeled::occ_scan_list».obs ev with
  | .Nil (ld12 := ld) (he21 := hr) (he22 := hh) .. =>
    subst hr hh
    obtain rfl := IxVM.Refinement.Core.RepList.nil_of_load hes ld
    exact ⟨Heap.Extends.refl _, acc, hacc, 0, fun f _ => rfl⟩
  | .Cons (x_x := xx) (x_rest := xrest) (cs44 := cs2) (v50 := vacc1) (m73 := m1) (cs81 := cs1)
      (ld12 := ld) (ev83 := ev1) (ev46 := ev2) (hc116 := hc) =>
    obtain ⟨z, zs, rfl, hz, hzs⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
    have hlt1 : cs1.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨ext1, a1, ha1, n1, hn1⟩ := occ_scan_spec hA hI hMem occ_mentions_block
      aux_entry_in hdepth ev1 (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hd hblock hbb hz hacc
    have hlt2 : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨ext2, a2, ha2, n2, hn2⟩ := occ_scan_list_spec hA hI hMem occ_mentions_block
      aux_entry_in hdepth ev2 (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hd
      (Bytes.repAddressRef_heapMono₂ addrTy ext1 hblock) hbb (tmOExactList_mono ext1 hzs) ha1
    exact ⟨ext1.trans ext2, a2, ha2, max n1 n2, fun f hf => by
      simp only [scanList, hn1 f (by omega), hn2 f (by omega)]⟩
termination_by cs.length

end

/-! ## `ctors_scan` -/

/-- **`KernelModeled::ctors_scan`** from constructor `c` is `ctorsLoop` over the constructors
`c, …, nctors - 1` of one entry: each constructor's type at the entry's levels, past the
parameters or with the parameters instantiated, scanned. -/
theorem ctors_scan_spec {κ : _root_.Address → KKey} {root : List (Call F)}
    {S : _root_.Address → Prop} {Vf : FlatView} {B : _root_.Address}
    (hA : FlatAddrOf κ Vf) (hI : FlatIndAnswersIn root Vf)
    (hC : FlatCtorAnswersIn root S κ Vf) (hMem : FlatMembersAnswersIn root Vf)
    (occ_mentions_block : OccMentionsSpecIn root κ Vf B)
    (aux_entry_in : AuxEntryInSpecIn root κ) (hdepth : ScanDepthIn root)
    {info : IndInfo} {aux : Bool} {sp : List KExpr} {us : List KLevel}
    (hnp : info.np < 72057594037927936) (hidx : info.idx < 72057594037927936)
    (hnct : info.nctors < 72057594037927936) (hS : S info.blk) :
    ∀ (k : Nat) {c : Nat} {acc : List FlatEntry} {xblock xmblk xsp xus xacc r : SourceValue F}
      {bb bm : Bytes.Address} {h h' : Heap F} {cs : List (Call F)},
      c + k = info.nctors →
      ObsFn W "KernelModeled::ctors_scan"
        [xblock, xmblk, .field (info.idx : F), .field (info.nctors : F), .field (c : F),
          .field (info.np : F), auxVal aux, xsp, xus, xacc] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
      Bytes.RepAddressRef addrTy h bb xblock → ixAddr bb = B →
      Bytes.RepAddressRef addrTy h bm xmblk → ixAddr bm = info.blk →
      RepList kexprListEnum (TmOExact κ) h sp xsp → RepKLevelList h us xus →
      RepList flatListEnum (FlatEntryRepExact κ) h acc xacc →
      Heap.Extends h h' ∧ ∃ acc', RepList flatListEnum (FlatEntryRepExact κ) h' acc' r ∧
        ctorsLoop Vf B info aux sp us (List.range' c k) acc = some acc' := by
  intro k
  induction k with
  | zero =>
    intro c acc xblock xmblk xsp xus xacc r bb bm h h' cs hck ev hbnd hroot hblock hbb hbm hbmB
      hsp hus hacc
    match Obs.«KernelModeled::ctors_scan».obs ev with
    | .n0 (he25 := hr) (he26 := hh) .. =>
      subst hr hh
      exact ⟨Heap.Extends.refl _, acc, hacc, rfl⟩
    | .other (op17 := op) (hne28 := hne) .. =>
      exact absurd (by omega) (binop_sub_ne_nat op hne)
  | succ k ih =>
    intro c acc xblock xmblk xsp xus xacc r bb bm h h' cs hck ev hbnd hroot hblock hbb hbm hbmB
      hsp hus hacc
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelModeled::ctors_scan».obs ev with
    | .n0 (op17 := op) .. =>
      have := binop_sub_eq_zero_nat (by omega) (by omega) op
      omega
    | .other (m33 := m33) (p41 := pc) (cs47 := csc) (x_cty := xcty) (v127 := vt) (m128 := m128)
        (cs138 := csl) (v221 := vbody) (m222 := m222) (cs224 := csseg) (cs233 := csrec)
        (v240 := vc1) (v245 := vacc1) (m318 := m318) (cs326 := csocc) (ev49 := evc)
        (ld43 := ldc) (ev140 := evl) (sg229 := sg) (op287 := opc) (ev328 := evocc)
        (ev235 := evrec) (hc360 := hc) .. =>
      obtain ⟨ty, hty, rty⟩ := hC hbm evc (fun c hc' => hroot c (by rw [hc]; simp [hc']))
        (by rw [hbmB]; exact hS) hidx (by omega) ldc _ _ _ _ _ _ _ _ rfl
      rw [hbmB] at hty
      have ext1 := evc.heap_extends
      have rT := expr_inst_levels_tmOExact (sub fun c hc' => by rw [hc]; simp [hc']) rty
        (hus.mono ext1) evl
      have ext2 := evl.heap_extends
      have hseg : Heap.Extends m128 m222 ∧ ∃ body,
          ctorBody aux info.np sp (exprInstLevels us ty) = some body ∧
          TmOExact κ m222 body vbody := by
        cases sg with
        | n0 cs_p hv170 ev_p hc193 =>
          obtain rfl := auxVal_eq_zero.mp hv170
          obtain ⟨Bd, hpeel, hB⟩ := peel_n_foralls_zeta_spec info.np (by omega) rT
            (sub fun c hc' => by rw [hc, hc193]; simp [hc']) ev_p
          exact ⟨ev_p.heap_extends, Bd, hpeel, hB⟩
        | other cs201 hne194 ev203 hc220 =>
          have haux : aux = true := by
            cases aux
            · exact (hne194 (auxVal_eq_zero.mpr rfl)).elim
            · rfl
          subst haux
          exact inst_ctor_params_spec ev203
            (sub fun c hc' => by rw [hc, hc220]; simp [hc'])
            (fun c hc' => hroot c (by rw [hc, hc220]; simp [hc'])) rT
            (tmOExactList_mono (ext1.trans ext2) hsp)
      obtain ⟨ext3, body, hbody, rbody⟩ := hseg
      have extA : Heap.Extends h m222 := ext1.trans (ext2.trans ext3)
      have evocc' : ObsFn W "KernelModeled::occ_scan"
          [xblock, vbody, .field ((0 : Nat) : F), xacc] m222 vacc1 m318 csocc := by
        simpa using evocc
      obtain ⟨ext4, a1, ha1, n1, hn1⟩ := occ_scan_spec hA hI hMem occ_mentions_block
        aux_entry_in hdepth evocc' (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) (by decide)
        (Bytes.repAddressRef_heapMono₂ addrTy extA hblock) hbb rbody (flatList_mono extA hacc)
      have hscan : occScanF Vf B (exprSize body + 1) body 0 acc = some a1 := by
        rw [occScanF_fuel Vf B (exprSize body + 1) (max n1 (exprSize body + 1)) body (by omega)
          (by omega) 0 acc]
        exact hn1 _ (Nat.le_max_left _ _)
      obtain rfl := binop_add_one_nat opc
      have extB : Heap.Extends h m318 := extA.trans ext4
      obtain ⟨ext5, acc', hacc', hloop⟩ := ih (c := c + 1) (by omega) evrec
        (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc']))
        (Bytes.repAddressRef_heapMono₂ addrTy extB hblock) hbb
        (Bytes.repAddressRef_heapMono₂ addrTy extB hbm) hbmB
        (tmOExactList_mono extB hsp) (hus.mono extB) ha1
      refine ⟨extB.trans ext5, acc', hacc', ?_⟩
      simp only [List.range'_succ, ctorsLoop, ctorScan, hty, hbody, hscan]
      exact hloop

/-! ## `nested_walk` -/

/-- **`KernelModeled::nested_walk(block, acc, i)`** is `nestedWalk` at some fuel of steps: the
constructors of entry `i` onwards scanned, each new entry appended. The returned list
represents exactly the model's. -/
theorem nested_walk_spec {κ : _root_.Address → KKey} {root : List (Call F)}
    {S : _root_.Address → Prop} {Vf : FlatView} {B : _root_.Address}
    (hA : FlatAddrOf κ Vf) (hI : FlatIndAnswersIn root Vf)
    (hC : FlatCtorAnswersIn root S κ Vf) (hMem : FlatMembersAnswersIn root Vf)
    (occ_mentions_block : OccMentionsSpecIn root κ Vf B)
    (aux_entry_in : AuxEntryInSpecIn root κ) (hdepth : ScanDepthIn root)
    (hS : ∀ a d, Vf.ci a = some (some d) → S d.blk)
    {i : Nat} {acc : List FlatEntry} {xblock xacc r : SourceValue F} {bb : Bytes.Address}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelModeled::nested_walk" [xblock, xacc, .field (i : F)] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hi : i ≤ acc.length)
    (hblock : Bytes.RepAddressRef addrTy h bb xblock) (hbb : ixAddr bb = B)
    (hacc : RepList flatListEnum (FlatEntryRepExact κ) h acc xacc) :
    Heap.Extends h h' ∧ ∃ es, RepList flatListEnum (FlatEntryRepExact κ) h' es r ∧
      ∃ n, nestedWalk Vf B n i acc = some es := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  match Obs.«KernelModeled::nested_walk».obs ev with
  | .n0 (x10 := x10) (m12 := m12) (cs21 := cs0) (ev23 := evlen) (op17 := op) (he38 := hr)
      (he39 := hh) (hc40 := hc) =>
    have hlen : acc.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbnd
        (c := ⟨Obs.Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>», [xacc], h⟩)
        (by rw [hc]; simp) (by simp) hacc
    obtain ⟨rfl, rfl⟩ := flat_length evlen hacc
    subst hr hh
    have heq := binop_sub_eq_zero_nat (by omega) (by omega) op
    have hnone : acc[i]? = none := by rw [← heq]; simp
    exact ⟨Heap.Extends.refl _, acc, hacc, 1, by simp only [nestedWalk, hnone]⟩
  | .other (x10 := x10) (m12 := m12) (cs21 := cs0) (m46 := m46) (cs56 := cslk) (x_addr := xaddr)
      (x_is_aux := xaux) (x_sp := xsp) (x_us := xus) (m99 := m99) (p107 := pci)
      (cs113 := csci) (x_np := xnp) (x_nctors := xnct) (x_mblk := xmblk) (x_midx := xmidx)
      (cs177 := csrec) (v181 := vacc1) (v182 := vi1) (m191 := m191) (cs199 := csctors)
      (ev23 := evlen) (op17 := op) (hne41 := hne) (ev58 := evlk) (ev115 := evci)
      (ld109 := ldci) (ev201 := evctors) (op294 := opi) (ev179 := evrec) (hc296 := hc) .. =>
    have hlen : acc.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbnd
        (c := ⟨Obs.Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>», [xacc], h⟩)
        (by rw [hc]; simp) (by simp) hacc
    obtain ⟨rfl, rfl⟩ := flat_length evlen hacc
    have hnei : acc.length ≠ i := binop_sub_ne_nat op hne
    obtain ⟨⟨e, hget, he⟩, rfl⟩ := flat_lookup evlk hacc
    rw [fval_natCast (by omega)] at hget
    obtain ⟨xa, xps, xls, a, htup, ra, hae, hps, hls⟩ := he
    injection htup with hl
    injection hl with h1 hl
    injection hl with h2 hl
    injection hl with h3 hl
    injection hl with h4 _
    subst h1 h2 h3 h4
    obtain ⟨info, bm, hci, hnp, hnct, hidx, rfl, rfl, hbm, rbm, rfl⟩ :=
      (hI ra evci (hroot _ (by rw [hc]; simp))
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ldci).1 _ _ _ _ _ _ _ _ rfl
    rw [hae] at hci
    have ext1 := evci.heap_extends
    have evctors' : ObsFn W "KernelModeled::ctors_scan"
        [xblock, xmblk, .field (info.idx : F), .field (info.nctors : F), .field ((0 : Nat) : F),
          .field (info.np : F), auxVal e.aux, xsp, xus, xacc] m99 vacc1 m191 csctors := by
      simpa using evctors
    obtain ⟨ext2, a1, ha1, hloop⟩ := ctors_scan_spec hA hI hC hMem occ_mentions_block
      aux_entry_in hdepth hnp hidx hnct (hS _ _ hci) info.nctors (c := 0) (by omega) evctors'
      (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      (Bytes.repAddressRef_heapMono₂ addrTy ext1 hblock) hbb rbm hbm
      (tmOExactList_mono ext1 hps) (hls.mono ext1) (flatList_mono ext1 hacc)
    have hctors : ctorsScan Vf B info e.aux e.params e.levels acc = some a1 := by
      unfold ctorsScan
      rw [List.range_eq_range']
      exact hloop
    have hpre := (ctorsLoop_prefix Vf B info e.aux e.params e.levels _ acc a1 hloop).length_le
    obtain rfl := binop_add_one_nat opi
    have hlt : csrec.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨ext3, es, hes, n, hn⟩ := nested_walk_spec hA hI hC hMem occ_mentions_block
      aux_entry_in hdepth hS evrec (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) (by omega)
      (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ext2) hblock) hbb ha1
    exact ⟨ext1.trans (ext2.trans ext3), es, hes, n + 1, by
      simp only [nestedWalk, hget, hci, hctors]
      exact hn⟩
termination_by cs.length

/-! ## `aux_already_in` (the record side's membership test) -/

theorem prop_bit_mul {p q : Prop} [Decidable p] [Decidable q] {v : SourceValue F}
    (op : evalBinOp .mul (.field (if p then 1 else 0) : SourceValue F)
      (.field (if q then 1 else 0)) = .ok v) :
    v = .field (if p ∧ q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, evalBinOp] at op ⊢ <;> exact op.symm

theorem auxEntryIn_cons (e : FlatEntry) (es : List FlatEntry) (a : _root_.Address)
    (sp : List KExpr) (us : List KLevel) :
    auxEntryIn (e :: es) a sp us =
      ((e.aux && e.addr == a && e.params == sp && e.levels == us) || auxEntryIn es a sp us) := by
  simp [auxEntryIn]

/-- **`KernelCheck::aux_already_in(flat, addr, sp, us)`** decides `auxEntryIn` when `κ` is
injective: an auxiliary entry with the type, structurally the parameters and the levels. -/
theorem aux_already_in_spec {κ : _root_.Address → KKey} (hinj : Function.Injective κ)
    {root : List (Call F)} :
    ∀ (es : List FlatEntry) {a : Bytes.Address} {sp : List KExpr} {us : List KLevel}
      {xflat xa xsp xus r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelCheck::aux_already_in" [xflat, xa, xsp, xus] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      Bytes.RepAddressRef addrTy h a xa →
      RepList kexprListEnum (TmOExact κ) h sp xsp → RepKLevelList h us xus →
      r = .field (if auxEntryIn es (ixAddr a) sp us then 1 else 0) := by
  intro es
  induction es with
  | nil =>
    intro a sp us xflat xa xsp xus r h h' cs ev hbnd hroot hes ra hsp hus
    match Obs.«KernelCheck::aux_already_in».obs ev with
    | .Nil (he20 := hr) .. => rw [hr]; rfl
    | .Cons_n1_n1_n1 (ld12 := ld) .. | .Cons_n1_n1_other (ld12 := ld) ..
    | .Cons_n1_other (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e es ih =>
    intro a sp us xflat xa xsp xus r h h' cs ev hbnd hroot hes ra hsp hus
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    have entry : ∀ {xaddr xaux xps xou xrest : SourceValue F},
        loadValue h xflat = .ok (.construct flatListEnum "Cons"
          [(.tuple [xaddr, xaux, xps, xou]), xrest]) →
        xaux = auxVal e.aux ∧ (∃ ae : Bytes.Address, Bytes.RepAddressRef addrTy h ae xaddr ∧
          ixAddr ae = e.addr) ∧ RepList kexprListEnum (TmOExact κ) h e.params xps ∧
          RepKLevelList h e.levels xou ∧
          RepList flatListEnum (FlatEntryRepExact κ) h es xrest := by
      intro xaddr xaux xps xou xrest ld
      obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      obtain ⟨xa', xps', xls', ae, htup, rae, hae, hps, hls⟩ := hz
      injection htup with hl
      injection hl with h1 hl
      injection hl with h2 hl
      injection hl with h3 hl
      injection hl with h4 _
      subst h1 h2 h3 h4
      exact ⟨rfl, ⟨ae, rae, hae⟩, hps, hls, hzs'⟩
    rw [auxEntryIn_cons]
    match Obs.«KernelCheck::aux_already_in».obs ev with
    | .Nil (ld12 := ld) .. =>
      cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons_n1_n1_n1 (ld12 := ld) (ev104 := evaeq) (ev_bdqzbgud := evp) (ev_purmzcuq := evl)
        (op_irtiosum := op) (he160 := hr) (hc162 := hc) .. =>
      obtain ⟨haux, ⟨ae, rae, hae⟩, hps, hls, -⟩ := entry ld
      have haux' : e.aux = true := auxVal_eq_one.mp haux.symm
      obtain ⟨hv, rfl⟩ := Lib.address_eq_spec evaeq rae ra
      have hab : ae = a := by
        by_contra hne
        rw [ite_eq_right hne] at hv
        exact absurd (Value.field.inj hv) (by decide)
      have hx := spec_params_zeta_eq_exact hinj hps hsp
        (sub fun c hc' => by rw [hc]; simp [hc']) evp
      obtain ⟨hy, -⟩ := level_list_struct_eq_exact (hls.mono evp.heap_extends)
        (hus.mono evp.heap_extends) evl
      subst hx hy
      have hpq := prop_bit_mul op
      have hboth : e.params = sp ∧ e.levels = us := by
        by_contra hne
        rw [ite_eq_right hne] at hpq
        exact absurd (Value.field.inj hpq) (by decide)
      rw [hr]
      simp [haux', ← hae, hab, hboth.1, hboth.2]
    | .Cons_n1_n1_other (ld12 := ld) (cs170 := cs2) (ev104 := evaeq) (ev_bdqzbgud := evp)
        (ev_purmzcuq := evl) (op_irtiosum := op) (hne163 := hne1) (ev172 := evrec)
        (hc197 := hc) .. =>
      obtain ⟨haux, ⟨ae, rae, hae⟩, hps, hls, hrest⟩ := entry ld
      obtain ⟨hv, rfl⟩ := Lib.address_eq_spec evaeq rae ra
      have hx := spec_params_zeta_eq_exact hinj hps hsp
        (sub fun c hc' => by rw [hc]; simp [hc']) evp
      obtain ⟨hy, rfl⟩ := level_list_struct_eq_exact (hls.mono evp.heap_extends)
        (hus.mono evp.heap_extends) evl
      subst hx hy
      have hpq := prop_bit_mul op
      have hnot : ¬ (e.params = sp ∧ e.levels = us) := fun hb => hne1 (by rw [hpq, ite_eq_left hb])
      have ext := evp.heap_extends
      rw [ih evrec (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) (flatList_mono ext hrest)
        (Bytes.repAddressRef_heapMono₂ addrTy ext ra) (tmOExactList_mono ext hsp) (hus.mono ext)]
      have hhead : (e.aux && e.addr == ixAddr a && e.params == sp && e.levels == us) = false := by
        by_cases hp : e.params = sp
        · have hl : e.levels ≠ us := fun hl => hnot ⟨hp, hl⟩
          simp [hl]
        · simp [hp]
      rw [hhead, Bool.false_or]
    | .Cons_n1_other (ld12 := ld) (cs205 := cs2) (ev104 := evaeq) (hne198 := hne1)
        (ev207 := evrec) (hc232 := hc) .. =>
      obtain ⟨haux, ⟨ae, rae, hae⟩, hps, hls, hrest⟩ := entry ld
      obtain ⟨hv, rfl⟩ := Lib.address_eq_spec evaeq rae ra
      subst hv
      have hab : ae ≠ a := fun hab => hne1 (by rw [ite_eq_left hab])
      have haddr : e.addr ≠ ixAddr a := by
        rw [← hae]
        exact fun heq => hab (ixAddr_inj heq)
      rw [ih evrec (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hrest ra hsp hus]
      have hhead : (e.aux && e.addr == ixAddr a && e.params == sp && e.levels == us) = false := by
        simp [haddr]
      rw [hhead, Bool.false_or]
    | .Cons_other (ld12 := ld) (cs240 := cs2) (hne233 := hne1) (ev242 := evrec)
        (hc267 := hc) .. =>
      obtain ⟨haux, -, -, -, hrest⟩ := entry ld
      have haux' : e.aux = false := by
        cases hx : e.aux
        · rfl
        · exact (hne1 (by rw [haux, hx]; simp)).elim
      rw [ih evrec (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hrest ra hsp hus]
      simp [haux']

/-- **`KernelModeled::nested_walk(block, originals, 0)` derives the block's flattened family**:
from the block's own types (`originals` at the elimination offset), the returned list
represents exactly `derivedFlatAt` at some fuel. The mention test is refined here
(`occ_mentions_block_spec`). -/
theorem nested_walk_derivedFlatAt {κ : _root_.Address → KKey} {root : List (Call F)}
    {S : _root_.Address → Prop} {Vf : FlatView} {B : _root_.Address}
    (hA : FlatAddrOf κ Vf) (hI : FlatIndAnswersIn root Vf)
    (hC : FlatCtorAnswersIn root S κ Vf) (hMem : FlatMembersAnswersIn root Vf)
    (aux_entry_in : AuxEntryInSpecIn root κ) (hdepth : ScanDepthIn root)
    (hS : ∀ a d, Vf.ci a = some (some d) → S d.blk)
    {off : Nat} {ms : List _root_.Address} {os : List FlatEntry}
    {xblock xacc r : SourceValue F} {bb : Bytes.Address} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelModeled::nested_walk" [xblock, xacc, .field 0] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hblock : Bytes.RepAddressRef addrTy h bb xblock) (hbb : ixAddr bb = B)
    (hms : Vf.members B = some ms) (hos : originals Vf off ms = some os)
    (hacc : RepList flatListEnum (FlatEntryRepExact κ) h os xacc) :
    Heap.Extends h h' ∧ ∃ es, RepList flatListEnum (FlatEntryRepExact κ) h' es r ∧
      ∃ n, derivedFlatAt Vf B off n = some es := by
  have ev' : ObsFn W "KernelModeled::nested_walk" [xblock, xacc, .field ((0 : Nat) : F)]
      h r h' cs := by simpa using ev
  obtain ⟨ext, es, hes, n, hn⟩ := nested_walk_spec hA hI hC hMem
    (occMentionsSpecIn_of_answers hA hI) aux_entry_in hdepth hS ev' hbnd hroot (Nat.zero_le _)
    hblock hbb hacc
  exact ⟨ext, es, hes, n, by simp only [derivedFlatAt, hms, hos]; exact hn⟩

/-! ## The answers at a store -/

/-- An inductive type's data in the reconstruction's reading is its data in the flattening's. -/
theorem indInfoAt_of_indDataAt {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {a : _root_.Address}
    {d : IndData} (h : indDataAt t E a = some (some d)) :
    indInfoAt E a = some (some ⟨d.nl, d.np, d.nctors, d.blk, d.idx⟩) := by
  unfold indDataAt at h
  unfold indInfoAt
  repeat' split at h
  all_goals simp_all
  all_goals (subst_vars; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-- A constant of another kind in the reconstruction's reading is one in the flattening's. -/
theorem indInfoAt_of_indDataAt_none {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {a : _root_.Address} (h : indDataAt t E a = some none) : indInfoAt E a = some none := by
  unfold indDataAt at h
  unfold indInfoAt
  repeat' split at h
  all_goals simp_all

/-- **The flattening's `Ingress::get_ci` answers at a store**, from the reconstruction's. -/
theorem flatIndAnswersIn_ofStore {root : List (Call F)} {κ : _root_.Address → KKey}
    {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    (hI : IndAnswers root κ (ReconView.ofStore t E)) :
    FlatIndAnswersIn root (FlatView.ofStore t E) := by
  intro xa p ci h m cs a ra ev hself hroot ld
  obtain ⟨h1, h2⟩ := hI ra ev hself hroot ld
  refine ⟨fun xnl xty xnp xni xnc xrec xblk xidx hci => ?_,
    fun hne => indInfoAt_of_indDataAt_none (h2 hne)⟩
  obtain ⟨d, ba, hd, -, hnp, -, hnc, hidx, -, -, rfl, -, rfl, hba, rba, rfl⟩ :=
    h1 _ _ _ _ _ _ _ _ hci
  exact ⟨⟨d.nl, d.np, d.nctors, d.blk, d.idx⟩, ba, indInfoAt_of_indDataAt hd, hnp, hnc, hidx,
    rfl, rfl, hba, rba, rfl⟩

/-- **The flattening's view of a store inverts the table's keying**, at a well-formed table. -/
theorem flatAddrOf_ofStore {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) (E : Ixon.Env) :
    FlatAddrOf (IxVM.Consistency.keyOf t) (FlatView.ofStore t E) :=
  fun a => keyAddr_keyOf hwf a

end IxVM.Refinement.Binding.FamilyRecon
