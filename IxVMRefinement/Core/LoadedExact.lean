import IxVMRefinement.Core.Loaded

/-! # Exact representations of freshly converted records

Conversion preserves syntactic levels and binder annotations. These representations retain
that evidence before the semantic core weakens levels to equivalence. Existing declaration
names remain available to their callers.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (Expr LevelParam ConstantVal ConstantInfo RecRule)

/-! ## Exact heap representation (`TmExact` and `CIRepExact`)

`Tm` relaxes `Srt` and `Const` levels up to semantic equivalence (`LvEq` / `LvEqList`) so that
`Core` outputs after level reduction remain represented. Freshly converted constant records from
`Ingress` carry exact syntactic `RepKLevel` / `RepKLevelList` levels (`TmExact`), which both
refined syntactic checks (`validate_expr_well_scoped`, `kexpr_struct_eq`) read and weaken
immediately to `Tm` (`TmExact.toTm`) for `Core`. -/

inductive TmExact (κ : _root_.Address → KKey) (d : Nat) (Γ : Nat → KExpr) (h : Heap F) :
    Nat → KExpr → SourceValue F → Prop where
  | bvarLocal {k addr : Nat} {i : F}
      (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field i]))
      (hsmall : ZMod.val i < 9223372036854775808) (hi : ZMod.val i < k) :
      TmExact κ d Γ h k (.bvar (ZMod.val i)) (.ptr (.enum kexprEnum) addr)
  | bvarFree {k addr : Nat} {i : F}
      (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field i]))
      (hsmall : ZMod.val i < 9223372036854775808) (hk : k ≤ ZMod.val i)
      (hd : ZMod.val i - k < d) :
      TmExact κ d Γ h k (.fvar (fvIdx d k (ZMod.val i)) (Γ (fvIdx d k (ZMod.val i))))
        (.ptr (.enum kexprEnum) addr)
  | sort {k addr : Nat} {lp : SourceValue F} {l : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Srt" [lp]))
      (rl : RepKLevel h l lp) :
      TmExact κ d Γ h k (.sort l) (.ptr (.enum kexprEnum) addr)
  | const {k addr : Nat} {ap lsp : SourceValue F} {a : Bytes.Address} {ls : List KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Const" [ap, lsp]))
      (ra : Bytes.RepAddressRef addrTy h a ap) (rls : RepKLevelList h ls lsp) :
      TmExact κ d Γ h k (.const (κ (ixAddr a)) ls) (.ptr (.enum kexprEnum) addr)
  | app {k addr : Nat} {fp ap : SourceValue F} {Ef Ea : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "App" [fp, ap]))
      (rf : TmExact κ d Γ h k Ef fp) (ra : TmExact κ d Γ h k Ea ap) :
      TmExact κ d Γ h k (.app Ef Ea) (.ptr (.enum kexprEnum) addr)
  | lam {k addr : Nat} {tp bp lp : SourceValue F} {T B : KExpr} {ℓ : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Lam" [tp, bp, lp]))
      (rt : TmExact κ d Γ h k T tp) (rb : TmExact κ d Γ h (k + 1) B bp)
      (rl : RepKLevel h ℓ lp) :
      TmExact κ d Γ h k (.lam T B (bmeta ℓ)) (.ptr (.enum kexprEnum) addr)
  | forallE {k addr : Nat} {tp bp lp : SourceValue F} {T B : KExpr} {ℓ : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Forall" [tp, bp, lp]))
      (rt : TmExact κ d Γ h k T tp) (rb : TmExact κ d Γ h (k + 1) B bp)
      (rl : RepKLevel h ℓ lp) :
      TmExact κ d Γ h k (.forallE T B (bmeta ℓ)) (.ptr (.enum kexprEnum) addr)
  | letE {k addr : Nat} {tp vp bp : SourceValue F} {T V B : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "Let" [tp, vp, bp]))
      (rt : TmExact κ d Γ h k T tp) (rv : TmExact κ d Γ h k V vp)
      (rb : TmExact κ d Γ h (k + 1) B bp) :
      TmExact κ d Γ h k (instShift V 0 B) (.ptr (.enum kexprEnum) addr)
  | litNat {k addr : Nat} {lp : SourceValue F} {limbs : List UInt64}
      (cell : h[addr]? = some (.construct kexprEnum "Lit" [.construct klitEnum "Nat" [lp]]))
      (rl : RepList limbListEnum RepU64 h limbs lp) (hc : limbs.getLast? ≠ some 0) :
      TmExact κ d Γ h k (.lit (.natVal (limbsVal limbs))) (.ptr (.enum kexprEnum) addr)
  | litStr {k addr : Nat} {bp : SourceValue F} {bytes : List UInt8} {s : String}
      (cell : h[addr]? = some (.construct kexprEnum "Lit" [.construct klitEnum "Str" [bp]]))
      (rb : Bytes.RepByteStream byteListEnum h bytes bp) (hs : StrBytes s bytes) :
      TmExact κ d Γ h k (.lit (.strVal s)) (.ptr (.enum kexprEnum) addr)
  | proj {k addr : Nat} {ap ep : SourceValue F} {a : Bytes.Address} {i : F} {E : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "Proj" [ap, .field i, ep]))
      (ra : Bytes.RepAddressRef addrTy h a ap) (re : TmExact κ d Γ h k E ep) :
      TmExact κ d Γ h k (.proj (κ (ixAddr a)) (ZMod.val i) E) (.ptr (.enum kexprEnum) addr)

def TmCExact (κ : _root_.Address → KKey) (h : Heap F) (E : KExpr) (p : SourceValue F) : Prop :=
  ∀ d Γ, TmExact κ d Γ h 0 E p

theorem TmExact.toTm {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : TmExact κ d Γ h k E p) :
    Tm κ d Γ h k E p := by
  induction rep with
  | bvarLocal cell hs hi => exact .bvarLocal cell hs hi
  | bvarFree cell hs hk hd => exact .bvarFree cell hs hk hd
  | sort cell rl => exact .sort cell rl (LvEq.refl _)
  | const cell ra rls => exact .const cell ra rls (LvEqList.refl _)
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | letE cell _ _ _ iht ihv ihb => exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | proj cell ra _ ihe => exact .proj cell ra ihe

theorem TmCExact.toTmC {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr} {p : SourceValue F}
    (rep : TmCExact κ h E p) : TmC κ h E p :=
  fun d Γ => (rep d Γ).toTm

theorem TmExact.mono {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h₁ h₂ : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : TmExact κ d Γ h₁ k E p) : TmExact κ d Γ h₂ k E p := by
  induction rep with
  | bvarLocal cell hs hi => exact .bvarLocal (ext.getElem?_eq cell) hs hi
  | bvarFree cell hs hk hd => exact .bvarFree (ext.getElem?_eq cell) hs hk hd
  | sort cell rl => exact .sort (ext.getElem?_eq cell) (rl.mono ext)
  | const cell ra rls =>
    exact .const (ext.getElem?_eq cell) (Bytes.repAddressRef_heapMono₂ addrTy ext ra)
      (rls.mono ext)
  | app cell _ _ ihf iha => exact .app (ext.getElem?_eq cell) ihf iha
  | lam cell _ _ rl iht ihb => exact .lam (ext.getElem?_eq cell) iht ihb (rl.mono ext)
  | forallE cell _ _ rl iht ihb => exact .forallE (ext.getElem?_eq cell) iht ihb (rl.mono ext)
  | letE cell _ _ _ iht ihv ihb => exact .letE (ext.getElem?_eq cell) iht ihv ihb
  | litNat cell rl hc =>
    exact .litNat (ext.getElem?_eq cell) (repList_heapMono₂ _ repU64_heapMono₂ ext rl) hc
  | litStr cell rb hs =>
    exact .litStr (ext.getElem?_eq cell) (Bytes.repByteStream_heapMono₂ _ ext rb) hs
  | proj cell ra _ ihe =>
    exact .proj (ext.getElem?_eq cell) (Bytes.repAddressRef_heapMono₂ addrTy ext ra) ihe

theorem TmCExact.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {E : KExpr}
    {p : SourceValue F} (ext : Heap.Extends h₁ h₂) (rep : TmCExact κ h₁ E p) :
    TmCExact κ h₂ E p :=
  fun d Γ => (rep d Γ).mono ext

def ValRepExact (κ : _root_.Address → KKey) (h : Heap F) (nl ty : SourceValue F)
    (cv : ConstantVal .anon) : Prop :=
  nl = .field (cv.levelParams.length : F) ∧ cv.levelParams.length < 4294967296 ∧
    cv.levelParams.Perm (List.range cv.levelParams.length) ∧
    TmCExact κ h (posOf cv.levelParams cv.type) ty

def RuleRepExact (κ : _root_.Address → KKey) (h : Heap F) (ps : List LevelParam) (j : Nat)
    (v : SourceValue F) (rl : RecRule .anon) : Prop :=
  ∃ rhs : SourceValue F, v = .construct krrEnum "Mk" [.field (j : F), .field (rl.nfields : F), rhs] ∧
    rl.nfields < 72057594037927936 ∧ TmCExact κ h (posOf ps rl.rhs) rhs

inductive RulesRepExact (κ : _root_.Address → KKey) (h : Heap F) (ps : List LevelParam) :
    Nat → SourceValue F → List (RecRule .anon) → Prop where
  | nil {j addr : Nat} (cell : h[addr]? = some (.construct krrListEnum "Nil" [])) :
      RulesRepExact κ h ps j (.ptr (.enum krrListEnum) addr) []
  | cons {j addr : Nat} {v rest : SourceValue F} {rl : RecRule .anon} {rls : List (RecRule .anon)}
      (cell : h[addr]? = some (.construct krrListEnum "Cons" [v, rest]))
      (hr : RuleRepExact κ h ps j v rl) (rs : RulesRepExact κ h ps (j + 1) rest rls) :
      RulesRepExact κ h ps j (.ptr (.enum krrListEnum) addr) (rl :: rls)

inductive CIRepExact (κ : _root_.Address → KKey) (h : Heap F) :
    SourceValue F → ConstantInfo .anon → Prop where
  | axio {nl ty u : SourceValue F} {cv : ConstantVal .anon}
      (hv : ValRepExact κ h nl ty cv) :
      CIRepExact κ h (.construct kciEnum "Axiom" [nl, ty, u]) (.axiomInfo cv)
  | opaq {nl ty val u : SourceValue F} {cv : ConstantVal .anon} {V : KExpr}
      (hv : ValRepExact κ h nl ty cv)
      (hval : TmCExact κ h (posOf cv.levelParams V) val) :
      CIRepExact κ h (.construct kciEnum "Opaque" [nl, ty, val, u]) (.axiomInfo cv)
  | defn {nl ty val sf hint : SourceValue F} {cv : ConstantVal .anon}
      {V : KExpr} {hn : Ix.Kernel.ReducibilityHint}
      (hv : ValRepExact κ h nl ty cv) (hV : TmCExact κ h (posOf cv.levelParams V) val) :
      CIRepExact κ h (.construct kciEnum "Defn" [nl, ty, val, sf, hint]) (.defnInfo cv V hn)
  | thm {nl ty val : SourceValue F} {cv : ConstantVal .anon} {V : KExpr}
      (hv : ValRepExact κ h nl ty cv) (hV : TmCExact κ h (posOf cv.levelParams V) val) :
      CIRepExact κ h (.construct kciEnum "Thm" [nl, ty, val]) (.thmInfo cv V)
  | quot {nl ty kind : SourceValue F} {ci : ConstantInfo .anon}
      (hv : ValRepExact κ h nl ty ci.toConstantVal) (hk : QuotKindRep kind ci) :
      CIRepExact κ h (.construct kciEnum "Quot" [nl, ty, kind]) ci
  | induct {nl ty np ni nc u blk idx : SourceValue F} {cv : ConstantVal .anon}
      {caps : Ix.Kernel.IndCaps .anon}
      (hv : ValRepExact κ h nl ty cv)
      (hcounts : ∃ nP nI nC : Nat, np = .field (nP : F) ∧ ni = .field (nI : F) ∧
        nc = .field (nC : F) ∧ nP < 72057594037927936 ∧ nI < 72057594037927936 ∧
        nC < 72057594037927936)
      (hkey : ∃ (b : Bytes.Address) (i : F), Bytes.RepAddressRef addrTy h b blk ∧ idx = .field i ∧
        cv.name = κ (iprjAddr (ixAddr b) (ZMod.val i))) :
      CIRepExact κ h (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx])
        (.indInfo cv caps)
  | ctor {nl ty blk ind cidx np nf u : SourceValue F} {cv : ConstantVal .anon}
      {nP nF : Nat}
      (hv : ValRepExact κ h nl ty cv) (hnp : np = .field (nP : F)) (hnf : nf = .field (nF : F))
      (hcounts : nP < 72057594037927936 ∧ nF < 72057594037927936)
      (hkey : ∃ (b : Bytes.Address) (i j : F), Bytes.RepAddressRef addrTy h b blk ∧ ind = .field i ∧
        cidx = .field j ∧ cv.name = κ (cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j))) :
      CIRepExact κ h (.construct kciEnum "Ctor" [nl, ty, blk, ind, cidx, np, nf, u])
        (.ctorInfo cv nP nF)
  | recr {nl ty np ni nm nmi rules k u blk idx : SourceValue F}
      {cv : ConstantVal .anon} {mI rP : Nat} {rls : List (RecRule .anon)}
      {p i m mi : F}
      (hv : ValRepExact κ h nl ty cv) (hnp : np = .field p) (hni : ni = .field i)
      (hnm : nm = .field m) (hnmi : nmi = .field mi) (hrP : (rP : F) = p + m + mi)
      (hmI : (mI : F) = p + m + mi + i) (hcounts : rP ≤ mI ∧ mI < 288230376151711744)
      (hrules : RulesRepExact κ h cv.levelParams 0 rules rls)
      (hk : k = .field 1 → ∃ rl, rls = [rl] ∧ rl.k = true ∧ rl.ctorParams = ZMod.val p)
      (hkey : ∃ (b : Bytes.Address) (i : F), Bytes.RepAddressRef addrTy h b blk ∧ idx = .field i ∧
        (cv.name = κ (ixAddr b) ∨ cv.name = κ (rprjAddr (ixAddr b) (ZMod.val i)))) :
      CIRepExact κ h (.construct kciEnum "Rec"
        [nl, ty, np, ni, nm, nmi, rules, k, u, blk, idx]) (.recInfo cv mI rP rls)

theorem ValRepExact.toValRep {κ : _root_.Address → KKey} {h : Heap F} {nl ty : SourceValue F}
    {cv : ConstantVal .anon} (hv : ValRepExact κ h nl ty cv) : ValRep κ h nl ty cv :=
  ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.toTmC⟩

theorem RulesRepExact.toRulesRep {κ : _root_.Address → KKey} {h : Heap F} {ps : List LevelParam}
    {j : Nat} {v : SourceValue F} {rls : List (RecRule .anon)}
    (hr : RulesRepExact κ h ps j v rls) : RulesRep κ h ps j v rls := by
  induction hr with
  | nil cell => exact .nil cell
  | cons cell hh _ ih =>
    obtain ⟨rhs, hrhs, hnf, htm⟩ := hh
    exact .cons cell ⟨rhs, hrhs, hnf, htm.toTmC⟩ ih

/-- The exact constructor representation retains its value's exact type field. -/
theorem CIRepExact.ctor_valRep {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty blk ind cidx np nf safety : SourceValue F} {cv : ConstantVal .anon} {nP nF : Nat}
    (represented : CIRepExact κ h (.construct kciEnum "Ctor" [nl, ty, blk, ind, cidx, np, nf, safety])
      (.ctorInfo cv nP nF)) : ValRepExact κ h nl ty cv := by
  cases represented with
  | ctor value _ _ _ _ => exact value

theorem CIRepExact.toCIRep {κ : _root_.Address → KKey} {h : Heap F} {v : SourceValue F}
    {ci : ConstantInfo .anon} (hci : CIRepExact κ h v ci) : CIRep κ h v ci := by
  cases hci with
  | axio hv => exact .axio hv.toValRep
  | opaq hv _ => exact .opaq hv.toValRep
  | defn hv hV => exact .defn hv.toValRep hV.toTmC
  | thm hv hV => exact .thm hv.toValRep hV.toTmC
  | quot hv hk => exact .quot hv.toValRep hk
  | induct hv hcounts hkey => exact .induct hv.toValRep hcounts hkey
  | ctor hv hnp hnf hcounts hkey => exact .ctor hv.toValRep hnp hnf hcounts hkey
  | recr hv hnp hni hnm hnmi hrP hmI hcounts hrules hk hkey =>
    exact .recr hv.toValRep hnp hni hnm hnmi hrP hmI hcounts hrules.toRulesRep hk hkey

def CIPtrRepExact (κ : _root_.Address → KKey) (h : Heap F) (p : SourceValue F)
    (ci : ConstantInfo .anon) : Prop :=
  ∃ v, loadValue h p = .ok v ∧ CIRepExact κ h v ci

theorem CIPtrRepExact.toCIPtrRep {κ : _root_.Address → KKey} {h : Heap F} {p : SourceValue F}
    {ci : ConstantInfo .anon} (r : CIPtrRepExact κ h p ci) : CIPtrRep κ h p ci :=
  let ⟨v, hl, hr⟩ := r; ⟨v, hl, hr.toCIRep⟩

theorem ValRepExact.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {nl ty : SourceValue F}
    {cv : ConstantVal .anon} (ext : Heap.Extends h₁ h₂) (r : ValRepExact κ h₁ nl ty cv) :
    ValRepExact κ h₂ nl ty cv :=
  ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.mono ext⟩

theorem RulesRepExact.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {ps : List LevelParam}
    {j : Nat} {v : SourceValue F} {rls : List (RecRule .anon)} (ext : Heap.Extends h₁ h₂)
    (r : RulesRepExact κ h₁ ps j v rls) : RulesRepExact κ h₂ ps j v rls := by
  induction r with
  | nil cell => exact .nil (ext.getElem?_eq cell)
  | cons cell hr _ ih =>
    obtain ⟨rhs, hv, hn, hrhs⟩ := hr
    exact .cons (ext.getElem?_eq cell) ⟨rhs, hv, hn, hrhs.mono ext⟩ ih

theorem CIRepExact.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {v : SourceValue F}
    {ci : ConstantInfo .anon} (ext : Heap.Extends h₁ h₂) (r : CIRepExact κ h₁ v ci) :
    CIRepExact κ h₂ v ci := by
  cases r with
  | axio hv => exact .axio (hv.mono ext)
  | opaq hv hval => exact .opaq (hv.mono ext) (hval.mono ext)
  | defn hv hV => exact .defn (hv.mono ext) (hV.mono ext)
  | thm hv hV => exact .thm (hv.mono ext) (hV.mono ext)
  | quot hv hk => exact .quot (hv.mono ext) hk
  | induct hv hcounts hkey =>
    obtain ⟨b, i, hb, hi, hn⟩ := hkey
    exact .induct (hv.mono ext) hcounts ⟨b, i, Bytes.repAddressRef_heapMono₂ addrTy ext hb, hi, hn⟩
  | ctor hv hnp hnf hcounts hkey =>
    obtain ⟨b, i, j, hb, hi, hj, hn⟩ := hkey
    exact .ctor (hv.mono ext) hnp hnf hcounts
      ⟨b, i, j, Bytes.repAddressRef_heapMono₂ addrTy ext hb, hi, hj, hn⟩
  | recr hv hnp hni hnm hnmi hrP hmI hcounts hrules hk hkey =>
    obtain ⟨b, i, hb, hi, hn⟩ := hkey
    exact .recr (hv.mono ext) hnp hni hnm hnmi hrP hmI hcounts (hrules.mono ext) hk
      ⟨b, i, Bytes.repAddressRef_heapMono₂ addrTy ext hb, hi, hn⟩

theorem CIPtrRepExact.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {p : SourceValue F}
    {ci : ConstantInfo .anon} (ext : Heap.Extends h₁ h₂) (r : CIPtrRepExact κ h₁ p ci) :
    CIPtrRepExact κ h₂ p ci :=
  let ⟨v, hl, hr⟩ := r; ⟨v, ext.loadValue_eq hl, hr.mono ext⟩

/-! ## Cell-load inversions for `TmExact` -/

section TmExactInversion
variable {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F} {k : Nat}
  {E : KExpr} {p : SourceValue F}

theorem TmExact.bvar_of_load {x : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "BVar" [x])) :
    ∃ i : F, x = .field i ∧ ZMod.val i < 9223372036854775808 ∧
      ((ZMod.val i < k ∧ E = .bvar (ZMod.val i)) ∨
        (k ≤ ZMod.val i ∧ ZMod.val i - k < d ∧
          E = .fvar (fvIdx d k (ZMod.val i)) (Γ (fvIdx d k (ZMod.val i))))) :=
  rep.toTm.bvar_of_load hl

theorem TmExact.sort_of_load {x : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Srt" [x])) :
    ∃ l, E = .sort l ∧ RepKLevel h l x := by
  cases rep with
  | sort cell rl =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with hx; subst hx
    exact ⟨_, rfl, rl⟩
  | bvarLocal cell | bvarFree cell | const cell | app cell | lam cell | forallE cell | letE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmExact.const_of_load {ap lsp : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Const" [ap, lsp])) :
    ∃ a ls, E = .const (κ (ixAddr a)) ls ∧ Bytes.RepAddressRef addrTy h a ap ∧
      RepKLevelList h ls lsp := by
  cases rep with
  | const cell ra rls =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2; subst h1 h2
    exact ⟨_, _, rfl, ra, rls⟩
  | bvarLocal cell | bvarFree cell | sort cell | app cell | lam cell | forallE cell | letE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmExact.app_of_load {fp ap : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "App" [fp, ap])) :
    ∃ Ef Ea, E = .app Ef Ea ∧ TmExact κ d Γ h k Ef fp ∧ TmExact κ d Γ h k Ea ap := by
  cases rep with
  | app cell rf ra =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2; subst h1 h2
    exact ⟨_, _, rfl, rf, ra⟩
  | bvarLocal cell | bvarFree cell | sort cell | const cell | lam cell | forallE cell | letE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmExact.lam_of_load {tp bp lp : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Lam" [tp, bp, lp])) :
    ∃ T B ℓ, E = .lam T B (bmeta ℓ) ∧ TmExact κ d Γ h k T tp ∧
      TmExact κ d Γ h (k + 1) B bp ∧ RepKLevel h ℓ lp := by
  cases rep with
  | lam cell rt rb rl =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2 h3; injection h3 with h3
    subst h1 h2 h3
    exact ⟨_, _, _, rfl, rt, rb, rl⟩
  | bvarLocal cell | bvarFree cell | sort cell | const cell | app cell | forallE cell | letE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmExact.forallE_of_load {tp bp lp : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Forall" [tp, bp, lp])) :
    ∃ T B ℓ, E = .forallE T B (bmeta ℓ) ∧ TmExact κ d Γ h k T tp ∧
      TmExact κ d Γ h (k + 1) B bp ∧ RepKLevel h ℓ lp := by
  cases rep with
  | forallE cell rt rb rl =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2 h3; injection h3 with h3
    subst h1 h2 h3
    exact ⟨_, _, _, rfl, rt, rb, rl⟩
  | bvarLocal cell | bvarFree cell | sort cell | const cell | app cell | lam cell | letE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmExact.letE_of_load {tp vp bp : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Let" [tp, vp, bp])) :
    ∃ T V B, E = instShift V 0 B ∧ TmExact κ d Γ h k T tp ∧ TmExact κ d Γ h k V vp ∧
      TmExact κ d Γ h (k + 1) B bp := by
  cases rep with
  | letE cell rt rv rb =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2 h3; injection h3 with h3
    subst h1 h2 h3
    exact ⟨_, _, _, rfl, rt, rv, rb⟩
  | bvarLocal cell | bvarFree cell | sort cell | const cell | app cell | lam cell | forallE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmExact.lit_of_load {lv : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Lit" [lv])) :
    (∃ lp limbs, lv = .construct klitEnum "Nat" [lp] ∧
      E = .lit (.natVal (limbsVal limbs)) ∧ RepList limbListEnum RepU64 h limbs lp) ∨
    (∃ bp bytes s, lv = .construct klitEnum "Str" [bp] ∧
      E = .lit (.strVal s) ∧ Bytes.RepByteStream byteListEnum h bytes bp ∧ StrBytes s bytes) := by
  cases rep with
  | litNat cell rl _ =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with hx; subst hx
    exact .inl ⟨_, _, rfl, rfl, rl⟩
  | litStr cell rb hs =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with hx; subst hx
    exact .inr ⟨_, _, _, rfl, rfl, rb, hs⟩
  | bvarLocal cell | bvarFree cell | sort cell | const cell | app cell | lam cell | forallE cell
  | letE cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmExact.proj_of_load {ap fp ep : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Proj" [ap, fp, ep])) :
    ∃ (a : Bytes.Address) (i : F) (E₁ : KExpr),
      fp = .field i ∧ E = .proj (κ (ixAddr a)) (ZMod.val i) E₁ ∧
      Bytes.RepAddressRef addrTy h a ap ∧ TmExact κ d Γ h k E₁ ep := by
  cases rep with
  | proj cell ra re =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2 h3; injection h3 with h3
    subst h1 h2 h3
    exact ⟨_, _, _, rfl, rfl, ra, re⟩
  | bvarLocal cell | bvarFree cell | sort cell | const cell | app cell | lam cell | forallE cell
  | letE cell | litNat cell | litStr cell =>
    exact (load_cell_ne cell hl (by decide)).elim

end TmExactInversion

end IxVM.Refinement.Decl
