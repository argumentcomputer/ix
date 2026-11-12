import IxVMRefinement.Core.Rep
import IxC.Ixon.Codec

/-! # Loaded constants: IxVM's `KConstantInfo` and the kernel's `ConstantInfo`

`CIRep κ h v ci`: the value `v` (a `KernelTypes::KConstantInfo`, as `*(Ingress::get_ci(a))`
loads it) represents the kernel constant `ci`, for all eight IxVM kinds:

| IxVM | kernel | related |
|---|---|---|
| `Axiom(nl, ty, unsafe)` | `axiomInfo cv` | level count, type |
| `Opaque(nl, ty, value, unsafe)` | `axiomInfo cv` (the kernel stores an opaque as an axiom) | level count, type |
| `Defn(nl, ty, value, safety, hint)` | `defnInfo cv V hint'` | level count, type, value |
| `Thm(nl, ty, value)` | `thmInfo cv V` | level count, type, value |
| `Quot(nl, ty, kind)` | the pinned quotient constant of that kind | level count, type, kind |
| `Induct(nl, ty, np, ni, nc, unsafe, block, idx)` | `indInfo cv caps` | level count, type |
| `Ctor(nl, ty, block, ind, cidx, np, nf, unsafe)` | `ctorInfo cv nP nF` | level count, type, `np`, `nf` |
| `Rec(nl, ty, np, ni, nm, nmi, rules, k, unsafe, block, idx)` | `recInfo cv mI rP rules'` | level count, type, the two sums, the rules one for one |

A constant's level parameters are positional (`List.range nl`), as the kernel reader writes
them. Types, values and rule right-hand sides are closed terms (`TmC`). The kernel's
install-computed data (an inductive's capabilities, a rule's constructor key, firing mode,
parameter count and flags, a definition's hint) are not read off IxVM's value: where the
core needs them they are environment facts (`Ctx.lean`, `EnvFacts`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

/-! ## Projection-record addresses -/

/-- The address of a projection record with empty tables (`info` a projection). IxVM computes
these (`Ingress::projection_addr`, `KernelDefEq::compute_iprj_addr`,
`KernelCheck::projection_addr_ctor`) by serializing and hashing the record. -/
def projAddr (info : Ixon.ConstantInfo) : _root_.Address :=
  Address.blake3Pure (Ixon.serConstant ⟨info, #[], #[], #[]⟩)

/-- The inductive-projection record of member `i` of the block `b`. -/
def iprjAddr (b : _root_.Address) (i : Nat) : _root_.Address :=
  projAddr (.iPrj ⟨i.toUInt64, b⟩)

/-- The constructor-projection record of constructor `j` of member `i` of the block `b`. -/
def cprjAddr (b : _root_.Address) (i j : Nat) : _root_.Address :=
  projAddr (.cPrj ⟨i.toUInt64, j.toUInt64, b⟩)

/-- The recursor-projection record of member `i` of the block `b`. -/
def rprjAddr (b : _root_.Address) (i : Nat) : _root_.Address :=
  projAddr (.rPrj ⟨i.toUInt64, b⟩)

/-- The definition-projection record of member `i` of the block `b`. -/
def dprjAddr (b : _root_.Address) (i : Nat) : _root_.Address :=
  projAddr (.dPrj ⟨i.toUInt64, b⟩)

/-! ## The relation -/

/-- **A constant's level count and type**: `nl` is the number of its (positional) level
parameters, below `2^32` (the decoders' bound on level counts), and `ty` represents its closed
type. -/
def ValRep (κ : _root_.Address → KKey) (h : Heap F) (nl ty : SourceValue F)
    (cv : Ix.Kernel.ConstantVal .anon) : Prop :=
  nl = .field (cv.levelParams.length : F) ∧ cv.levelParams.length < 4294967296 ∧
    cv.levelParams = List.range cv.levelParams.length ∧ TmC κ h cv.type ty

/-- **A recursor rule** (`KernelTypes::KRecRule::Mk(cidx, nfields, rhs)`, the `j`-th of its
list): its constructor index is its position, its field count and closed right-hand side are
the kernel rule's. The rule's constructor key is an environment fact (`EnvFacts.recRules`). -/
def RuleRep (κ : _root_.Address → KKey) (h : Heap F) (j : Nat) (v : SourceValue F)
    (rl : Ix.Kernel.RecRule .anon) : Prop :=
  ∃ rhs, v = .construct krrEnum "Mk" [.field (j : F), .field (rl.nfields : F), rhs] ∧
    TmC κ h rl.rhs rhs

/-- **The rule list**, one for one from position `j`. -/
inductive RulesRep (κ : _root_.Address → KKey) (h : Heap F) :
    Nat → SourceValue F → List (Ix.Kernel.RecRule .anon) → Prop where
  | nil {j addr : Nat} (cell : h[addr]? = some (.construct krrListEnum "Nil" [])) :
      RulesRep κ h j (.ptr (.enum krrListEnum) addr) []
  | cons {j addr : Nat} {v rest : SourceValue F} {rl : Ix.Kernel.RecRule .anon}
      {rls : List (Ix.Kernel.RecRule .anon)}
      (cell : h[addr]? = some (.construct krrListEnum "Cons" [v, rest]))
      (hr : RuleRep κ h j v rl) (rs : RulesRep κ h (j + 1) rest rls) :
      RulesRep κ h j (.ptr (.enum krrListEnum) addr) (rl :: rls)

/-- **A quotient constant's kind** (`Ixon::QuotKind`: `Typ`, `Ctor`, `Lift`, `Ind`) and the
pinned quotient constant it reads as (`Ix.Kernel.BasisKind.quotK`): the type former, the
constructor `Quot.mk`, the recursors `Quot.lift` and `Quot.ind`. -/
def QuotKindRep (kind : SourceValue F) (ci : Ix.Kernel.ConstantInfo .anon) : Prop :=
  (kind = .construct "Ixon::QuotKind" "Typ" [] ∧ ∃ cv caps, ci = .indInfo cv caps) ∨
  (kind = .construct "Ixon::QuotKind" "Ctor" [] ∧ ∃ cv nP nF, ci = .ctorInfo cv nP nF) ∨
  (kind = .construct "Ixon::QuotKind" "Lift" [] ∧ ∃ cv mI rP rs, ci = .recInfo cv mI rP rs) ∨
  (kind = .construct "Ixon::QuotKind" "Ind" [] ∧ ∃ cv mI rP rs, ci = .recInfo cv mI rP rs)

/-- **The loaded constant represents the kernel constant** (module docstring's table). -/
inductive CIRep (κ : _root_.Address → KKey) (h : Heap F) :
    SourceValue F → Ix.Kernel.ConstantInfo .anon → Prop where
  | axio {nl ty u : SourceValue F} {cv : Ix.Kernel.ConstantVal .anon}
      (hv : ValRep κ h nl ty cv) :
      CIRep κ h (.construct kciEnum "Axiom" [nl, ty, u]) (.axiomInfo cv)
  | opaq {nl ty val u : SourceValue F} {cv : Ix.Kernel.ConstantVal .anon}
      (hv : ValRep κ h nl ty cv) :
      CIRep κ h (.construct kciEnum "Opaque" [nl, ty, val, u]) (.axiomInfo cv)
  | defn {nl ty val sf hint : SourceValue F} {cv : Ix.Kernel.ConstantVal .anon} {V : KExpr}
      {hn : Ix.Kernel.ReducibilityHint}
      (hv : ValRep κ h nl ty cv) (hV : TmC κ h V val) :
      CIRep κ h (.construct kciEnum "Defn" [nl, ty, val, sf, hint]) (.defnInfo cv V hn)
  | thm {nl ty val : SourceValue F} {cv : Ix.Kernel.ConstantVal .anon} {V : KExpr}
      (hv : ValRep κ h nl ty cv) (hV : TmC κ h V val) :
      CIRep κ h (.construct kciEnum "Thm" [nl, ty, val]) (.thmInfo cv V)
  | quot {nl ty kind : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon}
      (hv : ValRep κ h nl ty ci.toConstantVal) (hk : QuotKindRep kind ci) :
      CIRep κ h (.construct kciEnum "Quot" [nl, ty, kind]) ci
  | induct {nl ty np ni nc u blk idx : SourceValue F} {cv : Ix.Kernel.ConstantVal .anon}
      {caps : Ix.Kernel.IndCaps .anon}
      (hv : ValRep κ h nl ty cv)
      (hkey : ∃ (b : Bytes.Address) (i : F), Bytes.RepAddressRef addrTy h b blk ∧ idx = .field i ∧
        cv.name = κ (iprjAddr (ixAddr b) (ZMod.val i))) :
      CIRep κ h (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) (.indInfo cv caps)
  | ctor {nl ty blk ind cidx np nf u : SourceValue F} {cv : Ix.Kernel.ConstantVal .anon}
      {nP nF : Nat}
      (hv : ValRep κ h nl ty cv) (hnp : np = .field (nP : F)) (hnf : nf = .field (nF : F))
      (hkey : ∃ (b : Bytes.Address) (i j : F), Bytes.RepAddressRef addrTy h b blk ∧ ind = .field i ∧
        cidx = .field j ∧ cv.name = κ (cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j))) :
      CIRep κ h (.construct kciEnum "Ctor" [nl, ty, blk, ind, cidx, np, nf, u]) (.ctorInfo cv nP nF)
  | recr {nl ty np ni nm nmi rules k u blk idx : SourceValue F}
      {cv : Ix.Kernel.ConstantVal .anon} {mI rP : Nat} {rls : List (Ix.Kernel.RecRule .anon)}
      {p i m mi : F}
      (hv : ValRep κ h nl ty cv) (hnp : np = .field p) (hni : ni = .field i) (hnm : nm = .field m)
      (hnmi : nmi = .field mi) (hrP : (rP : F) = p + m + mi) (hmI : (mI : F) = p + m + mi + i)
      (hrules : RulesRep κ h 0 rules rls)
      (hkey : ∃ (b : Bytes.Address) (i : F), Bytes.RepAddressRef addrTy h b blk ∧ idx = .field i ∧
        (cv.name = κ (ixAddr b) ∨ cv.name = κ (rprjAddr (ixAddr b) (ZMod.val i)))) :
      CIRep κ h (.construct kciEnum "Rec" [nl, ty, np, ni, nm, nmi, rules, k, u, blk, idx])
        (.recInfo cv mI rP rls)

/-- **A pointer to a loaded constant** (`&KernelTypes::KConstantInfo`, what `Ingress::get_ci`
returns) represents `ci`. -/
def CIPtrRep (κ : _root_.Address → KKey) (h : Heap F) (p : SourceValue F)
    (ci : Ix.Kernel.ConstantInfo .anon) : Prop :=
  ∃ v, loadValue h p = .ok v ∧ CIRep κ h v ci

/-! ## Heap monotonicity -/

theorem ValRep.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {nl ty : SourceValue F}
    {cv : Ix.Kernel.ConstantVal .anon} (ext : Heap.Extends h₁ h₂) (r : ValRep κ h₁ nl ty cv) :
    ValRep κ h₂ nl ty cv :=
  ⟨r.1, r.2.1, r.2.2.1, TmC.mono ext r.2.2.2⟩

theorem RulesRep.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {j : Nat} {v : SourceValue F}
    {rls : List (Ix.Kernel.RecRule .anon)} (ext : Heap.Extends h₁ h₂) (r : RulesRep κ h₁ j v rls) :
    RulesRep κ h₂ j v rls := by
  induction r with
  | nil cell => exact .nil (ext.getElem?_eq cell)
  | cons cell hr _ ih =>
    obtain ⟨rhs, hv, hrhs⟩ := hr
    exact .cons (ext.getElem?_eq cell) ⟨rhs, hv, TmC.mono ext hrhs⟩ ih

theorem CIRep.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {v : SourceValue F}
    {ci : Ix.Kernel.ConstantInfo .anon} (ext : Heap.Extends h₁ h₂) (r : CIRep κ h₁ v ci) :
    CIRep κ h₂ v ci := by
  cases r with
  | axio hv => exact .axio (hv.mono ext)
  | opaq hv => exact .opaq (hv.mono ext)
  | defn hv hV => exact .defn (hv.mono ext) (TmC.mono ext hV)
  | thm hv hV => exact .thm (hv.mono ext) (TmC.mono ext hV)
  | quot hv hk => exact .quot (hv.mono ext) hk
  | induct hv hkey =>
    obtain ⟨b, i, hb, hi, hn⟩ := hkey
    exact .induct (hv.mono ext) ⟨b, i, Bytes.repAddressRef_heapMono₂ addrTy ext hb, hi, hn⟩
  | ctor hv hnp hnf hkey =>
    obtain ⟨b, i, j, hb, hi, hj, hn⟩ := hkey
    exact .ctor (hv.mono ext) hnp hnf ⟨b, i, j, Bytes.repAddressRef_heapMono₂ addrTy ext hb, hi, hj, hn⟩
  | recr hv hnp hni hnm hnmi hrP hmI hrules hkey =>
    obtain ⟨b, i, hb, hi, hn⟩ := hkey
    exact .recr (hv.mono ext) hnp hni hnm hnmi hrP hmI (hrules.mono ext)
      ⟨b, i, Bytes.repAddressRef_heapMono₂ addrTy ext hb, hi, hn⟩

theorem CIPtrRep.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {p : SourceValue F}
    {ci : Ix.Kernel.ConstantInfo .anon} (ext : Heap.Extends h₁ h₂) (r : CIPtrRep κ h₁ p ci) :
    CIPtrRep κ h₂ p ci :=
  let ⟨v, hl, hr⟩ := r; ⟨v, ext.loadValue_eq hl, hr.mono ext⟩

end IxVM.Refinement.Core
