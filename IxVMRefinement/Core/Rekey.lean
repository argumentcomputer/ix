import IxVMRefinement.Core.Loaded

/-!
# Changing the keying of a represented term

A heap term represented under one keying is represented under another that agrees with it on the
addresses of the term's `Const` and `Proj` cells (`Tm.rekey`). The condition reads the heap, not
the image: a `Let` cell's type is a sub-term of the heap term and no part of its image.

The same for a loaded constant (`CIRep.rekey`): the two keyings agree on the addresses of its
type, value and rule terms, and on every address its own name is the key of.
-/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

/-- **An address occurs in a heap term**: it is the address of a `Const` or `Proj` cell reachable
from the pointer through term cells. -/
inductive AddrIn (h : Heap F) : SourceValue F → Bytes.Address → Prop where
  | const {addr : Nat} {ap lsp : SourceValue F} {a : Bytes.Address}
      (cell : h[addr]? = some (.construct kexprEnum "Const" [ap, lsp]))
      (ra : Bytes.RepAddressRef addrTy h a ap) :
      AddrIn h (.ptr (.enum kexprEnum) addr) a
  | projHead {addr : Nat} {ap ep : SourceValue F} {i : F} {a : Bytes.Address}
      (cell : h[addr]? = some (.construct kexprEnum "Proj" [ap, .field i, ep]))
      (ra : Bytes.RepAddressRef addrTy h a ap) :
      AddrIn h (.ptr (.enum kexprEnum) addr) a
  | projArg {addr : Nat} {ap ep : SourceValue F} {i : F} {a : Bytes.Address}
      (cell : h[addr]? = some (.construct kexprEnum "Proj" [ap, .field i, ep]))
      (sub : AddrIn h ep a) :
      AddrIn h (.ptr (.enum kexprEnum) addr) a
  | appFn {addr : Nat} {fp ap : SourceValue F} {a : Bytes.Address}
      (cell : h[addr]? = some (.construct kexprEnum "App" [fp, ap]))
      (sub : AddrIn h fp a) :
      AddrIn h (.ptr (.enum kexprEnum) addr) a
  | appArg {addr : Nat} {fp ap : SourceValue F} {a : Bytes.Address}
      (cell : h[addr]? = some (.construct kexprEnum "App" [fp, ap]))
      (sub : AddrIn h ap a) :
      AddrIn h (.ptr (.enum kexprEnum) addr) a
  | lamTy {addr : Nat} {tp bp lp : SourceValue F} {a : Bytes.Address}
      (cell : h[addr]? = some (.construct kexprEnum "Lam" [tp, bp, lp]))
      (sub : AddrIn h tp a) :
      AddrIn h (.ptr (.enum kexprEnum) addr) a
  | lamBody {addr : Nat} {tp bp lp : SourceValue F} {a : Bytes.Address}
      (cell : h[addr]? = some (.construct kexprEnum "Lam" [tp, bp, lp]))
      (sub : AddrIn h bp a) :
      AddrIn h (.ptr (.enum kexprEnum) addr) a
  | forallTy {addr : Nat} {tp bp lp : SourceValue F} {a : Bytes.Address}
      (cell : h[addr]? = some (.construct kexprEnum "Forall" [tp, bp, lp]))
      (sub : AddrIn h tp a) :
      AddrIn h (.ptr (.enum kexprEnum) addr) a
  | forallBody {addr : Nat} {tp bp lp : SourceValue F} {a : Bytes.Address}
      (cell : h[addr]? = some (.construct kexprEnum "Forall" [tp, bp, lp]))
      (sub : AddrIn h bp a) :
      AddrIn h (.ptr (.enum kexprEnum) addr) a
  | letTy {addr : Nat} {tp vp bp : SourceValue F} {a : Bytes.Address}
      (cell : h[addr]? = some (.construct kexprEnum "Let" [tp, vp, bp]))
      (sub : AddrIn h tp a) :
      AddrIn h (.ptr (.enum kexprEnum) addr) a
  | letVal {addr : Nat} {tp vp bp : SourceValue F} {a : Bytes.Address}
      (cell : h[addr]? = some (.construct kexprEnum "Let" [tp, vp, bp]))
      (sub : AddrIn h vp a) :
      AddrIn h (.ptr (.enum kexprEnum) addr) a
  | letBody {addr : Nat} {tp vp bp : SourceValue F} {a : Bytes.Address}
      (cell : h[addr]? = some (.construct kexprEnum "Let" [tp, vp, bp]))
      (sub : AddrIn h bp a) :
      AddrIn h (.ptr (.enum kexprEnum) addr) a

/-- **A represented term under another keying**: one that agrees with the first on the
addresses of the term's `Const` and `Proj` cells. The keys of those cells resolve under the second
keying because they resolve under the first. -/
theorem Tm.rekey {κ₁ κ₂ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ₁ d Γ h k E p) :
    (∀ a, AddrIn h p a → κ₂ (ixAddr a) = κ₁ (ixAddr a)) → Tm κ₂ d Γ h k E p := by
  induction rep with
  | bvarLocal cell hs hi => exact fun _ => .bvarLocal cell hs hi
  | bvarFree cell hs hk hd => exact fun _ => .bvarFree cell hs hk hd
  | sort cell rl hu => exact fun _ => .sort cell rl hu
  | @const k addr ap lsp a ls us res cell ra rls hus =>
    intro agree
    have e := agree a (.const cell ra)
    have : Resolved (κ₂ (ixAddr a)) := ⟨by rw [e]; exact res.ne⟩
    rw [← e]
    exact .const cell ra rls hus
  | app cell _ _ ihf iha =>
    exact fun agree => .app cell (ihf fun a m => agree a (.appFn cell m))
      (iha fun a m => agree a (.appArg cell m))
  | lam cell _ _ rl iht ihb =>
    exact fun agree => .lam cell (iht fun a m => agree a (.lamTy cell m))
      (ihb fun a m => agree a (.lamBody cell m)) rl
  | forallE cell _ _ rl iht ihb =>
    exact fun agree => .forallE cell (iht fun a m => agree a (.forallTy cell m))
      (ihb fun a m => agree a (.forallBody cell m)) rl
  | letE cell _ _ _ iht ihv ihb =>
    exact fun agree => .letE cell (iht fun a m => agree a (.letTy cell m))
      (ihv fun a m => agree a (.letVal cell m)) (ihb fun a m => agree a (.letBody cell m))
  | litNat cell rl hc => exact fun _ => .litNat cell rl hc
  | litStr cell rb hs => exact fun _ => .litStr cell rb hs
  | @proj k addr ap ep a i E res cell ra _ ih =>
    intro agree
    have e := agree a (.projHead cell ra)
    have : Resolved (κ₂ (ixAddr a)) := ⟨by rw [e]; exact res.ne⟩
    rw [← e]
    exact .proj cell ra (ih fun a m => agree a (.projArg cell m))

/-- A closed represented term under another keying. -/
theorem TmC.rekey {κ₁ κ₂ : _root_.Address → KKey} {h : Heap F} {E : KExpr} {p : SourceValue F}
    (rep : TmC κ₁ h E p) (agree : ∀ a, AddrIn h p a → κ₂ (ixAddr a) = κ₁ (ixAddr a)) :
    TmC κ₂ h E p :=
  fun d Γ => (rep d Γ).rekey agree

/-- A represented level count and type under another keying. -/
theorem ValRep.rekey {κ₁ κ₂ : _root_.Address → KKey} {h : Heap F} {nl ty : SourceValue F}
    {cv : Ix.Kernel.ConstantVal .anon} (rep : ValRep κ₁ h nl ty cv)
    (agree : ∀ a, AddrIn h ty a → κ₂ (ixAddr a) = κ₁ (ixAddr a)) : ValRep κ₂ h nl ty cv :=
  ⟨rep.1, rep.2.1, rep.2.2.1, TmC.rekey rep.2.2.2 agree⟩

/-- **An address occurs in a rule list**: in the right-hand side of one of its rules. -/
inductive RulesAddrIn (h : Heap F) : SourceValue F → Bytes.Address → Prop where
  | head {addr : Nat} {cidx nf rhs rest : SourceValue F} {a : Bytes.Address}
      (cell : h[addr]? = some (.construct krrListEnum "Cons"
        [.construct krrEnum "Mk" [cidx, nf, rhs], rest]))
      (sub : AddrIn h rhs a) :
      RulesAddrIn h (.ptr (.enum krrListEnum) addr) a
  | tail {addr : Nat} {v rest : SourceValue F} {a : Bytes.Address}
      (cell : h[addr]? = some (.construct krrListEnum "Cons" [v, rest]))
      (sub : RulesAddrIn h rest a) :
      RulesAddrIn h (.ptr (.enum krrListEnum) addr) a

/-- A represented rule list under another keying. -/
theorem RulesRep.rekey {κ₁ κ₂ : _root_.Address → KKey} {h : Heap F}
    {ps : List Ix.Kernel.LevelParam} {j : Nat} {p : SourceValue F}
    {rls : List (Ix.Kernel.RecRule .anon)} (rep : RulesRep κ₁ h ps j p rls) :
    (∀ a, RulesAddrIn h p a → κ₂ (ixAddr a) = κ₁ (ixAddr a)) → RulesRep κ₂ h ps j p rls := by
  induction rep with
  | nil cell => exact fun _ => .nil cell
  | cons cell hr _ ih =>
    intro agree
    obtain ⟨rhs, rfl, hnf, hrhs⟩ := hr
    exact .cons cell ⟨rhs, rfl, hnf, TmC.rekey hrhs fun a m => agree a (.head cell m)⟩
      (ih fun a m => agree a (.tail cell m))

/-- **An address occurs in a loaded constant**: in its type, its value or a rule's right-hand
side. -/
inductive CIAddrIn (h : Heap F) : SourceValue F → Bytes.Address → Prop where
  | axio {nl ty u : SourceValue F} {a : Bytes.Address} (sub : AddrIn h ty a) :
      CIAddrIn h (.construct kciEnum "Axiom" [nl, ty, u]) a
  | opaq {nl ty val u : SourceValue F} {a : Bytes.Address} (sub : AddrIn h ty a) :
      CIAddrIn h (.construct kciEnum "Opaque" [nl, ty, val, u]) a
  | defnTy {nl ty val sf hint : SourceValue F} {a : Bytes.Address} (sub : AddrIn h ty a) :
      CIAddrIn h (.construct kciEnum "Defn" [nl, ty, val, sf, hint]) a
  | defnVal {nl ty val sf hint : SourceValue F} {a : Bytes.Address} (sub : AddrIn h val a) :
      CIAddrIn h (.construct kciEnum "Defn" [nl, ty, val, sf, hint]) a
  | thmTy {nl ty val : SourceValue F} {a : Bytes.Address} (sub : AddrIn h ty a) :
      CIAddrIn h (.construct kciEnum "Thm" [nl, ty, val]) a
  | thmVal {nl ty val : SourceValue F} {a : Bytes.Address} (sub : AddrIn h val a) :
      CIAddrIn h (.construct kciEnum "Thm" [nl, ty, val]) a
  | quot {nl ty kind : SourceValue F} {a : Bytes.Address} (sub : AddrIn h ty a) :
      CIAddrIn h (.construct kciEnum "Quot" [nl, ty, kind]) a
  | induct {nl ty np ni nc u blk idx : SourceValue F} {a : Bytes.Address} (sub : AddrIn h ty a) :
      CIAddrIn h (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) a
  | ctor {nl ty blk ind cidx np nf u : SourceValue F} {a : Bytes.Address} (sub : AddrIn h ty a) :
      CIAddrIn h (.construct kciEnum "Ctor" [nl, ty, blk, ind, cidx, np, nf, u]) a
  | recTy {nl ty np ni nm nmi rules k u blk idx : SourceValue F} {a : Bytes.Address}
      (sub : AddrIn h ty a) :
      CIAddrIn h (.construct kciEnum "Rec" [nl, ty, np, ni, nm, nmi, rules, k, u, blk, idx]) a
  | recRule {nl ty np ni nm nmi rules k u blk idx : SourceValue F} {a : Bytes.Address}
      (sub : RulesAddrIn h rules a) :
      CIAddrIn h (.construct kciEnum "Rec" [nl, ty, np, ni, nm, nmi, rules, k, u, blk, idx]) a

/-- **A loaded constant under another keying**: one that agrees with the first on the addresses
of the constant's terms and on every address the constant's name is the key of. -/
theorem CIRep.rekey {κ₁ κ₂ : _root_.Address → KKey} {h : Heap F} {v : SourceValue F}
    {ci : Ix.Kernel.ConstantInfo .anon} (rep : CIRep κ₁ h v ci)
    (name : ∀ x, ci.toConstantVal.name = κ₁ x → κ₂ x = κ₁ x)
    (agree : ∀ a, CIAddrIn h v a → κ₂ (ixAddr a) = κ₁ (ixAddr a)) : CIRep κ₂ h v ci := by
  cases rep with
  | axio hv => exact .axio (hv.rekey fun a m => agree a (.axio m))
  | opaq hv => exact .opaq (hv.rekey fun a m => agree a (.opaq m))
  | defn hv hV =>
    exact .defn (hv.rekey fun a m => agree a (.defnTy m))
      (TmC.rekey hV fun a m => agree a (.defnVal m))
  | thm hv hV =>
    exact .thm (hv.rekey fun a m => agree a (.thmTy m))
      (TmC.rekey hV fun a m => agree a (.thmVal m))
  | quot hv hk => exact .quot (hv.rekey fun a m => agree a (.quot m)) hk
  | induct hv hcounts hkey =>
    obtain ⟨b, i, hb, hidx, hname⟩ := hkey
    exact .induct (hv.rekey fun a m => agree a (.induct m)) hcounts
      ⟨b, i, hb, hidx, hname.trans (name _ hname).symm⟩
  | ctor hv hnp hnf hcounts hkey =>
    obtain ⟨b, i, j, hb, hind, hcidx, hname⟩ := hkey
    exact .ctor (hv.rekey fun a m => agree a (.ctor m)) hnp hnf hcounts
      ⟨b, i, j, hb, hind, hcidx, hname.trans (name _ hname).symm⟩
  | recr hv hnp hni hnm hnmi hrP hmI hcounts hrules hk hkey =>
    obtain ⟨b, i, hb, hidx, hname⟩ := hkey
    refine .recr (hv.rekey fun a m => agree a (.recTy m)) hnp hni hnm hnmi hrP hmI hcounts
      (hrules.rekey fun a m => agree a (.recRule m)) hk ⟨b, i, hb, hidx, ?_⟩
    rcases hname with hname | hname
    · exact .inl (hname.trans (name _ hname).symm)
    · exact .inr (hname.trans (name _ hname).symm)

/-- A pointer to a loaded constant under another keying. -/
theorem CIPtrRep.rekey {κ₁ κ₂ : _root_.Address → KKey} {h : Heap F} {p : SourceValue F}
    {ci : Ix.Kernel.ConstantInfo .anon} (rep : CIPtrRep κ₁ h p ci)
    (name : ∀ x, ci.toConstantVal.name = κ₁ x → κ₂ x = κ₁ x)
    (agree : ∀ v, loadValue h p = .ok v → ∀ a, CIAddrIn h v a → κ₂ (ixAddr a) = κ₁ (ixAddr a)) :
    CIPtrRep κ₂ h p ci := by
  obtain ⟨v, hld, hrep⟩ := rep
  exact ⟨v, hld, hrep.rekey name (agree v hld)⟩

end IxVM.Refinement.Core
