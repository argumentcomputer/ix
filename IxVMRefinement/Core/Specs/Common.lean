import IxVMRefinement.Core.Seams
import IxC.Kernel.Rules.Rel

/-! # The spec vocabulary, and the conventions every spec statement follows

The registry (`IxVMRefinement/Core/Registry.lean`) has one spec per function of the core and of
the functions the core calls, one file per family under `IxVMRefinement/Core/Specs/`. Each
family file defines `Fn` (an enumeration of its functions), `Fn.name` (the function's symbol,
as `ObsFn` names it) and `Fn.spec : Fn → SpecFn`, and one `def` per spec, named after the
function.

**Conventions.**

1. A spec is `fun c args h r h' calls => ∀ <arguments>, args = [<arguments>] → Good c calls →
   <hypotheses on the inputs, at the heap h> → <claim on the result r, at the heap h'>`.
2. A role context `rc` is related by `c.rc h rc` (`RCRep c.t h rc`); a context list `types` by
   `c.types Γ h d types` (`TypesRep`), for the same `d Γ` as the terms. A function that takes
   both is stated for every opening depth `d` and ghost context `Γ` at which its inputs are
   represented: `∀ d Γ, c.types Γ h d types → ∀ E, c.tm d Γ h E e → …`.
3. Terms: `c.tm d Γ h E e` (local depth `0`), `c.tmk d Γ k h E e` under `k` local binders,
   `c.tml d Γ h Es l` for term lists, `c.tmc h E e` for closed terms. Levels: `LvRep h u p`,
   `LvListRep h us p` (up to semantic equality). Addresses: `Bytes.RepAddressRef addrTy h a p`
   (the kernel key of the constant there is `c.κ (ixAddr a)`). Loaded constants:
   `CIRep c.κ h v ci` (the value), `CIPtrRep c.κ h p ci` (the pointer).
4. A result term is existential: `∃ E', c.tm d Γ h' E' r ∧ <rule> E E'`, with the kernel's rules
   (`Red`, `DefEq`, `Infer`, `Certs`, `DefEqList`) at `c.env` and depth `d`.
5. A yes/no answer claims something for its positive value only; nothing is claimed for `0`
   unless the spec says so explicitly (and then the circuit must decide it completely). A
   tagged result `(tag, x)` claims for `tag = 1` (or the tags the spec names) only.
6. Counts are field elements; a spec that reads one as a natural says so (`ZMod.val n`), and a
   proof bounds it through the ROM: `Bounded` gives a valid ROM of at most `2^39` addresses
   carrying the calls, and the cells of a list are at pairwise different addresses
   (`Core/RomBound.lean`).
7. Specs never mention a function's own calls beyond `Good c calls`.

A step lemma for `f` (in the package that owns `f`) has the form
`theorem f_step (c : Ctx) (hc : CoreFacts c) {args h r h' calls}
  (ev : ObsFn W "<f's symbol>" args h r h' calls) (ih : IH c calls) : <f's spec> c args h r h' calls`. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

/-! ## Abbreviations over a context -/

/-- A top-level term. -/
abbrev Ctx.tm (c : Ctx) (d : Nat) (Γ : Nat → KExpr) (h : Heap F) (E : KExpr)
    (p : SourceValue F) : Prop :=
  Tm c.κ d Γ h 0 E p

/-- A term under `k` local binders. -/
abbrev Ctx.tmk (c : Ctx) (d : Nat) (Γ : Nat → KExpr) (k : Nat) (h : Heap F) (E : KExpr)
    (p : SourceValue F) : Prop :=
  Tm c.κ d Γ h k E p

/-- A list of top-level terms. -/
abbrev Ctx.tml (c : Ctx) (d : Nat) (Γ : Nat → KExpr) (h : Heap F) (Es : List KExpr)
    (p : SourceValue F) : Prop :=
  TmL c.κ d Γ h Es p

/-- A closed term. -/
abbrev Ctx.tmc (c : Ctx) (h : Heap F) (E : KExpr) (p : SourceValue F) : Prop :=
  TmC c.κ h E p

/-- The role context reads the table. -/
abbrev Ctx.rc (c : Ctx) (h : Heap F) (rc : SourceValue F) : Prop := RCRep c.t h rc

/-- The context list is a segment of `Γ` ending at `d`. -/
abbrev Ctx.types (c : Ctx) (Γ : Nat → KExpr) (h : Heap F) (d : Nat) (types : SourceValue F) :
    Prop :=
  TypesRep c.κ Γ h d types

/-- A loaded constant value. -/
abbrev Ctx.ci (c : Ctx) (h : Heap F) (v : SourceValue F) (ci : Ix.Kernel.ConstantInfo .anon) :
    Prop :=
  CIRep c.κ h v ci

/-- An address. -/
abbrev RepAddr (h : Heap F) (a : Bytes.Address) (p : SourceValue F) : Prop :=
  Bytes.RepAddressRef addrTy h a p

/-- A `KernelTypes::KLimbs` limb list read as its value. -/
def RepLimbs (h : Heap F) (n : Nat) (p : SourceValue F) : Prop :=
  ∃ limbs, RepList limbListEnum RepU64 h limbs p ∧ limbsVal limbs = n

/-- A byte stream. -/
abbrev RepBytes (h : Heap F) (bytes : List UInt8) (p : SourceValue F) : Prop :=
  Bytes.RepByteStream byteListEnum h bytes p

/-- The symbol of an instance of a generic function. -/
abbrev inst (f : String) (ts : List Generic.Ty) : String := (Instance.mk f ts).symbol

end IxVM.Refinement.Core
