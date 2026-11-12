import IxVMRefinement.Core.Specs.Common
import IxC.Kernel.Tier.Ind

/-! # Specs: the functions outside the core that the core calls

* the record loads (`Ingress::get_ci`, `get_ci_cprj`, `get_ci_iprj`): their specs are
  `LoadFacts`' fields (`Good.lean`), so they are discharged from it;
* the decoded block of a record (`Ingress::load_verified_constant`), read shallowly: which kind
  of record, and for a block, its members' kinds (`ConstShapeRep`); the member projection
  addresses of a block (`Ingress::build_recur_addrs`);
* the projection-record addresses IxVM computes by serializing and hashing a projection record
  (`KernelCheck::projection_addr_ctor`, and `KernelDefEq::compute_iprj_addr`'s two calls
  `IxonSerialize::put_constant` and `Blake3::bytes_to_addr`);
* the parent inductive of a recursor (`KernelCheck::rec_to_parent_addr`: the head of its major
  premise's type);
* the modeled route's gates (`KernelModeled::block_is_modeled`, `block_is_multi`, `proj_ctor`,
  `fire_ok`, `fire_compare`, `defeq_list_ok`).

A load's result is related to `c.E` under `Good` (no hashed collision with `c.E`). -/

namespace IxVM.Refinement.Core.Specs.Callees

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

set_option linter.unusedVariables false

/-! ## Decoded records, shallowly -/

abbrev ixConstEnum : String := "Ixon::Constant"
abbrev ixInfoEnum : String := "Ixon::ConstantInfo"
abbrev ixMutEnum : String := "Ixon::MutConst"
/-- `Lists::Node<Ixon::MutConst>`: a block's members. -/
abbrev mutListEnum : String := Obs.Names.«Lists::Node<Ixon::MutConst>»
/-- `Lists::Node<&Ixon::Expr>`: a record's sharing table. -/
abbrev ixExprListEnum : String := Obs.Names.«Lists::Node<&Ixon::Expr>»
/-- `Lists::Node<&Ixon::Univ>`: a record's universe table. -/
abbrev ixUnivListEnum : String := Obs.Names.«Lists::Node<&Ixon::Univ>»

/-- The constructor of `Ixon::MutConst` a block member is. -/
def mutCtor : Ixon.MutConst → String
  | .defn _ => "Defn"
  | .indc _ => "Indc"
  | .recr _ => "Recr"

/-- The constructor of `Ixon::ConstantInfo` a record's info is. -/
def infoCtor : Ixon.ConstantInfo → String
  | .defn _ => "Defn"
  | .recr _ => "Recr"
  | .axio _ => "Axio"
  | .quot _ => "Quot"
  | .cPrj _ => "CPrj"
  | .rPrj _ => "RPrj"
  | .iPrj _ => "IPrj"
  | .dPrj _ => "DPrj"
  | .muts _ => "Muts"

/-- **A block member, by kind**: an `Ixon::MutConst` of the member's constructor. -/
def MutShape (_h : Heap F) (m : Ixon.MutConst) (v : SourceValue F) : Prop :=
  ∃ x, v = .construct ixMutEnum (mutCtor m) [x]

/-- **A block's members, by kind, in order.** -/
abbrev MembersRep (h : Heap F) (ms : List Ixon.MutConst) (p : SourceValue F) : Prop :=
  RepList mutListEnum MutShape h ms p

/-- **A record's info, shallowly**: its constructor, and for a block its members by kind. -/
def InfoShape (h : Heap F) : Ixon.ConstantInfo → SourceValue F → Prop
  | .muts ms, v => ∃ lp, v = .construct ixInfoEnum "Muts" [lp] ∧ MembersRep h ms.toList lp
  | info, v => ∃ x, v = .construct ixInfoEnum (infoCtor info) [x]

/-- **A decoded record, shallowly** (`Ixon::Constant::Mk(info, sharing, refs, univs)`). -/
def ConstShapeRep (h : Heap F) (cst : Ixon.Constant) (v : SourceValue F) : Prop :=
  ∃ info sh rf un, v = .construct ixConstEnum "Mk" [info, sh, rf, un] ∧ InfoShape h cst.info info

/-- An inductive block member. -/
def isIndc : Ixon.MutConst → Bool
  | .indc _ => true
  | _ => false

/-- **The record at `a` in `c.E` is no block of two or more inductives** (what
`block_is_multi`'s and `block_is_modeled`'s answer `0` establish; the latter's nested-occurrence
scan is not read). -/
def FewInductives (c : Ctx) (a : _root_.Address) : Prop :=
  ∀ cst ms, Ix.Cert.recordAt c.E a = some cst → cst.info = .muts ms →
    (ms.toList.filter isIndc).length ≤ 1

/-- The projection record of member `i` (of the given kind) of the block `b`. -/
def memberProjInfo (b : _root_.Address) (i : Nat) : Ixon.MutConst → Ixon.ConstantInfo
  | .defn _ => .dPrj ⟨i.toUInt64, b⟩
  | .indc _ => .iPrj ⟨i.toUInt64, b⟩
  | .recr _ => .rPrj ⟨i.toUInt64, b⟩

/-- **A projection record's info, as IxVM builds it** (`Ixon::ConstantInfo::CPrj(Mk(idx, cidx,
&block))` and the three others; the indices are `UInt64::U64` values). -/
def ProjInfoRep (h : Heap F) : Ixon.ConstantInfo → SourceValue F → Prop
  | .cPrj p, v => ∃ (vi vj bp : SourceValue F) (b : Bytes.Address),
      v = .construct ixInfoEnum "CPrj" [.construct "Ixon::ConstructorProj" "Mk" [vi, vj, bp]] ∧
      RepU64 h p.idx vi ∧ RepU64 h p.cidx vj ∧ RepAddr h b bp ∧ ixAddr b = p.block
  | .iPrj p, v => ∃ (vi bp : SourceValue F) (b : Bytes.Address),
      v = .construct ixInfoEnum "IPrj" [.construct "Ixon::InductiveProj" "Mk" [vi, bp]] ∧
      RepU64 h p.idx vi ∧ RepAddr h b bp ∧ ixAddr b = p.block
  | .rPrj p, v => ∃ (vi bp : SourceValue F) (b : Bytes.Address),
      v = .construct ixInfoEnum "RPrj" [.construct "Ixon::RecursorProj" "Mk" [vi, bp]] ∧
      RepU64 h p.idx vi ∧ RepAddr h b bp ∧ ixAddr b = p.block
  | .dPrj p, v => ∃ (vi bp : SourceValue F) (b : Bytes.Address),
      v = .construct ixInfoEnum "DPrj" [.construct "Ixon::DefinitionProj" "Mk" [vi, bp]] ∧
      RepU64 h p.idx vi ∧ RepAddr h b bp ∧ ixAddr b = p.block
  | _, _ => False

/-- **A projection record with empty tables, as IxVM builds it**
(`Ixon::Constant::Mk(info, &Nil, &Nil, &Nil)`). -/
def ProjConstRep (h : Heap F) (info : Ixon.ConstantInfo) (v : SourceValue F) : Prop :=
  ∃ (iv p1 p2 p3 : SourceValue F), v = .construct ixConstEnum "Mk" [iv, p1, p2, p3] ∧
    ProjInfoRep h info iv ∧
    RepList ixExprListEnum (fun _ (_ : Unit) _ => True) h [] p1 ∧
    RepList addrListEnum (fun _ (_ : Unit) _ => True) h [] p2 ∧
    RepList ixUnivListEnum (fun _ (_ : Unit) _ => True) h [] p3

/-! ## The modeled route's comparands, on the kernel side -/

/-- **The family block of a recursor has at most one inductive** (`KernelModeled::fire_compare`'s
first exit: `block_is_modeled(rec_family_block(r)) = 0`): after the recursor's parameters, the
first motive's type has a binder domain (IxVM reads its last one: `last_binder_dom`) headed by member
`i` of a block `b` that is no block of two or more inductives. -/
def FamilyFew (c : Ctx) (cv : Ix.Kernel.ConstantVal .anon) : Prop :=
  ∃ (np k : Nat) (mdom dom : KExpr) (b : _root_.Address) (i : Nat) (us : List KLevel),
    piDomAt np cv.type = some mdom ∧ piDomAt k mdom = some dom ∧
    dom.getAppFn = .const (c.κ (iprjAddr b i)) us ∧ FewInductives c b

/-- **The comparands a modeled family's rule fires at** (`KernelModeled::fire_compare`'s
comparison, against the kernel's nested-rule instantiations `Tier.nestedPins` and
`recFireComparands`' `.nested` arm): the major's constructor levels are the pinned levels at the
use's levels, and its leading arguments are definitionally equal to the pins at the use's levels
and the recursor's parameters. -/
def FireCompared (c : Ctx) (d : Nat) (cv : Ix.Kernel.ConstantVal .anon) (mI rP : Nat)
    (usK : List KLevel) (As : List KExpr) (M : KExpr) : Prop :=
  ∃ (lvls : List KLevel) (pins : List KExpr) (cj : KKey) (usj : List KLevel),
    Ix.Kernel.Tier.nestedPins cv.type mI rP pins.length = some (lvls, pins) ∧
    M.getAppFn = .const cj usj ∧
    LvEqList usj (lvls.map (Ix.Kernel.Level.subst cv.levelParams usK)) ∧
    Ix.Kernel.Rules.DefEqList c.env d (M.getAppArgs.take pins.length)
      (pins.map fun p => Ix.Kernel.Expr.instSpine (As.take rP) (rP - 1)
        (p.instantiateLevelParams cv.levelParams usK))

/-! ## The loads -/

/-- `Ingress::get_ci(addr)`: the constant at the address's key (`LoadFacts.getCI`). -/
def get_ci : SpecFn := fun c args h r h' calls =>
  ∀ ap (a : Bytes.Address), args = [ap] → Good c calls → RepAddr h a ap →
    ∃ ci, c.env.find? (c.κ (ixAddr a)) = some ci ∧ CIPtrRep c.κ h' r ci

/-- `Ingress::get_ci_cprj(block, i, j)`: the constant at the key of the constructor projection
record `(i, j, block)` (`LoadFacts.getCprj`). -/
def get_ci_cprj : SpecFn := fun c args h r h' calls =>
  ∀ bp (i j : F) (b : Bytes.Address), args = [bp, .field i, .field j] → Good c calls →
    RepAddr h b bp →
      ∃ ci, c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j))) = some ci ∧
        CIPtrRep c.κ h' r ci

/-- `Ingress::get_ci_iprj(block, i)`: the constant at the key of the inductive projection record
`(i, block)` (`LoadFacts.getIprj`). -/
def get_ci_iprj : SpecFn := fun c args h r h' calls =>
  ∀ bp (i : F) (b : Bytes.Address), args = [bp, .field i] → Good c calls → RepAddr h b bp →
    ∃ ci, c.env.find? (c.κ (iprjAddr (ixAddr b) (ZMod.val i))) = some ci ∧ CIPtrRep c.κ h' r ci

/-- `Ingress::load_verified_constant(addr)`: the record of `c.E` at the address, decoded,
shallowly. Nothing is claimed at an address `c.E` holds no record at. -/
def load_verified_constant : SpecFn := fun c args h r h' calls =>
  ∀ ap (a : Bytes.Address), args = [ap] → Good c calls → RepAddr h a ap →
    ∀ cst, Ix.Cert.recordAt c.E (ixAddr a) = some cst → ConstShapeRep h' cst r

/-- `Ingress::build_recur_addrs(members, block)`: the projection-record addresses of the block's
members, in order. -/
def build_recur_addrs : SpecFn := fun c args h r h' calls =>
  ∀ lp bp (ms : List Ixon.MutConst) (b : Bytes.Address), args = [lp, bp] → Good c calls →
    MembersRep h ms lp → RepAddr h b bp →
      ∃ as : List Bytes.Address, RepList addrListEnum RepAddr h' as r ∧
        as.map ixAddr = ms.mapIdx fun i m => projAddr (memberProjInfo (ixAddr b) i m)

/-! ## Projection addresses and parents -/

/-- `KernelCheck::rec_to_parent_addr(ty, np, nm, nmi, ni)` on a represented closed recursor type:
the address of the constant heading its major premise's type (the binder after the
`np + nm + nmi + ni` leading ones). -/
def rec_to_parent_addr : SpecFn := fun c args h r h' calls =>
  ∀ ty (p m mi i : F), args = [ty, .field p, .field m, .field mi, .field i] → Good c calls →
    ∀ T, c.tmc h T ty →
      ∃ (a : Bytes.Address) (dom : KExpr) (us : List KLevel), RepAddr h' a r ∧
        piDomAt (ZMod.val (p + m + mi + i)) T = some dom ∧
        dom.getAppFn = .const (c.κ (ixAddr a)) us

/-- `KernelCheck::projection_addr_ctor(i, j, block)`: the address of the constructor projection
record `(i, j, block)`. -/
def projection_addr_ctor : SpecFn := fun c args h r h' calls =>
  ∀ (i j : F) bp (b : Bytes.Address), args = [.field i, .field j, bp] → Good c calls →
    RepAddr h b bp →
      ∃ a : Bytes.Address, RepAddr h' a r ∧
        ixAddr a = cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j)

/-- `IxonSerialize::put_constant(c, rest)` at a projection record with empty tables (the form
`compute_iprj_addr`, `projection_addr` and `projection_addr_ctor` build): its serialization
(`Ixon.serConstant`) before `rest`. -/
def put_constant : SpecFn := fun c args h r h' calls =>
  ∀ cv tl (info : Ixon.ConstantInfo) (rest : List UInt8), args = [cv, tl] →
    ProjConstRep h info cv → RepBytes h rest tl →
      RepBytes h' ((Ixon.serConstant ⟨info, #[], #[], #[]⟩).data.toList ++ rest) r

/-- `Blake3::bytes_to_addr(bytes)`: the BLAKE3 address of the bytes (`Address.blake3Pure`). -/
def bytes_to_addr : SpecFn := fun c args h r h' calls =>
  ∀ bp (bytes : List UInt8), args = [bp] → RepBytes h bytes bp →
    ∃ a : Bytes.Address, RepAddr h' a r ∧ ixAddr a = Address.blake3Pure ⟨bytes.toArray⟩

/-! ## The modeled route's gates -/

/-- `KernelModeled::block_is_multi(block)`: the answer is `0` or `1` (a caller adds it to a
count), and for a record of `c.E` at the block address it is exact: `1` exactly when the record is
a block of two or more inductives (`FewInductives` at `0`). -/
def block_is_multi : SpecFn := fun c args h r h' calls =>
  ∀ bp (b : Bytes.Address), args = [bp] → Good c calls → RepAddr h b bp →
    (r = .field 0 ∨ r = .field 1) ∧
      ∀ cst, Ix.Cert.recordAt c.E (ixAddr b) = some cst →
        (r = .field 1 ↔ ∃ ms, cst.info = .muts ms ∧ 2 ≤ (ms.toList.filter isIndc).length)

/-- `KernelModeled::block_is_modeled(block)`, for a record of `c.E` at the block address: `1` at
a block of two or more inductives, `0` at a record with no inductive member (a block of none, or
no block). So an answer `0` gives `FewInductives`. At a block of exactly one inductive the answer
is the circuit's scan of its constructors for a nested occurrence, which is not described here
(nothing is claimed for either answer there). -/
def block_is_modeled : SpecFn := fun c args h r h' calls =>
  ∀ bp (b : Bytes.Address), args = [bp] → Good c calls → RepAddr h b bp →
    ∀ cst, Ix.Cert.recordAt c.E (ixAddr b) = some cst →
      ((∃ ms, cst.info = .muts ms ∧ 2 ≤ (ms.toList.filter isIndc).length) → r = .field 1) ∧
      ((∀ ms, cst.info = .muts ms → (ms.toList.filter isIndc).length = 0) → r = .field 0)

/-- `KernelModeled::proj_ctor(block, i)` (it asserts `block_is_modeled(block) = 0`): the block
has at most one inductive, and the result is the constant at the key of the constructor
projection record `(i, 0, block)`. -/
def proj_ctor : SpecFn := fun c args h r h' calls =>
  ∀ bp (i : F) (b : Bytes.Address), args = [bp, .field i] → Good c calls → RepAddr h b bp →
    FewInductives c (ixAddr b) ∧
      ∃ ci, c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) = some ci ∧
        CIPtrRep c.κ h' r ci

/-- `KernelModeled::defeq_list_ok(rc, xs, ys, types)`: a nonzero answer (the code answers `0` or
`1`) means the two lists are pairwise definitionally equal (`DefEqList`). Nothing is claimed
for `0`. -/
def defeq_list_ok : SpecFn := fun c args h r h' calls =>
  ∀ rc xs ys types, args = [rc, xs, ys, types] → Good c calls → c.rc h rc →
    ∀ d Γ, c.types Γ h d types → ∀ As Bs, c.tml d Γ h As xs → c.tml d Γ h Bs ys →
      r ≠ .field 0 → Ix.Kernel.Rules.DefEqList c.env d As Bs

/-- `KernelModeled::fire_compare(rc, head, us, spine, major, types)` at a recursor head
`Const(a, us)`: a nonzero answer means the recursor's family block has at most one inductive
(`FamilyFew`), or the major's comparands are the rule's pinned ones (`FireCompared`). Nothing
is claimed for `0`. -/
def fire_compare : SpecFn := fun c args h r h' calls =>
  ∀ rc head us spine major types, args = [rc, head, us, spine, major, types] → Good c calls →
    c.rc h rc → ∀ ap lp, loadValue h head = .ok (.construct kexprEnum "Const" [ap, lp]) →
    ∀ (a : Bytes.Address) cv mI rP rls, RepAddr h a ap →
      c.env.find? (c.κ (ixAddr a)) = some (.recInfo cv mI rP rls) →
    ∀ usK, LvListRep h usK us → usK.length = cv.levelParams.length →
    ∀ d Γ, c.types Γ h d types → ∀ As M, c.tml d Γ h As spine → c.tm d Γ h M major →
      r ≠ .field 0 → FamilyFew c cv ∨ FireCompared c d cv mI rP usK As M

/-- `KernelModeled::fire_ok(rc, nmot, head, us, spine, major, types)` at a recursor head
`Const(a, us)`: a nonzero answer (its caller fires on any) means the recursor has one motive, or
`fire_compare`'s claim holds.
Nothing is claimed for `0`. -/
def fire_ok : SpecFn := fun c args h r h' calls =>
  ∀ rc nmot head us spine major types, args = [rc, nmot, head, us, spine, major, types] →
    Good c calls → c.rc h rc → ∀ ap lp, loadValue h head = .ok (.construct kexprEnum "Const" [ap, lp]) →
    ∀ (a : Bytes.Address) cv mI rP rls, RepAddr h a ap →
      c.env.find? (c.κ (ixAddr a)) = some (.recInfo cv mI rP rls) →
    ∀ usK, LvListRep h usK us → usK.length = cv.levelParams.length →
    ∀ d Γ, c.types Γ h d types → ∀ As M, c.tml d Γ h As spine → c.tm d Γ h M major →
      r ≠ .field 0 → nmot = .field 1 ∨ FamilyFew c cv ∨ FireCompared c d cv mI rP usK As M

/-! ## The family -/

/-- The functions of this family. -/
inductive Fn where
  | get_ci
  | get_ci_cprj
  | get_ci_iprj
  | load_verified_constant
  | build_recur_addrs
  | rec_to_parent_addr
  | projection_addr_ctor
  | put_constant
  | bytes_to_addr
  | block_is_multi
  | block_is_modeled
  | proj_ctor
  | defeq_list_ok
  | fire_compare
  | fire_ok
  deriving DecidableEq, Repr

/-- The symbol `ObsFn` names each function by. -/
def Fn.name : Fn → String
  | .get_ci => "Ingress::get_ci"
  | .get_ci_cprj => "Ingress::get_ci_cprj"
  | .get_ci_iprj => "Ingress::get_ci_iprj"
  | .load_verified_constant => "Ingress::load_verified_constant"
  | .build_recur_addrs => "Ingress::build_recur_addrs"
  | .rec_to_parent_addr => "KernelCheck::rec_to_parent_addr"
  | .projection_addr_ctor => "KernelCheck::projection_addr_ctor"
  | .put_constant => "IxonSerialize::put_constant"
  | .bytes_to_addr => "Blake3::bytes_to_addr"
  | .block_is_multi => "KernelModeled::block_is_multi"
  | .block_is_modeled => "KernelModeled::block_is_modeled"
  | .proj_ctor => "KernelModeled::proj_ctor"
  | .defeq_list_ok => "KernelModeled::defeq_list_ok"
  | .fire_compare => "KernelModeled::fire_compare"
  | .fire_ok => "KernelModeled::fire_ok"

/-- Each function's spec. -/
def Fn.spec : Fn → SpecFn
  | .get_ci => Specs.Callees.get_ci
  | .get_ci_cprj => Specs.Callees.get_ci_cprj
  | .get_ci_iprj => Specs.Callees.get_ci_iprj
  | .load_verified_constant => Specs.Callees.load_verified_constant
  | .build_recur_addrs => Specs.Callees.build_recur_addrs
  | .rec_to_parent_addr => Specs.Callees.rec_to_parent_addr
  | .projection_addr_ctor => Specs.Callees.projection_addr_ctor
  | .put_constant => Specs.Callees.put_constant
  | .bytes_to_addr => Specs.Callees.bytes_to_addr
  | .block_is_multi => Specs.Callees.block_is_multi
  | .block_is_modeled => Specs.Callees.block_is_modeled
  | .proj_ctor => Specs.Callees.proj_ctor
  | .defeq_list_ok => Specs.Callees.defeq_list_ok
  | .fire_compare => Specs.Callees.fire_compare
  | .fire_ok => Specs.Callees.fire_ok

end IxVM.Refinement.Core.Specs.Callees
