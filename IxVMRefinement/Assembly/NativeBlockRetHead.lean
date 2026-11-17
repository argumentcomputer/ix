import IxVMRefinement.Assembly.NativeBlockOutsRaw
import IxVMRefinement.Assembly.NativeBlockInstallOf
import IxVMRefinement.Assembly.LateRegistry

/-! # The literal return position of a native block's constructors, at every load

When the native block step admits a constructor, `check_ctor_return_type` checks the raw heap
term of its type: `nP + nF` literal `Forall` cells, then a literal application spine over the
family's `Const` cell (`Decl.NativeCtorOut.residual`). The recursor's comparison needs the same
shape at its own loads of the constructor, and its own run does not check it (a `let` at the
return position reads as a spine without arguments).

Every `get_ci_cprj` load of a constructor in calls that hash no collision with the store reads
the record exactly (`LoadedReads.ctor_load_canon`): the loaded type pointer has, cell for cell,
the raw image of the slot's reading under the record's binder plan (`canonRawAnn`), with the
level parameters renamed to positions. The raw type the admission checks is that image
(`ctorOuts_of_member_raw`). So the admission's shape is a fact about the record, and it holds
at every later load.

* `CtorAppHeadConstT`, `CtorRetHeadT`: the heap shapes (same constructors as the recursor
  comparison's `NatAppHeadConstT`, `NatRetHeadT`);
* `ctorRetHeadT_of_rawTmExact`: a raw reading whose first `n` binders are literal and end in a
  constant-headed spine has the heap shape;
* `BlockRawRetHead t E B ind cb`: the store holds the one-member block `cb` at `B`, and each
  constructor slot's raw image has the literal shape (a fact about the store and the table only);
* `BlockRawRetHead.load`, `BlockRawRetHead.ctorRetHeadAt`: the shape at every good load, in the
  form `NatCtorRetHeadT` states (`CtorRetHeadAtT`);
* `blockRawRetHead_of_member`: the producer, from the block step's member check;
* `FamRetHead`, `famRetHead_of_install`, `FamRetHead.ctorRetHeadAt_of_record`: the fact at a
  registered family, and its use at the record data of the family's registry entry.
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)
open Ix.Kernel.Semantics (NativeFam)
open LoadedReads (canonRawAnn)

universe u

/-! ## The heap shape -/

/-- A literal application spine over a literal `Const` cell. -/
inductive CtorAppHeadConstT (h : Heap F) : SourceValue F → Prop where
  | const {addr : Nat} {ap lsp : SourceValue F}
      (cell : h[addr]? = some (.construct Core.kexprEnum "Const" [ap, lsp])) :
      CtorAppHeadConstT h (.ptr (.enum Core.kexprEnum) addr)
  | app {addr : Nat} {fp ap : SourceValue F}
      (cell : h[addr]? = some (.construct Core.kexprEnum "App" [fp, ap]))
      (rf : CtorAppHeadConstT h fp) :
      CtorAppHeadConstT h (.ptr (.enum Core.kexprEnum) addr)

/-- `n` literal `Forall` cells, then a literal application spine over a literal `Const` cell. -/
inductive CtorRetHeadT (h : Heap F) : Nat → SourceValue F → Prop where
  | zero {p : SourceValue F} (hhead : CtorAppHeadConstT h p) : CtorRetHeadT h 0 p
  | succ {n addr : Nat} {xt xb xm : SourceValue F}
      (cell : h[addr]? = some (.construct Core.kexprEnum "Forall" [xt, xb, xm]))
      (hrest : CtorRetHeadT h n xb) :
      CtorRetHeadT h (n + 1) (.ptr (.enum Core.kexprEnum) addr)

/-- At every `get_ci_cprj` load of constructor `j` of member `idx` of the block `b₀`, the loaded
type's first `nP + nF` binders are literal and end in a literal application spine over a literal
`Const` cell (the body of the recursor comparison's `NatCtorRetHeadT`, verbatim). -/
def CtorRetHeadAtT (b₀ : Bytes.Address) (idx nP : Nat)
    (ctors_info : List (Core.KKey × Nat × Core.KExpr × Core.KExpr × List Nat))
    (x_block : SourceValue F) (calls_bound : List (Call F)) : Prop :=
  ∀ (j : Nat), j < ctors_info.length →
    ∀ (p9 : SourceValue F) (h m2 : Heap F) (cs15 : List (Call F))
      (w45 x_cty0 w46 w47 w48 w49 x_nf w50 : SourceValue F),
      (∀ x ∈ cs15, x ∈ calls_bound) →
      Bytes.RepAddressRef Core.addrTy h b₀ x_block →
      ObsFn Core.W "Ingress::get_ci_cprj" [x_block, .field (idx : F), .field (j : F)] h p9 m2
        cs15 →
      loadValue m2 p9 = .ok (.construct Core.kciEnum "Ctor"
        [w45, x_cty0, w46, w47, w48, w49, x_nf, w50]) →
      ∀ info, ctors_info[j]? = some info →
        CtorRetHeadT m2 (nP + info.2.1) x_cty0

/-! ## The shape of a raw reading on the heap -/

/-- A raw application spine over a constant. -/
inductive CtorRawConstSpine : Core.KExpr → Prop where
  | const (c : Core.KKey) (us : List Core.KLevel) : CtorRawConstSpine (.const c us)
  | app {f : Core.KExpr} (a : Core.KExpr) (hf : CtorRawConstSpine f) :
      CtorRawConstSpine (.app f a)

theorem ctorRawConstSpine_mkAppN :
    ∀ (args : List Core.KExpr) {f : Core.KExpr},
      CtorRawConstSpine f → CtorRawConstSpine (Ix.Kernel.Expr.mkAppN f args)
  | [], _, hf => hf
  | a :: as, _, hf => ctorRawConstSpine_mkAppN as (.app a hf)

private theorem ctorRet_stripPis_succ_inv :
    ∀ {e : Core.KExpr} {k : Nat} {bs : List (Core.KExpr × Ix.Kernel.BinderMeta)}
      {body : Core.KExpr}, e.stripPis (k + 1) = some (bs, body) →
      ∃ t b m bs0, e = .forallE t b m ∧ b.stripPis k = some (bs0, body)
  | .forallE t b m, k, _, body, h => by
    simp only [Ix.Kernel.Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs0, body0⟩, hs0, heq⟩ := h
    obtain rfl : body0 = body := congrArg Prod.snd heq
    exact ⟨t, b, m, bs0, rfl, hs0⟩
  | .bvar _, _, _, _, h | .fvar _ _, _, _, _, h | .sort _, _, _, _, h | .const _ _, _, _, _, h
  | .app _ _, _, _, _, h | .lam _ _ _, _, _, _, h | .letE _ _ _ _, _, _, _, h
  | .lit _, _, _, _, h | .proj _ _ _, _, _, _, h => by simp [Ix.Kernel.Expr.stripPis] at h

/-- A raw reading of a constant-headed spine is a literal application spine over a literal
`Const` cell. -/
theorem ctorAppHeadConstT_of_rawTmExact {κ : _root_.Address → Core.KKey} {d : Nat}
    {Γ : Nat → Core.KExpr} {h : Heap F} {k : Nat} {R E : Core.KExpr} {p : SourceValue F}
    (rep : Decl.RawTmExact κ d Γ h k R E p) : CtorRawConstSpine R → CtorAppHeadConstT h p := by
  induction rep with
  | const cell _ _ => exact fun _ => .const cell
  | app cell _ _ ihf _ =>
    intro hs
    cases hs with
    | app _ hf => exact .app cell (ihf hf)
  | bvarLocal => intro hs; cases hs
  | bvarFree => intro hs; cases hs
  | sort => intro hs; cases hs
  | lam => intro hs; cases hs
  | forallE => intro hs; cases hs
  | letE => intro hs; cases hs
  | litNat => intro hs; cases hs
  | litStr => intro hs; cases hs
  | proj => intro hs; cases hs

/-- **A raw reading with a literal return position has the heap shape**: if its first `n`
binders are literal and end in a constant-headed spine, the pointer has `n` literal `Forall`
cells and then a literal application spine over a literal `Const` cell. -/
theorem ctorRetHeadT_of_rawTmExact {κ : _root_.Address → Core.KKey} {d : Nat}
    {Γ : Nat → Core.KExpr} {h : Heap F} :
    ∀ (n : Nat) {k : Nat} {R E : Core.KExpr} {p : SourceValue F}
      {bs : List (Core.KExpr × Ix.Kernel.BinderMeta)} {body : Core.KExpr},
      Decl.RawTmExact κ d Γ h k R E p → R.stripPis n = some (bs, body) →
      CtorRawConstSpine body → CtorRetHeadT h n p
  | 0, _, R, _, _, bs, body, rep, hst, hsp => by
    have e0 : (some ([], R) : Option (List (Core.KExpr × Ix.Kernel.BinderMeta) × Core.KExpr)) =
        some (bs, body) := hst
    have hRb : R = body := congrArg Prod.snd (Option.some.inj e0)
    subst hRb
    exact .zero (ctorAppHeadConstT_of_rawTmExact rep hsp)
  | n + 1, _, R, _, _, bs, body, rep, hst, hsp => by
    obtain ⟨ty, b, m, bs0, rfl, hb⟩ := ctorRet_stripPis_succ_inv hst
    cases rep with
    | forallE cell _ rb _ => exact .succ cell (ctorRetHeadT_of_rawTmExact n rb hb hsp)

/-! ## The fact about the store -/

/-- **The constructors of the one-member block at `B` return literally, on every raw image**:
the store holds the block record `cb` at `B` (one inductive member `ind`, its projection record
at `iprjAddr B 0`, fewer than `2^56` constructors), and for each slot `j`, the constructor's
reading (closed, at its level parameters) has a raw image under the record's binder plan at the
constructor's root whose first `ind.params + fields` binders are literal and end in an
application spine over the family's constant. Only the store and the table are read. -/
structure BlockRawRetHead (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (B : _root_.Address)
    (ind : Ixon.Inductive) (cb : Ixon.Constant) : Prop where
  block : recordOf E B = some cb
  former : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind))
  muts : cb.info = .muts #[.indc ind]
  size : ind.ctors.size < 72057594037927936
  slot : ∀ j < ind.ctors.size, ∃ (ct : Ixon.Constructor) (cty R' : Core.KExpr)
      (rcbs : List (Core.KExpr × Ix.Kernel.BinderMeta)) (rargs : List Core.KExpr),
    ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧
    (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t B #[.indc ind])).read ct.typ = .ok cty ∧
    cty.looseBVarsBounded 0 = true ∧
    cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true ∧
    canonRawAnn cb (List.range ct.lvls.toNat)
      (((L1.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList (ZMod.val (0 : F)) :
        Nat) : F) + 1 + ((j : Nat) : F)) ct.typ cty = some R' ∧
    (Core.posOf (List.range ct.lvls.toNat) R').stripPis (ind.params.toNat + ct.fields.toNat) =
      some (rcbs, Ix.Kernel.Expr.mkAppN
        (.const (Core.keyOf t (Core.iprjAddr B 0))
          ((List.range ind.lvls.toNat).map Ix.Kernel.Level.param)) rargs)

/-- **The shape at one load**: a `get_ci_cprj` load of slot `j` of member `0` of the block at
`B`, in calls that hash no collision with the store and are bounded, loads the slot's
constructor record; its field count is the record's, and its type pointer has `ind.params +
fields` literal `Forall` cells and then a literal application spine over a literal `Const`
cell. -/
theorem BlockRawRetHead.load {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {B : _root_.Address}
    {ind : Ixon.Inductive} {cb : Ixon.Constant} (ht : t.check = .ok ())
    (hR : BlockRawRetHead t E B ind cb)
    {cs : List (Call F)} (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbound : Bounded cs)
    {b₀ : Bytes.Address} (hb₀ : Core.ixAddr b₀ = B) {x_block p9 : SourceValue F}
    {h m2 : Heap F} {j : Nat} (hj : j < ind.ctors.size)
    (hrep : Bytes.RepAddressRef Core.addrTy h b₀ x_block)
    (ev : ObsFn Core.W "Ingress::get_ci_cprj" [x_block, .field 0, .field (j : F)] h p9 m2 cs)
    {w45 x_cty0 w46 w47 w48 w49 x_nf w50 : SourceValue F}
    (hld : loadValue m2 p9 = .ok (.construct Core.kciEnum "Ctor"
      [w45, x_cty0, w46, w47, w48, w49, x_nf, w50])) :
    ∃ ct : Ixon.Constructor, ind.ctors[j]? = some ct ∧ x_nf = .field (ct.fields.toNat : F) ∧
      CtorRetHeadT m2 (ind.params.toNat + ct.fields.toNat) x_cty0 := by
  obtain ⟨ct, cty, R', rcbs, rargs, hct, hcidx, hty, hlbb, hdef, hraw, hshape⟩ := hR.slot j hj
  have hjval : ZMod.val ((j : Nat) : F) = j :=
    ZMod.val_natCast_of_lt (Nat.lt_trans (Nat.lt_trans hj hR.size) (by decide))
  have hmem : (#[.indc ind] : Array Ixon.MutConst)[ZMod.val (0 : F)]? = some (.indc ind) := by
    rw [ZMod.val_zero]
    rfl
  have hct' : ind.ctors[ZMod.val ((j : Nat) : F)]? = some ct := by
    rw [hjval]
    exact hct
  have hcidx' : ct.cidx.toNat = ZMod.val ((j : Nat) : F) := by
    rw [hjval]
    exact hcidx
  have hblock : recordOf E (Core.ixAddr b₀) = some cb := by
    rw [hb₀]
    exact hR.block
  have hty' : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t (Core.ixAddr b₀) #[.indc ind])).read ct.typ = .ok cty := by
    rw [hb₀]
    exact hty
  obtain ⟨tyPtr, blkPtr, b', ty', R'', hld', -, -, -, -, -, -, hrc, -, hrawE, -⟩ :=
    LoadedReads.ctor_load_canon ht hnc hbound hrep ev hblock hR.muts hmem hct' hcidx' hty' hlbb
      hdef
  have hR'' : R'' = R' := Option.some.inj (hrc.symm.trans hraw)
  subst hR''
  have hval := Except.ok.inj (hld.symm.trans hld')
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hval
  obtain ⟨-, hx, -, -, -, -, hnf, -⟩ := hval
  subst hx
  exact ⟨ct, hct, hnf, ctorRetHeadT_of_rawTmExact _ (hrawE 0 (fun _ => default)) hshape
    (ctorRawConstSpine_mkAppN rargs (.const _ _))⟩

/-- **The pairing form** (`NatCtorRetHeadT`'s body, `CtorRetHeadAtT`): at a block `b₀` whose
address is `B`, member `idx = 0`, `nP` the member's parameter count, for every `ctors_info`
whose entries carry the slots' field counts, in calls that hash no collision with the store and
are bounded. -/
theorem BlockRawRetHead.ctorRetHeadAt {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {B : _root_.Address} {ind : Ixon.Inductive} {cb : Ixon.Constant} (ht : t.check = .ok ())
    (hR : BlockRawRetHead t E B ind cb) {b₀ : Bytes.Address} (hb₀ : Core.ixAddr b₀ = B)
    {idx nP : Nat} (hidx : idx = 0) (hnP : nP = ind.params.toNat)
    {ctors_info : List (Core.KKey × Nat × Core.KExpr × Core.KExpr × List Nat)}
    (hinfo : ∀ (j : Nat) (info : Core.KKey × Nat × Core.KExpr × Core.KExpr × List Nat),
      ctors_info[j]? = some info →
      ∃ ct : Ixon.Constructor, ind.ctors[j]? = some ct ∧ info.2.1 = ct.fields.toNat)
    (x_block : SourceValue F) {calls_bound : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] calls_bound) (hbound : Bounded calls_bound) :
    CtorRetHeadAtT b₀ idx nP ctors_info x_block calls_bound := by
  subst hidx hnP
  intro j hj p9 h m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hsub hrep ev hld info hinfo_j
  obtain ⟨ct, hct, hnf⟩ := hinfo j info hinfo_j
  have hjs : j < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
  rw [Nat.cast_zero] at ev
  obtain ⟨ct', hct', -, hhead⟩ := hR.load ht (fun hc => hnc (Core.collision_mono hsub hc))
    (Core.bounded_sub hsub hbound) hb₀ hjs hrep ev hld
  have hctEq : ct' = ct := Option.some.inj (hct'.symm.trans hct)
  subst hctEq
  rw [hnf]
  exact hhead

/-! ## The producer -/

/-- **The block step's member check gives the fact about the store** (inputs of
`ctorOuts_of_member_named`): the admission's residual fixes the shape of the raw type it checks
(`Decl.NativeCtorOut.residual`, at either recursion flag), and that raw type is the slot's raw
image (`ctorOuts_of_member_raw`). -/
theorem blockRawRetHead_of_member {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    {n : Nat} {env : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    {p₀ : Ix.Kernel.NativeParts .anon}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    (hnat : NativeRouteAt calls B) (htele : FormerAtTele t E₀ B cb ind)
    (hblk : BlockReadings t E₀ B ind blk)
    (hp₀ : Ix.Kernel.Semantics.nativePartsNoRec? ind.params.toNat blk = some p₀)
    (hinv : Decl.PrefixInv.{u} E t (some n) env) (hstored : Decl.UsedRefsStored t env cb)
    (hP : HashedBlockProjectionsHeld E) (hkeys : HashKeyed t env)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hcov : L1.CanonicalHashCoverage E calls) (haux : Decl.AuxRootSynced env) :
    BlockRawRetHead t E B ind cb := by
  obtain ⟨ty₀, ty', cvS, bsT, ctorsA, rawTypes, hty, hlbb, hdef, hcT, hcvT, hcvS, hnP₀, hnIdx₀,
    hlenP, hper, hT, hstT, hname, hlenA, hout, hun, hc56, hrawL, -⟩ :=
    ctorOuts_of_member_raw ht hS hst hrec hchk hnat htele hblk hp₀ hinv hstored hP hkeys
      hfresh hfree hcov haux
  have hblockE : recordOf E B = some cb :=
    (recordOf_eq_recordAt_of_decoded hst.decoded B).trans (hst.runRecord B cb hrec.record)
  have hprojE : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)) :=
    (recordOf_eq_recordAt_of_decoded hst.decoded _).trans (hst.runRecord _ _ hrec.former)
  obtain ⟨sortss, -, houts⟩ := hout false
  refine ⟨hblockE, hprojE, hrec.muts, hc56, fun j hj => ?_⟩
  have hjP : j < p₀.ctors.length := by
    rw [hlenP]
    exact hj
  obtain ⟨c, cA, sorts, hc, -, -, hout_j⟩ := houts j hjP
  obtain ⟨ct, cty', hct, hcidx, -, -, -, -, hcf, hread, hl, hd, -, -⟩ := hper j c hc
  obtain ⟨ct', R', hct', hrc, hrj⟩ := hrawL j c hc
  have hctEq : ct' = ct := Option.some.inj (hct'.symm.trans hct)
  rw [hctEq] at hrc hrj
  obtain ⟨rcbs, rargs, -, -, hstR, -⟩ := hout_j.residual
  have hget : rawTypes.getD j default = Core.posOf (List.range ct.lvls.toNat) R' := by
    rw [List.getD_eq_getElem?_getD, hrj]
    rfl
  rw [hget, hnP₀, hcf, hcvT] at hstR
  exact ⟨ct, c.1.type, R', rcbs, rargs, hct, hcidx, hread, hl, hd, hrc, hstR⟩

/-! ## At a registered family -/

/-- **The constructors of a family return literally at every load**: the family's name is the
key of the projection record of member `0` of a one-member block at `B` whose constructors
return literally on every raw image (`BlockRawRetHead`). A fact about the store and the table:
every later step keeps it. -/
def FamRetHead (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (fam : NativeFam .anon) : Prop :=
  ∃ (B : _root_.Address) (ind : Ixon.Inductive) (cb : Ixon.Constant),
    fam.p.cvT.name = Core.keyOf t (Core.iprjAddr B 0) ∧ BlockRawRetHead t E B ind cb

/-- **The family the install registers** (`lateFamAt_of_install`'s family) has the fact. -/
theorem famRetHead_of_install {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)} {p₀ p : Ix.Kernel.NativeParts .anon}
    {new : List (ConstantInfo .anon)} {ty' : Ix.Kernel.Expr .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps)
    (hR : BlockRawRetHead t E B ind cb) :
    FamRetHead t E
      ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩ := by
  refine ⟨B, ind, cb, ?_, hR⟩
  show p.cvT.name = Core.keyOf t (Core.iprjAddr B 0)
  rw [hO.cvT]
  exact hO.cvT₀.1

/-- **The pairing form at a registry entry's record data**: given the fact at a family, and the
data `LateFamAt.record` gives (the projection record at `P` whose key is the family's name, of
member `ip.idx` of the block record at `ip.block`), `CtorRetHeadAtT` holds at every block `b₀`
whose address is `ip.block`, at `idx = ip.idx`, `nP` the family's parameter count, for every
`ctors_info` whose entries carry the member's field counts, in calls that hash no collision with
the store and are bounded. -/
theorem FamRetHead.ctorRetHeadAt_of_record {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {fam : NativeFam .anon} (ht : t.check = .ok ()) (hdec : L1.EnvDecoded E)
    (hF : FamRetHead t E fam)
    {P : _root_.Address} {cm : Ixon.Constant} {ip : Ixon.InductiveProj} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hname : fam.p.cvT.name = keyOf t P) (hP : Ix.Cert.recordAt E P = some cm)
    (hcm : cm.info = .iPrj ip) (hblk : Ix.Cert.recordAt E ip.block = some cb)
    (hms : cb.info = .muts ms) (hmem : ms[ip.idx.toNat]? = some (.indc ind))
    (hnP : fam.p.nP = ind.params.toNat)
    {b₀ : Bytes.Address} (hb₀ : Core.ixAddr b₀ = ip.block)
    {ctors_info : List (Core.KKey × Nat × Core.KExpr × Core.KExpr × List Nat)}
    (hinfo : ∀ (j : Nat) (info : Core.KKey × Nat × Core.KExpr × Core.KExpr × List Nat),
      ctors_info[j]? = some info →
      ∃ ct : Ixon.Constructor, ind.ctors[j]? = some ct ∧ info.2.1 = ct.fields.toNat)
    (x_block : SourceValue F) {calls_bound : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] calls_bound) (hbound : Bounded calls_bound) :
    CtorRetHeadAtT b₀ ip.idx.toNat fam.p.nP ctors_info x_block calls_bound := by
  obtain ⟨B, ind₀, cb₀, hT, hR⟩ := hF
  have hPB : P = Core.iprjAddr B 0 :=
    Assembly.keyOf_injective (x := P) (y := Core.iprjAddr B 0) ht
      ((LoadedReads.keyOf_eq t P).trans (hname.symm.trans hT))
  subst hPB
  have hcm' : cm = memberProjection B 0 (.indc ind₀) :=
    Option.some.inj ((((recordOf_eq_recordAt_of_decoded hdec _).trans hP).symm).trans hR.former)
  subst hcm'
  have hipEq : (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj) = ip := by
    have hinfo0 : (memberProjection B 0 (.indc ind₀)).info =
        .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
    rw [hinfo0] at hcm
    exact Ixon.ConstantInfo.iPrj.inj hcm
  have hipb : ip.block = B := by
    subst hipEq
    rfl
  have hipi : ip.idx.toNat = 0 := by
    subst hipEq
    show ((0 : Nat).toUInt64).toNat = 0
    decide
  have hcb : cb = cb₀ := by
    have h1 : recordOf E B = some cb := by
      rw [← hipb]
      exact (recordOf_eq_recordAt_of_decoded hdec _).trans hblk
    exact Option.some.inj (h1.symm.trans hR.block)
  subst hcb
  have hms' : ms = #[.indc ind₀] := Ixon.ConstantInfo.muts.inj (hms.symm.trans hR.muts)
  subst hms'
  have hind : ind = ind₀ := by
    rw [hipi] at hmem
    have e : (some (.indc ind₀) : Option Ixon.MutConst) = some (.indc ind) := hmem
    exact (Ixon.MutConst.indc.inj (Option.some.inj e)).symm
  subst hind
  exact hR.ctorRetHeadAt ht (hb₀.trans hipb) hipi hnP hinfo x_block hnc hbound

end IxVM.Refinement.Typing
