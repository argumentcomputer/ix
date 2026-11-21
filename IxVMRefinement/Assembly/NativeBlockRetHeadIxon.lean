import IxVMRefinement.Assembly.NativeBlockRetHead

/-! # The literal return of a native block's constructors, on the record's Ixon syntax

`NativeBlockRetHead.lean` reads the admission's return shape off the record through the raw
image of each constructor's reading. The same fact can be stated on the record's own syntax: the
type of each constructor is, through the record's sharing table, `ind.params + fields` literal
`all` binders and then an application spine over a reference. A load converts the Ixon
expression cell for cell (`Ingress.RawConvExpr`: `all`, `app`, `ref`/`recur` become `Forall`, `App`,
`Const` cells, every other node a cell of another tag, and a `share` node the cell of its
target), so a literal heap shape at one load reads back as the syntactic shape.

* `BlockIxonAppHeadRef`, `BlockIxonRetHead`: the syntactic shapes;
* `blockIxonRetHead_of_conv`: a converted term with the heap shape has the syntactic shape;
* `BlockCtorIxonRetHead cb ind`: every constructor of `ind` has it in `cb`;
* `blockCtorIxonRetHead_of_member`: from the block step's member check (one load per slot, the
  heap shape there by `BlockRawRetHead.load`);
* `BlockRawRetHead.record_eq`: the record data of a registry entry at the family's key is the
  block's;
* `FamIxonRetHead`, `famIxonRetHead_of_block`, `famIxonRetHead_of_member`: the fact at every
  record data a registry entry's key can name.
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

universe u

/-! ## The syntactic shape -/

/-- An Ixon expression that is, through the sharing table, an application spine over a
reference (`ref` or `recur`). -/
inductive BlockIxonAppHeadRef (sharing : List Ixon.Expr) : Ixon.Expr → Prop
  | ref {i : UInt64} {us : Array UInt64} : BlockIxonAppHeadRef sharing (.ref i us)
  | recur {i : UInt64} {us : Array UInt64} : BlockIxonAppHeadRef sharing (.recur i us)
  | app {f a : Ixon.Expr} : BlockIxonAppHeadRef sharing f → BlockIxonAppHeadRef sharing (.app f a)
  | share {idx : UInt64} {s : Ixon.Expr} : sharing[idx.toNat]? = some s →
      BlockIxonAppHeadRef sharing s → BlockIxonAppHeadRef sharing (.share idx)

/-- An Ixon expression that is, through the sharing table, `n` literal `all` binders and then an
application spine over a reference. -/
inductive BlockIxonRetHead (sharing : List Ixon.Expr) : Nat → Ixon.Expr → Prop
  | zero {e : Ixon.Expr} : BlockIxonAppHeadRef sharing e → BlockIxonRetHead sharing 0 e
  | all {n : Nat} {ty body : Ixon.Expr} : BlockIxonRetHead sharing n body →
      BlockIxonRetHead sharing (n + 1) (.all ty body)
  | share {n : Nat} {idx : UInt64} {s : Ixon.Expr} : sharing[idx.toNat]? = some s →
      BlockIxonRetHead sharing n s → BlockIxonRetHead sharing n (.share idx)

/-- **The constructors of member `ind` of the block record `cb` return literally**: each
constructor's type is, through `cb`'s sharing table, `ind.params + fields` literal binders and
then an application spine over a reference. -/
def BlockCtorIxonRetHead (cb : Ixon.Constant) (ind : Ixon.Inductive) : Prop :=
  ∀ (j : Nat) (ct : Ixon.Constructor), ind.ctors[j]? = some ct →
    BlockIxonRetHead cb.sharing.toList (ind.params.toNat + ct.fields.toNat) ct.typ

/-- **The constructors of a family return literally, at every record data its key names**: at
the member record whose address the family's name is the key of (its projection record at `P`,
of member `ip.idx` of the block record at `ip.block`), `BlockCtorIxonRetHead`. -/
def FamIxonRetHead (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (fam : NativeFam .anon) : Prop :=
  ∀ (P : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj) (cb : Ixon.Constant)
    (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
    fam.p.cvT.name = keyOf t P → Ix.Cert.recordAt E P = some cm → cm.info = .iPrj ip →
    Ix.Cert.recordAt E ip.block = some cb → cb.info = .muts ms →
    ms[ip.idx.toNat]? = some (.indc ind) → BlockCtorIxonRetHead cb ind

/-! ## From the heap shape back to the syntax -/

private theorem retHeadIxon_cell_tag {h : Heap F} {addr : Nat} {t₁ t₂ : String}
    {xs ys : List (SourceValue F)}
    (c₁ : h[addr]? = some (.construct Core.kexprEnum t₁ xs))
    (c₂ : h[addr]? = some (.construct Core.kexprEnum t₂ ys)) : t₁ = t₂ := by
  rw [c₁] at c₂
  injection c₂ with c₂
  injection c₂ with _ e _

private theorem retHeadIxon_cell_args {h : Heap F} {addr : Nat} {t₁ t₂ : String}
    {xs ys : List (SourceValue F)}
    (c₁ : h[addr]? = some (.construct Core.kexprEnum t₁ xs))
    (c₂ : h[addr]? = some (.construct Core.kexprEnum t₂ ys)) : xs = ys := by
  rw [c₁] at c₂
  injection c₂ with c₂
  injection c₂ with _ _ e

private theorem retHeadIxon_appHead_tag {h : Heap F} {addr : Nat} {t : String}
    {xs : List (SourceValue F)} (cell : h[addr]? = some (.construct Core.kexprEnum t xs))
    (hh : CtorAppHeadConstT h (.ptr (.enum Core.kexprEnum) addr)) : t = "Const" ∨ t = "App" := by
  cases hh with
  | const cell' => exact .inl (retHeadIxon_cell_tag cell cell')
  | app cell' _ => exact .inr (retHeadIxon_cell_tag cell cell')

private theorem retHeadIxon_retHead_tag {h : Heap F} {addr n : Nat} {t : String}
    {xs : List (SourceValue F)} (cell : h[addr]? = some (.construct Core.kexprEnum t xs))
    (hr : CtorRetHeadT h n (.ptr (.enum Core.kexprEnum) addr)) :
    t = "Const" ∨ t = "App" ∨ t = "Forall" := by
  cases hr with
  | zero hh =>
    rcases retHeadIxon_appHead_tag cell hh with e | e
    · exact .inl e
    · exact .inr (.inl e)
  | succ cell' _ => exact .inr (.inr (retHeadIxon_cell_tag cell cell'))

/-- A converted term whose pointer is a literal application spine over a literal `Const` cell
is, through the sharing table, an application spine over a reference. -/
theorem blockIxonAppHeadRef_of_conv {refs recurAddrs : List _root_.Address}
    {univs : List Ixon.Univ} {sharing : List Ixon.Expr}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {bound : Nat} {e : Ixon.Expr}
    {p : SourceValue F}
    (raw : Ingress.RawConvExpr refs recurAddrs univs sharing blobs h bound e p) :
    CtorAppHeadConstT h p → BlockIxonAppHeadRef sharing e := by
  induction raw with
  | ref => exact fun _ => .ref
  | recur => exact fun _ => .recur
  | app rf ra cell ihf iha =>
    intro hh
    cases hh with
    | const cell' => exact absurd (retHeadIxon_cell_tag cell cell') (by decide)
    | app cell' rf' =>
      have e := retHeadIxon_cell_args cell cell'
      injection e with e1 _
      subst e1
      exact .app (ihf rf')
  | share _ hsh _ ih => exact fun hh => .share hsh (ih hh)
  | var _ cell => exact fun hh => absurd (retHeadIxon_appHead_tag cell hh) (by decide)
  | sort _ _ _ cell => exact fun hh => absurd (retHeadIxon_appHead_tag cell hh) (by decide)
  | prj _ _ _ _ _ _ cell _ => exact fun hh => absurd (retHeadIxon_appHead_tag cell hh) (by decide)
  | str _ _ _ _ _ cell => exact fun hh => absurd (retHeadIxon_appHead_tag cell hh) (by decide)
  | nat _ _ _ _ _ _ _ cell =>
    exact fun hh => absurd (retHeadIxon_appHead_tag cell hh) (by decide)
  | lam _ _ _ cell _ _ => exact fun hh => absurd (retHeadIxon_appHead_tag cell hh) (by decide)
  | all _ _ _ cell _ _ => exact fun hh => absurd (retHeadIxon_appHead_tag cell hh) (by decide)
  | letE _ _ _ cell _ _ _ =>
    exact fun hh => absurd (retHeadIxon_appHead_tag cell hh) (by decide)

/-- **A converted term with the heap shape has the syntactic shape**: if the pointer has `n`
literal `Forall` cells and then a literal application spine over a literal `Const` cell, the
Ixon expression is, through the sharing table, `n` literal `all` binders and then an
application spine over a reference. -/
theorem blockIxonRetHead_of_conv {refs recurAddrs : List _root_.Address}
    {univs : List Ixon.Univ} {sharing : List Ixon.Expr}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {bound : Nat} {e : Ixon.Expr}
    {p : SourceValue F}
    (raw : Ingress.RawConvExpr refs recurAddrs univs sharing blobs h bound e p) :
    ∀ {n : Nat}, CtorRetHeadT h n p → BlockIxonRetHead sharing n e := by
  induction raw with
  | ref _ _ _ _ _ _ cell =>
    intro n hr
    cases hr with
    | zero hh => exact .zero .ref
    | succ cell' _ => exact absurd (retHeadIxon_cell_tag cell cell') (by decide)
  | recur _ _ _ _ _ _ cell =>
    intro n hr
    cases hr with
    | zero hh => exact .zero .recur
    | succ cell' _ => exact absurd (retHeadIxon_cell_tag cell cell') (by decide)
  | app rf ra cell ihf iha =>
    intro n hr
    cases hr with
    | zero hh => exact .zero (blockIxonAppHeadRef_of_conv (.app rf ra cell) hh)
    | succ cell' _ => exact absurd (retHeadIxon_cell_tag cell cell') (by decide)
  | all _ _ _ cell iht ihb =>
    intro n hr
    cases hr with
    | zero hh => exact absurd (retHeadIxon_appHead_tag cell hh) (by decide)
    | succ cell' hrest =>
      have e := retHeadIxon_cell_args cell cell'
      injection e with _ e2
      injection e2 with e2 _
      subst e2
      exact .all (ihb hrest)
  | share _ hsh _ ih => exact fun hr => .share hsh (ih hr)
  | var _ cell => exact fun hr => absurd (retHeadIxon_retHead_tag cell hr) (by decide)
  | sort _ _ _ cell => exact fun hr => absurd (retHeadIxon_retHead_tag cell hr) (by decide)
  | prj _ _ _ _ _ _ cell _ =>
    exact fun hr => absurd (retHeadIxon_retHead_tag cell hr) (by decide)
  | str _ _ _ _ _ cell => exact fun hr => absurd (retHeadIxon_retHead_tag cell hr) (by decide)
  | nat _ _ _ _ _ _ _ cell =>
    exact fun hr => absurd (retHeadIxon_retHead_tag cell hr) (by decide)
  | lam _ _ _ cell _ _ => exact fun hr => absurd (retHeadIxon_retHead_tag cell hr) (by decide)
  | letE _ _ _ cell _ _ _ =>
    exact fun hr => absurd (retHeadIxon_retHead_tag cell hr) (by decide)

/-! ## The producer -/

/-- **The block step's member check gives the syntactic fact** (inputs of
`ctorOuts_of_member_named`): the member check loads each slot; at that load the converted type
has the heap shape (`BlockRawRetHead.load`), so the constructor's Ixon type has the syntactic
shape. -/
theorem blockCtorIxonRetHead_of_member {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
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
    (hcov : Ingress.CanonicalHashCoverage E calls) (haux : Decl.AuxRootSynced env) :
    BlockCtorIxonRetHead cb ind := by
  have hR := blockRawRetHead_of_member ht hS hst hrec hchk hnat htele hblk hp₀ hinv hstored hP
    hkeys hfresh hfree hcov haux
  obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hloads⟩ :=
    ctorOuts_of_member_raw ht hS hst hrec hchk hnat htele hblk hp₀ hinv hstored hP hkeys
      hfresh hfree hcov haux
  intro j ct hct
  have hj : j < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
  obtain ⟨bp, ptr, h, h', cs, b, ev, hsub, hrep, hbB⟩ := hloads j hj
  have hg : Core.Good ⟨E, env, t, some n⟩ cs := (hst.good env (some n)).sub hsub
  obtain ⟨-, -, -, blkBytes, cb', ms', ind', ct', blobs, v, hhB, haB, hexB, -, hcb', hms', hct',
    -, hldv, raw⟩ := Ingress.get_ci_cprj_spec hg.2 hrep ev
  -- the block record the load decoded is `cb`
  have hblock : recordOf E (Core.ixAddr b) = some cb := by
    rw [hbB]
    exact hR.block
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hblock
  have hbytes : blkBytes = lcB.rawBytes := Core.load_escape hgetB hg.1 blkBytes hhB haB
  have hcbEq : cb = cb' := by
    rw [hbytes, hdecB] at hexB
    exact Except.ok.inj hexB
  subst hcbEq
  have hmsEq : ms' = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hR.muts)
  subst hmsEq
  have hindEq : ind' = ind := by
    rw [ZMod.val_zero] at hms'
    have e : (some (.indc ind) : Option Ixon.MutConst) = some (.indc ind') := hms'
    exact (Ixon.MutConst.indc.inj (Option.some.inj e)).symm
  subst hindEq
  have hjval : ZMod.val ((j : Nat) : F) = j :=
    ZMod.val_natCast_of_lt (Nat.lt_trans (Nat.lt_trans hj hR.size) (by decide))
  have hctEq : ct' = ct := by
    rw [hjval, Array.getElem?_toList] at hct'
    exact Option.some.inj (hct'.symm.trans hct)
  obtain ⟨-, -, -, -, -, tyPtr, blkPtr, b'', -, -, hv, hconv⟩ := raw
  rw [hctEq] at hconv
  subst hv
  obtain ⟨ct'', hct'', -, hret⟩ := hR.load ht hg.1 hg.2 hbB hj hrep ev hldv
  have hc2 : ct'' = ct := Option.some.inj (hct''.symm.trans hct)
  rw [hc2] at hret
  exact blockIxonRetHead_of_conv hconv hret

/-! ## At a registered family -/

/-- **The record data a registry entry's key names is the block's**: if the key of `P` is the
key of the block's former, the projection record at `P` is member `0` of the block record at
`B`, which is `cb` with the one member `ind`. -/
theorem BlockRawRetHead.record_eq {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {B : _root_.Address}
    {ind : Ixon.Inductive} {cb : Ixon.Constant} (ht : t.check = .ok ()) (hdec : Ingress.EnvDecoded E)
    (hR : BlockRawRetHead t E B ind cb)
    {P : _root_.Address} {cm : Ixon.Constant} {ip : Ixon.InductiveProj} {cb' : Ixon.Constant}
    {ms : Array Ixon.MutConst} {ind' : Ixon.Inductive}
    (hkey : keyOf t P = Core.keyOf t (Core.iprjAddr B 0)) (hP : Ix.Cert.recordAt E P = some cm)
    (hcm : cm.info = .iPrj ip) (hblk : Ix.Cert.recordAt E ip.block = some cb')
    (hms : cb'.info = .muts ms) (hmem : ms[ip.idx.toNat]? = some (.indc ind')) :
    ip.block = B ∧ ip.idx.toNat = 0 ∧ cb' = cb ∧ ind' = ind := by
  have hPB : P = Core.iprjAddr B 0 :=
    Assembly.keyOf_injective (x := P) (y := Core.iprjAddr B 0) ht
      ((LoadedReads.keyOf_eq t P).trans hkey)
  subst hPB
  have hcm' : cm = memberProjection B 0 (.indc ind) :=
    Option.some.inj ((((recordOf_eq_recordAt_of_decoded hdec _).trans hP).symm).trans hR.former)
  subst hcm'
  have hipEq : (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj) = ip := by
    have hinfo0 : (memberProjection B 0 (.indc ind)).info =
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
  have hcb : cb' = cb := by
    have h1 : recordOf E B = some cb' := by
      rw [← hipb]
      exact (recordOf_eq_recordAt_of_decoded hdec _).trans hblk
    exact Option.some.inj (h1.symm.trans hR.block)
  refine ⟨hipb, hipi, hcb, ?_⟩
  rw [hcb, hR.muts] at hms
  have hms' : ms = #[.indc ind] := (Ixon.ConstantInfo.muts.inj hms).symm
  subst hms'
  rw [hipi] at hmem
  have e : (some (.indc ind) : Option Ixon.MutConst) = some (.indc ind') := hmem
  exact (Ixon.MutConst.indc.inj (Option.some.inj e)).symm

/-- **A family named by the block's former has the syntactic fact at every record data its key
names.** -/
theorem famIxonRetHead_of_block {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {B : _root_.Address}
    {ind : Ixon.Inductive} {cb : Ixon.Constant} (ht : t.check = .ok ()) (hdec : Ingress.EnvDecoded E)
    (hR : BlockRawRetHead t E B ind cb) (hI : BlockCtorIxonRetHead cb ind)
    {fam : NativeFam .anon} (hT : fam.p.cvT.name = Core.keyOf t (Core.iprjAddr B 0)) :
    FamIxonRetHead t E fam := by
  intro P cm ip cb' ms ind' hname hP hcm hblk hms hmem
  obtain ⟨-, -, hcb, hind⟩ := hR.record_eq ht hdec (hname.symm.trans hT) hP hcm hblk hms hmem
  rw [hcb, hind]
  exact hI

/-- **The family the install registers** (`lateFamAt_of_install`'s family) **has the syntactic
fact**, from the block step's member check. -/
theorem famIxonRetHead_of_member {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    {n : Nat} {env : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    {p₀ p : Ix.Kernel.NativeParts .anon} {new : List (ConstantInfo .anon)}
    {ty' : Ix.Kernel.Expr .anon} {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}
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
    (hcov : Ingress.CanonicalHashCoverage E calls) (haux : Decl.AuxRootSynced env)
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps) :
    FamIxonRetHead t E
      ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩ := by
  have hR := blockRawRetHead_of_member ht hS hst hrec hchk hnat htele hblk hp₀ hinv hstored hP
    hkeys hfresh hfree hcov haux
  have hI := blockCtorIxonRetHead_of_member ht hS hst hrec hchk hnat htele hblk hp₀ hinv hstored
    hP hkeys hfresh hfree hcov haux
  refine famIxonRetHead_of_block ht hst.decoded hR hI ?_
  show p.cvT.name = Core.keyOf t (Core.iprjAddr B 0)
  rw [hO.cvT]
  exact hO.cvT₀.1

end IxVM.Refinement.Typing
