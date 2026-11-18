import IxVMRefinement.Assembly.NativeBlockUnitStep
import IxVMRefinement.Assembly.NativeAliasStepOver
import IxVMRefinement.Binding.ClauseInvariant
import IxVMRefinement.Binding.UnitDefn

/-! # The step of a block whose former is declared at its telescope, in the binding fold's form

The step is stated once (`Typing.NativeUnitStep`, `Assembly/NativeBlockUnitStep.lean`): from
the clause at the store and the limit of the block's check, new constants and one family, with
the clause kept at every admitted store, every limit and every registry. The binding fold
carries the clause with one registry at every record store for its store `R` and every carried
limit within its groups; its unit step is `Binding.OverUnitStep`.

* `NativeInstallOut.atStore`: the install's output at another store, from the new constants as
  that store reads them. The output reads the store in that field only.
* `BlockCert.recordsFor`: the certificate of the new projection table over a store is its
  certificate over every record store for it.
* `nativeUnitStep_of_member_holds`: the step from the walk's member check, kept at every store
  of a family whose members hold the block's records and the run's blobs, where the new
  table's certificate is given over each of them.
* `NativeUnitStep.overUnitStep`: **the binding fold's step.** The block's check is read at one
  record store for `R` and one carried limit within the groups; the registry after the step is
  the registry before, extended by the one family, at every store and limit.
* `overUnitStep_nativeBlockTele`: the binding fold's step from the walk's facts.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)
open Ix.Kernel.Semantics (NativeFam)

/-- **The install's output at another store**, from the new constants as that store reads them:
every other field is a fact about the environments and the run's store. -/
theorem NativeInstallOut.atStore {t : Ix.Kernel.RoleTable} {E₀ Ec E : Ixon.Env} {n m : Nat}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)}
    {p₀ p : Ix.Kernel.NativeParts .anon} {new : List (ConstantInfo .anon)}
    {ty' : Ix.Kernel.Expr .anon} {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}
    (hO : NativeInstallOut t E₀ Ec n env B cb ind blk p₀ new p ty' ctorsA caps)
    (hI : BlockInstall ⟨E, env, t, some m⟩ new B cb ind caps) :
    NativeInstallOut t E₀ E m env B cb ind blk p₀ new p ty' ctorsA caps :=
  { facts := hO.facts
    install := hI
    caps_eq := hO.caps_eq
    nodup := hO.nodup
    fresh := hO.fresh
    reads := hO.reads
    named := hO.named
    ctors := hO.ctors
    lenA := hO.lenA
    nP := hO.nP
    nIdx := hO.nIdx
    nP₀ := hO.nP₀
    nIdx₀ := hO.nIdx₀
    cvT := hO.cvT
    cvT₀ := hO.cvT₀
    ctorNames := hO.ctorNames
    formerFind := hO.formerFind
    ctorFind := hO.ctorFind
    tableName := hO.tableName }

/-- **The certificate of the new projection table over a store is its certificate over every
record store for it.** -/
theorem BlockCert.recordsFor {t : Ix.Kernel.RoleTable} {R E : Ixon.Env}
    {env₂ : Ix.Kernel.Env .anon} {B : _root_.Address} (h : BlockCert t R env₂ B)
    (hRE : RecordsFor R E) : BlockCert t E env₂ B := by
  intro tbl htbl hprop
  obtain ⟨cvC, nP, nF, raw, hctor, hraw, hpos, cert⟩ := h tbl htbl hprop
  exact ⟨cvC, nP, nF, raw, hctor, Guard.ctorRaw_recordsFor hRE hraw, hpos,
    cert.mono (GuardRaw.ofStore_extends_recordsFor hRE)⟩

/-- **The step from the walk's member check, kept at every store of a family that holds the
block's records.** The member's check is read at the store `Ec` and the limit `lc`; every
store in `Stores` holds the block's records and the run's blobs (`hholds`); `hcert` gives, for
every output of the install at one constructor, no index and a sort that tests zero, with the
sorts its table stage ran at as the classifier checked them at `Ec`, the certificate of the new
projection table over every store in `Stores`. -/
theorem nativeUnitStep_of_member_holds {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ Ec : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lc : Option Nat} {bAddr B : _root_.Address}
    {cb : Ixon.Constant} {ind : Ixon.Inductive} {Stores : Ixon.Env → Prop}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ Ec) (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lc)
    (hnat : NativeRouteAt calls B) (htele : FormerAtTele t E₀ B cb ind)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hcov : L1.CanonicalHashCoverage Ec calls)
    (hread : Core.ProjGuardRunReading)
    (hholds : ∀ E, Stores E → HoldsBlock E₀ E B cb ind)
    (hcert : ind.ctors.size = 1 → ind.indices.toNat = 0 →
      ∀ (env : Ix.Kernel.Env .anon) (new blk : List (ConstantInfo .anon))
        (p₀ p : Ix.Kernel.NativeParts .anon) (ty' : Ix.Kernel.Expr .anon)
        (ctorsA : List (ConstantVal .anon × Nat)) (caps : IndCaps .anon),
        NativeInstallOut t E₀ Ec 0 env B cb ind blk p₀ new p ty' ctorsA caps →
        InstallSortsCheckedLim calls t Ec lc env B
          ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ p₀ new p ctorsA →
        Ix.Kernel.Level.isEquiv p.resSort .zero = some true →
        ∀ E, Stores E → BlockCert t E ⟨new ++ env.consts⟩ B) :
    NativeUnitStep.{u} L t envT E₀ Stores Ec lc B cb := by
  refine nativeUnitStep_of_install hL ht hread hS hrec hholds ?_
  intro env Reg hext hnd hC href hfresh
  obtain ⟨blk, p₀, new, p, ty', ctorsA, caps, hO, hpin, hna, hstored, hret, hnp, hSorts, hty,
    hcty⟩ :=
    nativeInstall_of_member ht hS hst hrec hchk hnat htele hfree hinert hcover hcov hext hnd hC
      href hfresh
  refine ⟨blk, p₀, new, p, ty', ctorsA, caps, hO, hpin, hna, hstored, hret, hnp, ?_⟩
  intro E hE
  exact ⟨hO.atStore (hO.install.atStore hst.runBlob (hholds E hE) hty hcty),
    fun h1 h0 hz => hcert h1 h0 env new blk p₀ p ty' ctorsA caps hO hSorts hz E hE⟩

end IxVM.Refinement.Typing

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)
open Ix.Kernel.Semantics (NativeFam)

/-- **The binding fold's step of a one-type native block that registers one family** (module
docstring). `Ec` is a record store for `R` the block's check is read at, at a carried limit
`lc` within `G`; the clause is kept at every record store for `R`; the keys of the record's
constant addresses are free. A constant of the step at a derived key is at no operation's key:
an operation's key is a role key. -/
theorem _root_.IxVM.Refinement.Typing.NativeUnitStep.overUnitStep
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {t : Ix.Kernel.RoleTable}
    {G : Nat → Prop} {R E₀ Ec : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {Stores : Ixon.Env → Prop} {lc : Option Nat} {B : _root_.Address} {cb : Ixon.Constant}
    (hRc : RecordsFor R Ec) (hc : Carried lc) (hl : LimWithin G t lc)
    (hStores : ∀ E, RecordsFor R E → Stores E)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (h : NativeUnitStep.{u} L t envT E₀ Stores Ec lc B cb) :
    OverUnitStep.{u} L t G R envT E₀ B cb := by
  intro env Reg hext hnd hcl href hfresh
  obtain ⟨new, fam, hnd', hfr, hkeep, hnamed, hreads⟩ :=
    h env Reg hext hnd (hcl Ec hRc lc hc hl) href hfresh
  refine ⟨new, fun f => Reg f ∨ f = fam, hnd', hfr,
    fun E hE lim hc' hl' => hkeep E lim Reg (hStores E hE) (hcl E hE lim hc' hl'), ?_, hreads,
    hnamed⟩
  intro ci hci
  rcases hnamed ci hci with ⟨x, hx, hn⟩ | ⟨k, s, hn⟩
  · rw [hn]
    exact not_mem_opNames_of_keyFree (hfree x hx)
  · rw [hn]
    intro hm
    have hb := RoleOps.isBaseKey_of_mem_opNames hm
    exact nomatch hb

/-- **The binding fold's step of a one-type native block whose former is declared at its
telescope, from the walk's facts.** The member's check is the walk's, observed under the role
context at the limit `lim` (a carried limit within `G`); `Ec` is a record store for `R` the
check is read at; `R` holds the block's records and every blob the run loaded. `hread` is the
reading of a projection guard's run; `hcert` gives, for every output of the install at one
constructor, no index and a sort that tests zero, with the sorts its table stage ran at as the
classifier checked them at `Ec`, the certificate of the new projection table over the witness
store `R` (it is then its certificate over every record store for `R`,
`BlockCert.recordsFor`). The run gives that certificate over `Ec` only
(`blockCert_of_install_lim`), and a certificate moves to a store that holds more records, not
to one that holds fewer: over `R` it is a premise. -/
theorem overUnitStep_nativeBlockTele {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
    {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R E₀ Ec : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {bAddr B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {lim : Option Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hRc : RecordsFor R Ec) (hst : StepStore calls t E₀ Ec)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hRblock : recordOf R B = some cb)
    (hRformer : recordOf R (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)))
    (hRctors : ∀ j < ind.ctors.size,
      recordOf R (ctorAddr B 0 j) = some (constructorProjection B 0 j))
    (hblobs : ∀ x b, E₀.blobs.get? x = some b → R.blobs.get? x = some b)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (hcn : Carried lim) (hln : LimWithin G t lim)
    (hnat : NativeRouteAt calls B) (htele : FormerAtTele t E₀ B cb ind)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hcov : L1.CanonicalHashCoverage Ec calls)
    (hread : Core.ProjGuardRunReading)
    (hcert : ind.ctors.size = 1 → ind.indices.toNat = 0 →
      ∀ (env : Ix.Kernel.Env .anon) (new blk : List (ConstantInfo .anon))
        (p₀ p : Ix.Kernel.NativeParts .anon) (ty' : Ix.Kernel.Expr .anon)
        (ctorsA : List (ConstantVal .anon × Nat)) (caps : IndCaps .anon),
        NativeInstallOut t E₀ Ec 0 env B cb ind blk p₀ new p ty' ctorsA caps →
        InstallSortsCheckedLim calls t Ec lim env B
          ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ p₀ new p ctorsA →
        Ix.Kernel.Level.isEquiv p.resSort .zero = some true →
        BlockCert t R ⟨new ++ env.consts⟩ B) :
    OverUnitStep.{u} L t G R envT E₀ B cb :=
  NativeUnitStep.overUnitStep (Stores := fun E => RecordsFor R E) hRc hcn hln (fun E hE => hE)
    hfree
    (nativeUnitStep_of_member_holds hL ht hS hst hrec hchk hnat htele hfree hinert hcover hcov
      hread (fun E hE => holdsBlock_of_recordsFor hE hRblock hRformer hRctors hblobs)
      (fun h1 h0 env new blk p₀ p ty' ctorsA caps hO hSorts hz E hE =>
        (hcert h1 h0 env new blk p₀ p ty' ctorsA caps hO hSorts hz).recordsFor hE))

end IxVM.Refinement.Binding
