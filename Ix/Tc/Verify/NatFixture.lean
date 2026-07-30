import Ix.Tc.Verify.Run
import Ix.Tc.Verify.Whnf

/-!
# G2a ambient-Nat fixture

This file instantiates `InductiveOracle` with a small, closed Theory model of
`Nat`, `Nat.zero`, and `Nat.succ`.  The concrete catalog entries retain their
inductive/constructor kinds, while the Theory model contains the semantic
constants those entries denote.  The constants are installed through
object-language `VDecl.axiom` steps; those are ordinary constructors of the
Theory judgment, not new Lean axioms.  This is deliberately an ambient model:
it does not claim an eliminator or pretend that Lean4Lean's still-opaque
`VEnv.addInduct` has been verified.

The fixture then promotes one ordinary axiom whose type is `Nat` and leaves a
second, raw-translatable but ill-typed axiom pending.  Thus adding an ambient
inductive family does not collapse the pending/trusted boundary established
in G1. G3a first instantiated finite run support for lift, substitution, and
universe instantiation. As in the G1
adversarial fixture, fixed distinct addresses keep this logical model
independent of the Blake3 FFI; it establishes semantic
inhabitation, not ingress hash-integrity or Rust parity. G3b extends that
witness to direct expression/universe interning, every currently formalized
walker family, and a non-empty `ExecutionRequests` certificate for the exact
same request list.
-/

namespace Ix.Tc

open Lean4Lean (VConstant VConstVal VDecl VEnv VExpr VLevel)

namespace AmbientNat

def address (byte : UInt8) : Address :=
  ⟨⟨Array.replicate 32 byte⟩⟩

def natAddress : Address := address 10
def zeroAddress : Address := address 11
def succAddress : Address := address 12
def goodAddress : Address := address 13
def iotaAddress : Address := address 14

def natId : KId .anon := ⟨natAddress, ()⟩
def zeroId : KId .anon := ⟨zeroAddress, ()⟩
def succId : KId .anon := ⟨succAddress, ()⟩
def goodId : KId .anon := ⟨goodAddress, ()⟩
def iotaId : KId .anon := ⟨iotaAddress, ()⟩

def natName : Lean.Name := `Nat
def zeroName : Lean.Name := `Nat.zero
def succName : Lean.Name := `Nat.succ
def goodName : Lean.Name := `Ix.Tc.Verify.ambientNatWitness

def info (addr : Address) : ExprInfo .anon where
  addr := addr
  lbr := 0
  count0 := 0
  hasFVars := false
  mdata := ()
  metaAddr := ()

def zeroLevel : KUniv .anon := .zero natAddress
def oneLevel : KUniv .anon := .succ zeroLevel zeroAddress

def natType : KExpr .anon := .sort oneLevel (info natAddress)
def natRef : KExpr .anon := .const natId #[] (info zeroAddress)
def succType : KExpr .anon :=
  .all () () natRef natRef (info succAddress)

def natConcrete : KConst .anon :=
  .indc () () 0 0 0 false natId 0 natType #[zeroId, succId] ()

def zeroConcrete : KConst .anon :=
  .ctor () () false 0 natId 0 0 0 natRef

def succConcrete : KConst .anon :=
  .ctor () () false 0 natId 1 0 1 succType

def goodConcrete : KConst .anon :=
  .axio () () false 0 natRef

/-- Deliberately untrusted recursor-shaped catalog entry used by the K1e
adversarial execution fixture.  Its rule is operationally consumable, but it
has no `nameOf` entry and is never added to the trusted log. -/
def iotaResult : KExpr .anon := .const zeroId #[] (info iotaAddress)

def iotaRule : RecRule .anon :=
  { ctor := (), fields := 0, rhs := iotaResult }

def iotaConcrete : KConst .anon :=
  .recr () () false false 0 0 0 0 0 natId 0 natRef #[iotaRule] ()

def catalog : Catalog := fun id =>
  if id == natId then some natConcrete
  else if id == zeroId then some zeroConcrete
  else if id == succId then some succConcrete
  else if id == goodId then some goodConcrete
  else if id == IllTypedPending.targetId then some IllTypedPending.concrete
  else if id == iotaId then some iotaConcrete
  else none

def nameOf : Address → Option Lean.Name := fun addr =>
  if addr == natAddress then some natName
  else if addr == zeroAddress then some zeroName
  else if addr == succAddress then some succName
  else if addr == goodAddress then some goodName
  else if addr == IllTypedPending.fixtureAddress then
    some IllTypedPending.targetName
  else none

theorem address_ne {a b : UInt8} (h : a ≠ b) : address a ≠ address b := by
  intro hab
  have hbyte := congrArg (fun x : Address => x.hash.get! 0) hab
  simp [address] at hbyte
  exact h hbyte

theorem zeroAddress_ne_natAddress : zeroAddress ≠ natAddress := by
  exact address_ne (by decide)

theorem succAddress_ne_natAddress : succAddress ≠ natAddress := by
  exact address_ne (by decide)

theorem succAddress_ne_zeroAddress : succAddress ≠ zeroAddress := by
  exact address_ne (by decide)

theorem goodAddress_ne_natAddress : goodAddress ≠ natAddress := by
  exact address_ne (by decide)

theorem goodAddress_ne_zeroAddress : goodAddress ≠ zeroAddress := by
  exact address_ne (by decide)

theorem goodAddress_ne_succAddress : goodAddress ≠ succAddress := by
  exact address_ne (by decide)

theorem badAddress_ne_natAddress :
    IllTypedPending.fixtureAddress ≠ natAddress := by
  exact address_ne (by decide)

theorem badAddress_ne_zeroAddress :
    IllTypedPending.fixtureAddress ≠ zeroAddress := by
  exact address_ne (by decide)

theorem badAddress_ne_succAddress :
    IllTypedPending.fixtureAddress ≠ succAddress := by
  exact address_ne (by decide)

theorem badAddress_ne_goodAddress :
    IllTypedPending.fixtureAddress ≠ goodAddress := by
  exact address_ne (by decide)

theorem natId_ne_zeroId : natId ≠ zeroId := by
  intro h
  exact address_ne (a := 10) (b := 11) (by decide)
    (congrArg KId.addr h)

theorem natId_ne_succId : natId ≠ succId := by
  intro h
  exact address_ne (a := 10) (b := 12) (by decide)
    (congrArg KId.addr h)

theorem zeroId_ne_succId : zeroId ≠ succId := by
  intro h
  exact address_ne (a := 11) (b := 12) (by decide)
    (congrArg KId.addr h)

theorem goodId_ne_natId : goodId ≠ natId := by
  intro h
  exact address_ne (a := 13) (b := 10) (by decide)
    (congrArg KId.addr h)

theorem goodId_ne_zeroId : goodId ≠ zeroId := by
  intro h
  exact address_ne (a := 13) (b := 11) (by decide)
    (congrArg KId.addr h)

theorem goodId_ne_succId : goodId ≠ succId := by
  intro h
  exact address_ne (a := 13) (b := 12) (by decide)
    (congrArg KId.addr h)

theorem badId_ne_natId : IllTypedPending.targetId ≠ natId := by
  intro h
  exact address_ne (a := 0) (b := 10) (by decide)
    (congrArg KId.addr h)

theorem badId_ne_zeroId : IllTypedPending.targetId ≠ zeroId := by
  intro h
  exact address_ne (a := 0) (b := 11) (by decide)
    (congrArg KId.addr h)

theorem badId_ne_succId : IllTypedPending.targetId ≠ succId := by
  intro h
  exact address_ne (a := 0) (b := 12) (by decide)
    (congrArg KId.addr h)

theorem badId_ne_goodId : IllTypedPending.targetId ≠ goodId := by
  intro h
  exact address_ne (a := 0) (b := 13) (by decide)
    (congrArg KId.addr h)

@[simp] theorem catalog_nat : catalog natId = some natConcrete := by
  rfl

@[simp] theorem catalog_zero : catalog zeroId = some zeroConcrete := by
  rfl

@[simp] theorem catalog_succ : catalog succId = some succConcrete := by
  rfl

@[simp] theorem catalog_good : catalog goodId = some goodConcrete := by
  rfl

@[simp] theorem catalog_bad :
    catalog IllTypedPending.targetId = some IllTypedPending.concrete := by
  rfl

@[simp] theorem catalog_iota : catalog iotaId = some iotaConcrete := by
  rfl

@[simp] theorem nameOf_nat : nameOf natAddress = some natName := by
  rfl

@[simp] theorem nameOf_zero : nameOf zeroAddress = some zeroName := by
  rfl

@[simp] theorem nameOf_succ : nameOf succAddress = some succName := by
  rfl

@[simp] theorem nameOf_good : nameOf goodAddress = some goodName := by
  rfl

@[simp] theorem nameOf_bad :
    nameOf IllTypedPending.fixtureAddress = some IllTypedPending.targetName := by
  rfl

def natConstant : VConstant where
  uvars := 0
  type := .sort (.succ .zero)

def zeroConstant : VConstant where
  uvars := 0
  type := .const natName []

def succConstant : VConstant where
  uvars := 0
  type := .forallE (.const natName []) (.const natName [])

def natVal : VConstVal := { natConstant with name := natName }
def zeroVal : VConstVal := { zeroConstant with name := zeroName }
def succVal : VConstVal := { succConstant with name := succName }

def natEnv₁ : VEnv where
  constants := fun name =>
    if natName = name then some natConstant else none
  defeqs := fun _ => False

def natEnv₂ : VEnv where
  constants := fun name =>
    if zeroName = name then some zeroConstant else natEnv₁.constants name
  defeqs := fun _ => False

def natEnv : VEnv where
  constants := fun name =>
    if succName = name then some succConstant else natEnv₂.constants name
  defeqs := fun _ => False

theorem addNat :
    VEnv.empty.addConst natName natConstant = some natEnv₁ := by
  rfl

theorem addZero :
    natEnv₁.addConst zeroName zeroConstant = some natEnv₂ := by
  rfl

theorem addSucc :
    natEnv₂.addConst succName succConstant = some natEnv := by
  rfl

@[simp] theorem natEnv_nat : natEnv.constants natName = some natConstant := by
  simp [natEnv, natEnv₂, natEnv₁, natName, zeroName, succName]

@[simp] theorem natEnv_zero : natEnv.constants zeroName = some zeroConstant := by
  simp [natEnv, natEnv₂, natEnv₁, natName, zeroName, succName]

@[simp] theorem natEnv_succ : natEnv.constants succName = some succConstant := by
  simp [natEnv, natEnv₂, natEnv₁, natName, zeroName, succName]

theorem natConstant_wf : natConstant.WF VEnv.empty := by
  exact ⟨_, VEnv.HasType.sort trivial⟩

theorem zeroConstant_wf : zeroConstant.WF natEnv₁ := by
  refine ⟨.succ .zero, ?_⟩
  exact VEnv.HasType.const (VEnv.addConst_self addNat) (by simp) rfl

theorem succConstant_wf : succConstant.WF natEnv₂ := by
  apply VEnv.IsType.forallE
  · refine ⟨.succ .zero, ?_⟩
    exact VEnv.HasType.const
      ((VEnv.addConst_le addZero).constants (VEnv.addConst_self addNat))
      (by simp) rfl
  · refine ⟨.succ .zero, ?_⟩
    exact VEnv.HasType.const
      ((VEnv.addConst_le addZero).constants (VEnv.addConst_self addNat))
      (by simp) rfl

theorem natEnv_wf : natEnv.WF := by
  refine ⟨[.axiom succVal, .axiom zeroVal, .axiom natVal], ?_⟩
  exact .decl (.axiom succConstant_wf addSucc)
    (.decl (.axiom zeroConstant_wf addZero)
      (.decl (.axiom natConstant_wf addNat) .empty))

theorem natEnv_ordered : natEnv.Ordered :=
  .const
    (.const
      (.const .empty natConstant_wf addNat)
      zeroConstant_wf addZero)
    succConstant_wf addSucc

theorem empty_le_natEnv : VEnv.empty ≤ natEnv :=
  (VEnv.addConst_le addNat).trans
    ((VEnv.addConst_le addZero).trans (VEnv.addConst_le addSucc))

theorem natConstant_wf_final : natConstant.WF natEnv :=
  natConstant_wf.mono empty_le_natEnv

theorem zeroConstant_wf_final : zeroConstant.WF natEnv :=
  zeroConstant_wf.mono
    ((VEnv.addConst_le addZero).trans (VEnv.addConst_le addSucc))

theorem succConstant_wf_final : succConstant.WF natEnv :=
  succConstant_wf.mono (VEnv.addConst_le addSucc)

/-! ## Ambient-block translation -/

def members (id : KId .anon) : Prop :=
  id = natId ∨ id = zeroId ∨ id = succId

theorem natRaw : RawInductiveConstRel natEnv nameOf RawProjRel.none
    natId natConcrete natName natConstant := by
  refine ⟨?_, nameOf_nat, rfl, ?_⟩
  · trivial
  · exact RawExprRel.sort

theorem zeroRaw : RawInductiveConstRel natEnv nameOf RawProjRel.none
    zeroId zeroConcrete zeroName zeroConstant := by
  refine ⟨?_, nameOf_zero, rfl, ?_⟩
  · trivial
  · exact RawExprRel.const nameOf_nat natEnv_nat rfl

theorem succRaw : RawInductiveConstRel natEnv nameOf RawProjRel.none
    succId succConcrete succName succConstant := by
  refine ⟨?_, nameOf_succ, rfl, ?_⟩
  · trivial
  · apply RawExprRel.all
    · exact RawExprRel.const nameOf_nat natEnv_nat rfl
    · exact RawExprRel.const nameOf_nat natEnv_nat rfl

/-- A real model of the G2a assumption boundary.  This particular block has
no recursor declaration, so `recursorFacts` is vacuous; any later block that
contains a `.recr` entry must supply its Theory defeq witnesses explicitly. -/
def oracle : InductiveOracle RawProjRel.none catalog nameOf
    (fun _ => False) VEnv.empty where
  members := members
  nonempty := ⟨natId, Or.inl rfl⟩
  fresh := by
    intro id _ h
    exact h
  after := natEnv
  envLE := empty_le_natEnv
  blockWF := natEnv_wf
  translateBlock := by
    intro id hmember
    rcases hmember with rfl | rfl | rfl
    · exact ⟨natConcrete, natName, natConstant, catalog_nat, natRaw,
        natEnv_nat, natConstant_wf_final⟩
    · exact ⟨zeroConcrete, zeroName, zeroConstant, catalog_zero, zeroRaw,
        natEnv_zero, zeroConstant_wf_final⟩
    · exact ⟨succConcrete, succName, succConstant, catalog_succ, succRaw,
        natEnv_succ, succConstant_wf_final⟩
  recursorFacts := by
    intro id c rule hmember hcatalog hrule
    rcases hmember with rfl | rfl | rfl
    · rw [catalog_nat] at hcatalog
      cases hcatalog
      exact False.elim hrule
    · rw [catalog_zero] at hcatalog
      cases hcatalog
      exact False.elim hrule
    · rw [catalog_succ] at hcatalog
      cases hcatalog
      exact False.elim hrule

def worldNat : VerifyWorld where
  catalog := catalog
  trusted := oracle.TrustBlock
  venv := natEnv
  nameOf := nameOf
  venvWF := natEnv_wf
  trustedCatalogued := by
    intro id htrusted
    rcases htrusted with hmember | hold
    · exact oracle.catalogued hmember
    · exact False.elim hold

theorem trustedCatalogRelNat :
    TrustedCatalogRel RawProjRel.none worldNat :=
  TrustedCatalogLog.ambient oracle TrustedCatalogLog.empty

theorem nat_trusted : worldNat.trusted natId :=
  oracle.trust_member (Or.inl rfl)

theorem zero_trusted : worldNat.trusted zeroId :=
  oracle.trust_member (Or.inr (Or.inl rfl))

theorem succ_trusted : worldNat.trusted succId :=
  oracle.trust_member (Or.inr (Or.inr rfl))

/-- The ambient trusted-log path exposes the same exact operational lookup
contract as an ordinary promoted declaration. -/
theorem nat_trusted_lookup :
    ∃ c name ci,
      worldNat.catalog natId = some c ∧
      worldNat.nameOf natId.addr = some name ∧
      worldNat.venv.constants name = some ci :=
  trustedCatalogRelNat.lookup nat_trusted

/-! ## A valid standalone declaration over ambient Nat -/

def goodConstant : VConstVal where
  name := goodName
  uvars := 0
  type := .const natName []

def goodDecl : VDecl := .axiom goodConstant

theorem goodRaw : RawDeclRel worldNat.venv worldNat.nameOf
    RawProjRel.none goodId goodConcrete goodDecl := by
  apply RawDeclRel.axiom nameOf_good
  exact RawExprRel.const nameOf_nat natEnv_nat rfl

theorem good_not_trusted : ¬worldNat.trusted goodId := by
  rintro (hmember | hold)
  · rcases hmember with h | h | h
    · exact goodId_ne_natId h
    · exact goodId_ne_zeroId h
    · exact goodId_ne_succId h
  · exact hold

theorem good_closed : CatalogClosed catalog goodConcrete := by
  intro id href
  change natId = id at href
  subst id
  exact ⟨natConcrete, catalog_nat⟩

theorem natEnv_good_absent : natEnv.constants goodName = none := by
  rfl

theorem good_fresh : TargetFresh worldNat goodId := by
  intro name hname
  change nameOf goodAddress = some name at hname
  change natEnv.constants name = none
  rw [nameOf_good] at hname
  cases hname
  exact natEnv_good_absent

theorem goodPending :
    PendingDecl RawProjRel.none worldNat goodId goodDecl :=
  ⟨goodConcrete, catalog_good, goodRaw, good_not_trusted,
    good_closed, good_fresh⟩

def goodEnv : VEnv where
  constants := fun name =>
    if goodName = name then some goodConstant.toVConstant
    else natEnv.constants name
  defeqs := natEnv.defeqs

theorem addGood :
    natEnv.addConst goodName goodConstant.toVConstant = some goodEnv := by
  rfl

theorem goodConstant_wf : goodConstant.toVConstant.WF natEnv := by
  refine ⟨.succ .zero, ?_⟩
  exact VEnv.HasType.const natEnv_nat (by simp) rfl

theorem goodDecl_wf : VDecl.WF natEnv goodDecl goodEnv :=
  .axiom goodConstant_wf addGood

theorem goodEnv_ordered : goodEnv.Ordered :=
  .const natEnv_ordered goodConstant_wf addGood

def worldGood : VerifyWorld where
  catalog := catalog
  trusted := TrustInsert worldNat.trusted goodId
  venv := goodEnv
  nameOf := nameOf
  venvWF := by
    obtain ⟨ds, hds⟩ := natEnv_wf
    exact ⟨goodDecl :: ds, .decl goodDecl_wf hds⟩
  trustedCatalogued := by
    intro id htrusted
    rcases htrusted with hnew | hold
    · subst id
      exact ⟨goodConcrete, catalog_good⟩
    · exact worldNat.trustedCatalogued hold

theorem nat_le_good : worldNat ≤ worldGood := by
  exact ⟨rfl, rfl, TrustInsert.old, VEnv.addConst_le addGood⟩

theorem trustedCatalogRelGood :
    TrustedCatalogRel RawProjRel.none worldGood :=
  TrustedCatalogLog.promote trustedCatalogRelNat catalog_good goodRaw
    good_closed good_not_trusted goodDecl_wf

theorem good_trusted : worldGood.trusted goodId :=
  TrustInsert.self

theorem goodTrustedDecl :
    TrustedDecl RawProjRel.none worldGood goodId goodDecl := by
  exact ⟨goodConcrete, natEnv, goodEnv, catalog_good,
    goodRaw.mono (VEnv.addConst_le addGood), good_trusted,
    goodDecl_wf, VEnv.LE.rfl⟩

theorem nat_trusted_good : worldGood.trusted natId :=
  TrustInsert.old nat_trusted

theorem nat_lookup_good :
    ∃ c name ci,
      worldGood.catalog natId = some c ∧
      worldGood.nameOf natId.addr = some name ∧
      worldGood.venv.constants name = some ci :=
  trustedCatalogRelGood.lookup nat_trusted_good

/-! ## Ill-typed pending declaration in the Nat world -/

theorem badRaw : RawDeclRel worldGood.venv worldGood.nameOf
    RawProjRel.none IllTypedPending.targetId IllTypedPending.concrete
    IllTypedPending.theoryDecl := by
  apply RawDeclRel.axiom nameOf_bad
  exact RawExprRel.sort

theorem bad_not_trusted : ¬worldGood.trusted IllTypedPending.targetId := by
  rintro (hgood | hold)
  · exact badId_ne_goodId hgood
  · rcases hold with hmember | hfalse
    · rcases hmember with hnat | hzero | hsucc
      · exact badId_ne_natId hnat
      · exact badId_ne_zeroId hzero
      · exact badId_ne_succId hsucc
    · exact hfalse

theorem bad_closed :
    CatalogClosed catalog IllTypedPending.concrete := by
  intro id href
  change False at href
  exact False.elim href

theorem goodEnv_bad_absent :
    goodEnv.constants IllTypedPending.targetName = none := by
  rfl

theorem bad_fresh : TargetFresh worldGood IllTypedPending.targetId := by
  intro name hname
  change nameOf IllTypedPending.fixtureAddress = some name at hname
  change goodEnv.constants name = none
  rw [nameOf_bad] at hname
  cases hname
  exact goodEnv_bad_absent

theorem badPending : PendingDecl RawProjRel.none worldGood
    IllTypedPending.targetId IllTypedPending.theoryDecl :=
  ⟨IllTypedPending.concrete, catalog_bad, badRaw, bad_not_trusted,
    bad_closed, bad_fresh⟩

/-- The bad universe parameter remains impossible in the larger Nat world;
ambient constants cannot repair a malformed declared universe arity. -/
theorem badConstant_not_wf :
    ¬IllTypedPending.theoryConstant.toVConstant.WF goodEnv := by
  intro hwf
  have hlevel : (VLevel.param 0).WF 0 :=
    hwf.sort_inv goodEnv_ordered
  exact (Nat.not_lt_zero 0) hlevel

theorem badDecl_not_wf :
    ¬∃ env', VDecl.WF worldGood.venv IllTypedPending.theoryDecl env' := by
  rintro ⟨env', hwf⟩
  cases hwf with
  | «axiom» hconstant _ => exact badConstant_not_wf hconstant

/-! ## Concrete loaded-state witness -/

def loadedEnv : KEnv .anon :=
  ((((({} : KEnv .anon).insert natId natConcrete)
    |>.insert zeroId zeroConcrete)
    |>.insert succId succConcrete)
    |>.insert goodId goodConcrete)
    |>.insert IllTypedPending.targetId IllTypedPending.concrete

theorem loadedAgrees : LoadedAgrees catalog loadedEnv := by
  exact LoadedAgrees.insert
    (LoadedAgrees.insert
      (LoadedAgrees.insert
        (LoadedAgrees.insert
          (LoadedAgrees.insert (LoadedAgrees.empty catalog) catalog_nat)
          catalog_zero)
        catalog_succ)
      catalog_good)
    catalog_bad

@[simp] theorem loadedEnv_nat : loadedEnv.get? natId = some natConcrete := by
  simp only [loadedEnv, KEnv.get?, KEnv.insert,
    Std.HashMap.getElem?_insert]
  split
  · next h => exact False.elim (badId_ne_natId (eq_of_beq h))
  split
  · next h => exact False.elim (goodId_ne_natId (eq_of_beq h))
  split
  · next h => exact False.elim (natId_ne_succId (eq_of_beq h).symm)
  split
  · next h => exact False.elim (natId_ne_zeroId (eq_of_beq h).symm)
  · rfl

def state (prims : Primitives .anon) : TcState .anon :=
  { env := loadedEnv, prims, ctxId := natAddress }

theorem stateWF (prims : Primitives .anon) :
    TcStateWF RawProjRel.none (state prims) worldGood :=
  ⟨trustedCatalogRelGood, loadedAgrees, InternTable.WF.empty⟩

/-- The G2b consumer lookup is inhabited by an ambient inductive member in a
real concrete state; no legacy whole-environment translation is involved. -/
theorem natResolved (prims : Primitives .anon) :
    ∃ name ci,
      TrustedConstRel RawProjRel.none worldGood natId natConcrete name ci :=
  (stateWF prims).resolve loadedEnv_nat nat_trusted_good

/-- Resolution supplies the exact `TrKExprS.const` premise package used by
later reduction and inference proofs. -/
theorem natReferenceTranslates (prims : Primitives .anon) :
    ∃ name ci,
      TrustedConstRel RawProjRel.none worldGood natId natConcrete name ci ∧
      TrKExprS worldGood.venv ci.uvars worldGood.nameOf RawProjRel.none []
        natRef (.const name []) := by
  obtain ⟨name, ci, hresolved⟩ := natResolved prims
  refine ⟨name, ci, hresolved, ?_⟩
  simpa [natRef] using hresolved.trKExprS_const
    (ctx := []) (us := #[]) (info := info zeroAddress)
    (by simp) (by rfl)

/-- Concrete loading alone still cannot resolve the pending declaration
through the trusted consumer interface. -/
theorem bad_not_resolved :
    ¬∃ name ci, TrustedConstRel RawProjRel.none worldGood
      IllTypedPending.targetId IllTypedPending.concrete name ci := by
  rintro ⟨_, _, hresolved⟩
  exact bad_not_trusted hresolved.trusted

/-- The existential-world form used by C1--C3 consumers is non-vacuous on the
same ambient Nat state. -/
theorem natResolvedInv (prims : Primitives .anon) :
    ∃ world, worldGood ≤ world ∧
      ∃ name ci,
        TrustedConstRel RawProjRel.none world natId natConcrete name ci :=
  (stateWF prims).tcInv.resolve loadedEnv_nat nat_trusted_good

/-! ## G3 finite run-support and execution witness -/

/-- A constructed constant reference to the ambient Nat family.  Recording
the smart constructor's own info makes it both a concrete Nat reference and a
`KExpr.Constructed` witness for the resource-bound interface. -/
def supportExpr : KExpr .anon :=
  .const natId #[] (KExpr.mkConst natId #[] ()).info

theorem supportExpr_eq_mkConst :
    supportExpr = KExpr.mkConst natId #[] () :=
  (KExpr.mkConst_shape natId #[] ()).symm

theorem supportExpr_constructed : KExpr.Constructed supportExpr := by
  rw [supportExpr_eq_mkConst]
  exact .const

@[simp] theorem supportExpr_size : supportExpr.size = 1 := rfl

@[simp] theorem supportExpr_lbr : supportExpr.lbr = 0 := by
  rw [supportExpr_eq_mkConst]
  exact KExpr.mkConst_lbr natId #[] ()

/-- The run-scope model exercises direct interning and every walker family
currently covered by the proof library. -/
def supportRequests : List WalkerRequest := [
  .internExpr supportExpr,
  .internUniv zeroLevel,
  .lift supportExpr 0 0,
  .subst supportExpr supportExpr 0,
  .simulSubst supportExpr #[] 0,
  .instRev supportExpr #[],
  .abstractFVars supportExpr #[],
  .instUniv supportExpr #[]
]

def support : RunSupport := RunSupport.pair supportExpr zeroLevel

private theorem support_lift {x : KExpr .anon}
    (h : KExpr.LiftReach 0 supportExpr 0 x) : support x := by
  change x = supportExpr
  simpa [supportExpr, KExpr.LiftReach, KExpr.liftSpec] using h

private theorem support_subst {x : KExpr .anon}
    (h : KExpr.SubstReach supportExpr supportExpr 0 x) : support x := by
  change x = supportExpr
  simpa [supportExpr, KExpr.SubstReach, KExpr.substSpec] using h

private theorem support_simulSubst {x : KExpr .anon}
    (h : KExpr.SimulSubstReach #[] supportExpr 0 x) : support x := by
  change x = supportExpr
  simpa [supportExpr, KExpr.SimulSubstReach,
    KExpr.simulSubstSpec] using h

private theorem support_instRev {x : KExpr .anon}
    (h : KExpr.InstRevReach #[] supportExpr 0 x) : support x := by
  change x = supportExpr
  simpa [supportExpr, KExpr.InstRevReach,
    KExpr.instantiateRevSpec] using h

private theorem support_abstractFVars {x : KExpr .anon}
    (h : KExpr.AbstractReach (abstractFVarPositions #[]) 0
      supportExpr 0 x) : support x := by
  change x = supportExpr
  simpa [supportExpr, abstractFVarPositions, KExpr.AbstractReach,
    KExpr.abstractFVarsSpec] using h

private theorem supportExpr_instUniv :
    KExpr.instUnivSpec supportExpr #[] = .ok supportExpr := by
  unfold supportExpr
  rw [KExpr.instUnivSpec]
  simp only [Array.mapM_empty]
  change Except.ok (KExpr.mkConst natId #[] ()) =
    Except.ok (.const natId #[] (KExpr.mkConst natId #[] ()).info)
  exact congrArg Except.ok (KExpr.mkConst_shape natId #[] ())

private theorem support_instUniv {x : KExpr .anon}
    (h : KExpr.InstUnivReach #[] supportExpr x) : support x := by
  change x = supportExpr
  change x = supportExpr ∨
    KExpr.instUnivSpec supportExpr #[] = .ok x ∨ False at h
  rcases h with h | h | h
  · exact h
  · rw [supportExpr_instUniv] at h
    cases h
    rfl
  · exact False.elim h

/-- The paired support covers both empty initial intern ranges and all eight
recorded operation footprints. -/
theorem checkSupport (prims : Primitives .anon) :
    CheckConstSupport (state prims).env.intern supportRequests support := by
  constructor
  · constructor
    · intro x hx
      obtain ⟨a, ha⟩ := hx
      simp [state, loadedEnv, KEnv.insert] at ha
    · intro u hu
      obtain ⟨a, ha⟩ := hu
      simp [state, loadedEnv, KEnv.insert] at ha
  · intro request hmem
    simp [supportRequests] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · constructor
      · exact fun _ hx => hx
      · exact fun _ hu => False.elim hu
    · constructor
      · exact fun _ hx => False.elim hx
      · exact fun _ hu => hu
    · constructor
      · exact fun _ hx => support_lift hx
      · exact fun _ hu => False.elim hu
    · constructor
      · exact fun _ hx => support_subst hx
      · exact fun _ hu => False.elim hu
    · constructor
      · exact fun _ hx => support_simulSubst hx
      · exact fun _ hu => False.elim hu
    · constructor
      · exact fun _ hx => support_instRev hx
      · exact fun _ hu => False.elim hu
    · constructor
      · exact fun _ hx => support_abstractFVars hx
      · exact fun _ hu => False.elim hu
    · constructor
      · exact fun _ hx => support_instUniv hx
      · exact fun _ hu => False.elim hu

/-- Source traversal and generated-result arithmetic are simultaneously
bounded for the concrete G3b request list. -/
theorem resourceBounds : ResourceBounds supportRequests := by
  constructor
  intro request hmem
  simp [supportRequests] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact supportExpr_constructed
  · trivial
  · refine ⟨supportExpr_constructed, ?_, ?_⟩
    · simp [UInt64.size]
    · simp [UInt64.size]
  · refine ⟨supportExpr_constructed, supportExpr_constructed, ?_, ?_, ?_⟩
    · simp [UInt64.size]
    · simp [UInt64.size]
    · simp [UInt64.size]
  · refine ⟨supportExpr_constructed, ?_, ?_, ?_, ?_⟩
    · intro k hk
      simp at hk
    · intro k hk
      simp at hk
    · simp [UInt64.size]
    · intro k hk
      simp at hk
  · refine ⟨supportExpr_constructed, ?_, ?_⟩
    · intro k hk
      simp at hk
    · simp [UInt64.size]
  · refine ⟨supportExpr_constructed, ?_, ?_, ?_⟩
    · intro id p hp
      simp [abstractFVarPositions] at hp
    · simp [UInt64.size]
    · simp [UInt64.size]
  · trivial

/-- A small real `TcM` computation containing exactly the eight recorded
interning operations.  It is a proof fixture, not a claim about `checkConst`;
later K1--K3 proofs build the same certificate compositionally for the
production entry points. -/
def supportProgram : TcM .anon Unit := do
  let _ ← TcM.intern supportExpr
  let _ ← TcM.internUniv zeroLevel
  let _ ← TcM.runIntern (lift supportExpr 0 0)
  let _ ← TcM.runIntern (subst supportExpr supportExpr 0)
  let _ ← TcM.runIntern (simulSubst supportExpr #[] 0)
  let _ ← TcM.runIntern (instantiateRev supportExpr #[])
  let _ ← TcM.runIntern (abstractFVars supportExpr #[])
  let _ ← TcM.instantiateUnivParams supportExpr #[]
  return ()

theorem supportExecution (prims : Primitives .anon) :
    ExecutionRequests supportProgram (state prims) supportRequests := by
  unfold supportProgram supportRequests
  exact .bind (.internExpr (state prims) supportExpr) fun _ s₁ _ =>
    .bind (.internUniv s₁ zeroLevel) fun _ s₂ _ =>
    .bind (.lift s₂ supportExpr 0 0) fun _ s₃ _ =>
    .bind (.subst s₃ supportExpr supportExpr 0) fun _ s₄ _ =>
    .bind (.simulSubst s₄ supportExpr #[] 0) fun _ s₅ _ =>
    .bind (.instRev s₅ supportExpr #[]) fun _ s₆ _ =>
    .bind (.abstractFVars s₆ supportExpr #[]) fun _ s₇ _ =>
    .bind (.instUniv s₇ supportExpr #[]) fun _ s₈ _ => .pure s₈ ()

theorem runAssumptions (prims : Primitives .anon) :
    RunAssumptions (state prims) supportProgram
      supportRequests support :=
  ⟨supportExecution prims,
    RunSupport.pair_collisionFree supportExpr zeroLevel,
    checkSupport prims, resourceBounds⟩

/-- G3b is non-vacuous in the same state that contains a trusted ambient Nat
family and a loaded ill-typed pending declaration.  Its execution list cannot
be replaced by `[]`: it is indexed by the concrete eight-operation program. -/
theorem supportAcceptance (prims : Primitives .anon) :
    TcStateWF RawProjRel.none (state prims) worldGood ∧
    worldGood.trusted natId ∧
    PendingDecl RawProjRel.none worldGood IllTypedPending.targetId
      IllTypedPending.theoryDecl ∧
    RunAssumptions (state prims) supportProgram
      supportRequests support :=
  ⟨stateWF prims, nat_trusted_good, badPending,
    runAssumptions prims⟩

/-! ## K1 exact nonempty warm-cache witness -/

/-- This fixture contains only closed source expressions, so its context-key
model relates the distinguished empty key to the empty semantic context. -/
def whnfContextKeys : WhnfContextKeys :=
  WhnfContextKeys.closed 0

/-- Exact K1 semantics for all five WHNF cache families.  Non-WHNF semantic
caches are absent from the fixture; cached block errors remain replayable. -/
def whnfSemantics : CacheSemantics :=
  whnfCacheSemantics whnfContextKeys RawProjRel.none
    CacheSemantics.blockErrorsOnly

/-- The closed Nat reference is definitionally equal to itself in the real
ambient-Nat Theory world.  This is the semantic fact stored by the warm
cache, replacing G4's former address-only identity contract. -/
theorem supportExpr_whnfMeaning :
    WhnfMeaning RawProjRel.none worldNat 0 [] supportExpr supportExpr := by
  obtain ⟨name, ci, hresolved⟩ :=
    trustedCatalogRelNat.resolve nat_trusted catalog_nat
  have huvars : ci.uvars = 0 := by
    simpa [natConcrete] using hresolved.uvars.symm
  have htr0 := hresolved.trKExprS_const
    (ctx := []) (us := #[]) (info := supportExpr.info)
    (by simp) (by rfl)
  have htr :
      TrKExprS worldNat.venv 0 worldNat.nameOf RawProjRel.none []
        supportExpr (.const name []) := by
    simpa [supportExpr, huvars] using htr0
  have hwf0 :
      VExpr.WF worldNat.venv ci.uvars [] (.const name []) := by
    refine ⟨_, VEnv.HasType.const hresolved.lookup (by simp) ?_⟩
    simp [huvars]
  have hwf : VExpr.WF worldNat.venv 0 [] (.const name []) := by
    simpa [huvars] using hwf0
  exact WhnfMeaning.refl htr hwf

def warmKey : Address × Address :=
  (supportExpr.addr, emptyCtxAddr)

def warmEntry : CacheEntry :=
  .expr .whnf warmKey supportExpr

def warmEnv : KEnv .anon :=
  { loadedEnv with
    whnfCache := loadedEnv.whnfCache.insert warmKey supportExpr }

def warmState (prims : Primitives .anon) : TcState .anon :=
  { env := warmEnv, prims, ctxId := natAddress }

/-- The loaded ambient-Nat environment has constants but no semantic cache
entries. This is the fresh side of the G4 fresh/warm comparison. -/
theorem loadedEnv_noCacheEntries (entry : CacheEntry) :
    ¬loadedEnv.HasCacheEntry entry := by
  intro hentry
  cases hentry <;> simp [loadedEnv, KEnv.insert] at *

private theorem supportExpr_references {id : KId .anon}
    (h : supportExpr.References id) : id = natId := by
  change natId = id at h
  exact h.symm

/-- The nonempty entry has finite support, depends only on trusted ambient
Nat, and satisfies the fixture's semantic identity contract. -/
theorem warmProvenanceNat :
    CacheProvenance whnfSemantics
      (CacheAuthority.stable worldNat) support warmEntry := by
  refine ⟨?_, ?_, ?_⟩
  · change support.HasExprAddr supportExpr.addr ∧ support supportExpr
    constructor
    · exact ⟨supportExpr, rfl, rfl⟩
    · rfl
  · intro id href
    left
    change CacheEntry.SourceReferences support supportExpr.addr id ∨
      supportExpr.References id at href
    rcases href with href | href
    · obtain ⟨e, he, _, heref⟩ := href
      change e = supportExpr at he
      subst e
      have hid := supportExpr_references heref
      subst id
      exact nat_trusted
    · have hid := supportExpr_references href
      subst id
      exact nat_trusted
  · intro source hsource haddr Δ hctx
    change source = supportExpr at hsource
    subst source
    have hΔ : Δ = [] := by
      simpa [whnfContextKeys, warmKey] using hctx.2
    subst Δ
    exact supportExpr_whnfMeaning

theorem loadedCacheInvariantNat :
    CacheInvariant whnfSemantics
      (CacheAuthority.stable worldNat) support loadedEnv :=
  CacheInvariant.of_no_entries loadedEnv_noCacheEntries

/-- The reusable insertion rule constructs a genuinely nonempty invariant. -/
theorem warmCacheInvariantNat :
    CacheInvariant whnfSemantics
      (CacheAuthority.stable worldNat) support warmEnv := by
  exact CacheInvariant.insertWhnf loadedCacheInvariantNat warmProvenanceNat

/-- A warm entry admitted under the Nat world remains valid after the good
declaration is promoted. No cache flush or trust epoch is needed for this
monotone extension. -/
theorem warmCache_worldTransport :
    CacheInvariant whnfSemantics
      (CacheAuthority.stable worldGood) support warmEnv :=
  warmCacheInvariantNat.mono (CacheAuthority.stable_mono nat_le_good)

theorem warmEnv_hit : warmEnv.HasCacheEntry warmEntry := by
  apply KEnv.HasCacheEntry.whnf
  simp [warmEnv, warmKey]

theorem freshKernelStateWF (prims : Primitives .anon) :
    KernelStateWF whnfSemantics RawProjRel.none worldGood support
      (state prims) := by
  apply KernelStateWF.of_no_cache_entries (stateWF prims)
  · exact (checkSupport prims).initial
  · intro entry
    simpa [state] using loadedEnv_noCacheEntries entry

/-! ### First no-acceleration WHNF execution slice -/

def noAccelState (prims : Primitives .anon) : TcState .anon :=
  { state prims with noAccel := true }

def whnfLeafExpr : KExpr .anon :=
  .sort zeroLevel (info zeroAddress)

theorem whnfLeafTranslates :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
      whnfLeafExpr (.sort .zero) := by
  unfold whnfLeafExpr zeroLevel
  exact .sort (by trivial)

theorem whnfLeafTheoryWF :
    VExpr.WF worldGood.venv 0 [] (.sort .zero) :=
  ⟨_, VEnv.HasType.sort trivial⟩

/-- The concrete ambient-Nat state inhabits the full K1 invariant with
acceleration disabled. -/
theorem noAccelStateInv (prims : Primitives .anon) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood support
      0 [] (noAccelState prims) := by
  refine ⟨?_, ?_, rfl⟩
  · have h := freshKernelStateWF prims
    refine ⟨?_, ?_, ?_⟩
    · exact h.core.of_env_eq rfl
    · simpa [noAccelState] using h.internSupport
    · simpa [noAccelState] using h.caches
  · apply CtxRecon.empty <;> rfl

/-- A real Nat-containing state instantiates the first conditional
`RecM.whnf` theorem.  This branch returns before any cache, fuel, native, or
recursive-method operation, but still preserves the complete K1 invariant on
both EStateM outcomes. -/
theorem whnfLeaf_noAccel_wf (prims : Primitives .anon) :
    RecM.WF .noAccel whnfSemantics RawProjRel.none worldGood support 0 []
      (noAccelState prims) (RecM.whnf whnfLeafExpr)
      (fun result _ => WhnfPost RawProjRel.none worldGood 0 []
        (.sort .zero) result) :=
  RecM.whnf_leaf_wf .sort whnfLeafTranslates whnfLeafTheoryWF

/-- Non-vacuity package for the first no-acceleration algorithmic slice. -/
theorem whnfLeaf_noAccel_acceptance (prims : Primitives .anon) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood support
        0 [] (noAccelState prims) ∧
      RecM.WF .noAccel whnfSemantics RawProjRel.none worldGood support 0 []
        (noAccelState prims) (RecM.whnf whnfLeafExpr)
        (fun result _ => WhnfPost RawProjRel.none worldGood 0 []
          (.sort .zero) result) :=
  ⟨noAccelStateInv prims, whnfLeaf_noAccel_wf prims⟩

theorem warmCoreWF (prims : Primitives .anon) :
    TcStateWF RawProjRel.none (warmState prims) worldGood := by
  apply (stateWF prims).of_consts_eq
  · rfl
  · exact InternTable.WF.empty

theorem warmKernelStateWF (prims : Primitives .anon) :
    KernelStateWF whnfSemantics RawProjRel.none worldGood support
      (warmState prims) := by
  refine ⟨warmCoreWF prims, ?_, warmCache_worldTransport⟩
  simpa [warmState, warmEnv, state] using (checkSupport prims).initial

/-- The real warm state computes the certified key and its empty semantic
context is represented by the fixture's closed-key model. -/
theorem warmKey_matches (prims : Primitives .anon) :
    whnfContextKeys.Matches RawProjRel.none worldGood (warmState prims) []
      supportExpr warmKey := by
  refine ⟨?_, ?_, ?_⟩
  · apply CtxRecon.empty <;> rfl
  · simp [whnfContextKeys, warmKey]
  · refine ⟨warmState prims, ?_⟩
    simp [TcM.whnfKey, TcM.ctxAddrForLbr, supportExpr_lbr, warmKey]
    rfl

theorem warmStateInvAccelerated (prims : Primitives .anon) :
    WhnfStateInv .accelerated whnfSemantics RawProjRel.none worldGood support
      0 [] (warmState prims) := by
  exact ⟨warmKernelStateWF prims, (warmKey_matches prims).1, trivial⟩

/-- The generic key-frame theorem is inhabited by the real warm Nat state.
Because `supportExpr` is closed, its representation premise follows from the
exact closed-key execution equation and the state is unchanged. -/
theorem warmKey_matches_wf (prims : Primitives .anon) :
    TcM.WF
      (WhnfStateInv .accelerated whnfSemantics RawProjRel.none worldGood
        support 0 []) (warmState prims)
      (TcM.whnfKey supportExpr)
      (fun key s' =>
        whnfContextKeys.Matches RawProjRel.none worldGood
          (warmState prims) [] supportExpr key ∧
        ContextKeyFrame (warmState prims) s') := by
  have hrep : ∀ key s',
      TcM.whnfKey supportExpr (warmState prims) = .ok key s' →
      whnfContextKeys.Represents key.2 [] := by
    intro key s' hrun
    have hexact := TcM.whnfKey_closed
      (s := warmState prims) supportExpr_lbr
    rw [hexact] at hrun
    cases hrun
    simp [whnfContextKeys]
  simpa [whnfContextKeys] using
    (TcM.whnfKey_matches_wf (layer := .accelerated)
      (semantics := whnfSemantics) (trProj := RawProjRel.none)
      (world := worldGood) (support := support) (keys := whnfContextKeys)
      (Δ := []) (source := supportExpr) (s := warmState prims) hrep)

/-- A physical warm hit exposes exact Theory reduction meaning after world
transport, not merely equality of content addresses. -/
theorem warmHit_whnfMeaning (prims : Primitives .anon) :
    WhnfMeaning RawProjRel.none worldGood 0 [] supportExpr supportExpr := by
  exact ((warmKernelStateWF prims).cacheHit warmEnv_hit).whnfMeaningOfMatches
    .whnf rfl (warmKey_matches prims)

/-- Even though the bad declaration is physically loaded, the stable warm
cache cannot cite it as a semantic dependency. -/
theorem warmCache_cannotResolvePending (prims : Primitives .anon) :
    ¬warmEntry.References support IllTypedPending.targetId :=
  (warmKernelStateWF prims).pendingCacheIsolation badPending warmEnv_hit

/-- G4's formal acceptance witness contains both the fresh and nonempty warm
states, transported provenance, and pending-declaration isolation. The
executable failed-then-valid regression lives in `Tests.Ix.Tc.CheckTests`. -/
theorem cacheAcceptance (prims : Primitives .anon) :
    KernelStateWF whnfSemantics RawProjRel.none worldGood support
        (state prims) ∧
      KernelStateWF whnfSemantics RawProjRel.none worldGood support
        (warmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 []
        supportExpr supportExpr ∧
      ¬warmEntry.References support IllTypedPending.targetId :=
  ⟨freshKernelStateWF prims, warmKernelStateWF prims,
    warmHit_whnfMeaning prims, warmCache_cannotResolvePending prims⟩

theorem zero_trusted_good : worldGood.trusted zeroId :=
  TrustInsert.old zero_trusted

theorem succ_trusted_good : worldGood.trusted succId :=
  TrustInsert.old succ_trusted

/-! ### K1 structural beta witness -/

/-- A closed, typed beta redex over the ambient Nat family.  Smart
constructors supply its actual content metadata; the proof below does not
identify source and result by address. -/
def betaBody : KExpr .anon := KExpr.mkVar 0 ()
def betaArg : KExpr .anon := KExpr.mkConst zeroId #[] ()
def betaLam : KExpr .anon := KExpr.mkLam () () supportExpr betaBody
def betaSource : KExpr .anon := KExpr.mkApp betaLam betaArg

theorem betaTy_tr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
      supportExpr (.const natName []) := by
  rw [supportExpr_eq_mkConst, KExpr.mkConst_shape]
  exact .const (ci := natConstant) nameOf_nat
    (by simpa [worldGood, goodEnv, goodName, natName] using natEnv_nat)
    (by intro l hl; simp at hl) rfl

theorem betaBody_tr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none
      [(none, .vlam (.const natName []))] betaBody (.bvar 0) := by
  rw [betaBody, KExpr.mkVar_shape]
  exact .var rfl

theorem betaArg_tr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
      betaArg (.const zeroName []) := by
  rw [betaArg, KExpr.mkConst_shape]
  exact .const (ci := zeroConstant) nameOf_zero
    (by simpa [worldGood, goodEnv, goodName, zeroName] using natEnv_zero)
    (by intro l hl; simp at hl) rfl

theorem betaA_type :
    worldGood.venv.HasType 0 [] (.const natName [])
      (.sort (.succ .zero)) := by
  exact Lean4Lean.VEnv.HasType.const (env := worldGood.venv)
    (U := 0) (Γ := []) (ci := natConstant) (ls := [])
    (by simpa [worldGood, goodEnv, goodName, natName] using natEnv_nat)
    (by intro l hl; simp at hl) rfl

theorem betaBody_type :
    worldGood.venv.HasType 0 [(.const natName [])] (.bvar 0)
      (.const natName []) := by
  exact Lean4Lean.VEnv.HasType.bvar .zero

theorem betaArg_type :
    worldGood.venv.HasType 0 [] (.const zeroName [])
      (.const natName []) := by
  exact Lean4Lean.VEnv.HasType.const (env := worldGood.venv)
    (U := 0) (Γ := []) (ci := zeroConstant) (ls := [])
    (by simpa [worldGood, goodEnv, goodName, zeroName] using natEnv_zero)
    (by intro l hl; simp at hl) rfl

theorem betaTy_wf :
    VExpr.WF worldGood.venv 0 [] (.const natName []) :=
  ⟨_, betaA_type⟩

/-- The real flag-parametric core entry point returns the ambient Nat
constant immediately, in both full and cheap modes, while preserving the
no-acceleration state invariant. -/
theorem whnfCoreConst_noAccel_wf (prims : Primitives .anon)
    (flags : WhnfFlags) :
    RecM.WF .noAccel whnfSemantics RawProjRel.none worldGood support 0 []
      (noAccelState prims) (RecM.whnfCoreWithFlags supportExpr flags)
      (fun result _ => WhnfPost RawProjRel.none worldGood 0 []
        (.const natName []) result) :=
  RecM.whnfCoreWithFlags_leaf_wf .const betaTy_tr betaTy_wf

theorem whnfCoreConst_noAccel_acceptance (prims : Primitives .anon)
    (flags : WhnfFlags) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood support
        0 [] (noAccelState prims) ∧
      RecM.WF .noAccel whnfSemantics RawProjRel.none worldGood support 0 []
        (noAccelState prims) (RecM.whnfCoreWithFlags supportExpr flags)
        (fun result _ => WhnfPost RawProjRel.none worldGood 0 []
          (.const natName []) result) :=
  ⟨noAccelStateInv prims, whnfCoreConst_noAccel_wf prims flags⟩

/-- Nontrivial K1 semantic witness: the concrete Nat identity application
is definitionally equal to the exact output of the verified substitution
specification. -/
theorem betaIdentityMeaning :
    WhnfMeaning RawProjRel.none worldGood 0 [] betaSource
      (KExpr.substSpec betaBody betaArg 0) := by
  rw [betaSource, betaLam, KExpr.mkApp_shape, KExpr.mkLam_shape]
  apply WhnfMeaning.beta (RawProjRel.none_ok worldGood.venv 0)
    betaTy_tr betaBody_tr betaArg_tr betaA_type betaBody_type betaArg_type
  decide

/-- The concrete beta argument is smart-constructor coherent, which makes
lifting it by zero syntactically exact. -/
theorem betaArg_constructed : KExpr.Constructed betaArg := by
  unfold betaArg
  exact .const

/-- On the identity body, production's singleton simultaneous substitution
is exactly the single-substitution result used by the Theory beta theorem. -/
theorem betaSimulSpec :
    KExpr.simulSubstSpec betaBody #[betaArg] 0 =
      KExpr.substSpec betaBody betaArg 0 := by
  rw [betaBody, KExpr.mkVar_shape, KExpr.simulSubstSpec,
    KExpr.substSpec]
  exact KExpr.liftSpec_zero betaArg_constructed 0

theorem betaSimulLeaf :
    RecM.WhnfCoreLeaf (KExpr.simulSubstSpec betaBody #[betaArg] 0) := by
  rw [betaSimulSpec]
  rw [betaBody, KExpr.mkVar_shape, KExpr.substSpec]
  rw [KExpr.liftSpec_zero betaArg_constructed]
  exact .const

/-- The semantic beta witness now names the exact pure specification used by
the production multi-argument walker. -/
theorem betaSimulMeaning :
    WhnfMeaning RawProjRel.none worldGood 0 [] betaSource
      (KExpr.simulSubstSpec betaBody #[betaArg] 0) := by
  have h := betaIdentityMeaning
  unfold betaSource betaLam at h ⊢
  rw [KExpr.mkApp_shape, KExpr.mkLam_shape] at h ⊢
  exact WhnfMeaning.betaSimul h betaSimulSpec

private theorem stateM_bind {σ α β : Type} (x : StateM σ α)
    (f : α → StateM σ β) (s : σ) :
    (x >>= f) s = let (a, s') := x s; f a s' := rfl

private theorem stateM_map {σ α β : Type} (f : α → β)
    (x : StateM σ α) (s : σ) :
    (f <$> x) s = let (a, s') := x s; (f a, s') := rfl

private theorem stateM_pure {σ α : Type} (a : α) (s : σ) :
    (pure a : StateM σ α) s = (a, s) := rfl

/-- Exact evaluator for the production walker on the Nat identity body.  Its
zero-shift fast path returns the argument and leaves every intern table
unchanged. -/
theorem betaWalker_intern (it : InternTable .anon) :
    simulSubst betaBody #[betaArg] 0 it = (betaArg, it) := by
  unfold betaBody simulSubst
  rw [KExpr.mkVar_lbr]
  rw [KExpr.mkVar_shape]
  have hlbr :
      (KExpr.var 0 () (KExpr.mkVar (m := .anon) 0 ()).info).lbr = 1 := by
    rw [← KExpr.mkVar_shape]
    rfl
  unfold runWalk simulSubstCached scratchGet? scratchInsert liftInternW lift
  simp [stateM_bind, stateM_map, stateM_pure, hlbr]

theorem betaWalker_eval (prims : Primitives .anon) :
    TcM.runIntern (simulSubst betaBody #[betaArg] 0)
      (noAccelState prims) = .ok betaArg (noAccelState prims) := by
  unfold TcM.runIntern
  rw [betaWalker_intern]

theorem betaSimulResult :
    KExpr.simulSubstSpec betaBody #[betaArg] 0 = betaArg := by
  rw [betaSimulSpec, betaBody, KExpr.mkVar_shape, KExpr.substSpec]
  exact KExpr.liftSpec_zero betaArg_constructed 0

theorem betaResultMeaning :
    WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  rw [← betaSimulResult]
  exact betaSimulMeaning

/-- Small operational harness for the single recursive-head callback used by
this fixture.  It is not claimed to satisfy `Methods.WF` or to be the tied
production knot; the generic theorem above isolates the exact callback
equation that K2 must later prove for `methodsN`. -/
def betaHarnessMethods : Methods .anon where
  whnf := fun e => pure e
  whnfCore := fun e => pure e
  whnfMode := fun e _ => pure e
  whnfCoreFlags := fun e _ => pure e
  infer := fun e => pure e
  isDefEq := fun _ _ => pure false

/-- A real Nat-containing checker state executes the production bounded
WHNF-core driver through its beta branch and returns `Nat.zero`. -/
theorem betaCoreUncached_eval (prims : Primitives .anon)
    (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsUncached betaSource flags).run
      betaHarnessMethods (noAccelState prims) =
        .ok betaArg (noAccelState prims) := by
  unfold betaSource betaLam
  rw [KExpr.mkApp_shape, KExpr.mkLam_shape]
  apply RecM.whnfCoreWithFlagsUncached_betaOne
  · rfl
  · exact betaWalker_eval prims
  · simpa [betaSimulResult] using betaSimulLeaf

/-- K1c acceptance package: the concrete production execution preserves the
inhabited no-acceleration invariant, and its exact syntactic result has the
Theory beta meaning proved above. -/
theorem betaCoreUncached_acceptance (prims : Primitives .anon)
    (flags : WhnfFlags) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood support
        0 [] (noAccelState prims) ∧
      (RecM.whnfCoreWithFlagsUncached betaSource flags).run
        betaHarnessMethods (noAccelState prims) =
          .ok betaArg (noAccelState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg :=
  ⟨noAccelStateInv prims, betaCoreUncached_eval prims flags,
    betaResultMeaning⟩

/-! ### K1d legacy de-Bruijn zeta witness -/

/-- One legacy let frame whose stored Nat.zero value is inlined by the
translation context exactly as production `lookupLetVal` returns it. -/
def bvarZetaCtx : KVLCtx :=
  [(none, .vlet (.const natName []) (.const zeroName []))]

def bvarZetaState (prims : Primitives .anon) : TcState .anon :=
  { noAccelState prims with
    ctx := #[supportExpr]
    letVals := #[some betaArg]
    numLetBindings := 1 }

theorem bvarZetaCtxRecon (prims : Primitives .anon) :
    CtxRecon worldGood.venv 0 worldGood.nameOf RawProjRel.none
      (bvarZetaState prims) bvarZetaCtx := by
  refine {
    size_eq := rfl
    recon := ?_
    lwf := .empty
    incr := by simp [bvarZetaState, noAccelState, state]
    fresh := by simp [bvarZetaState, noAccelState, state]
    lets := rfl }
  have hrec :
      CtxRecon' worldGood.venv 0 worldGood.nameOf RawProjRel.none
        [(supportExpr, some betaArg)] [] bvarZetaCtx :=
    .bvar_let .nil betaTy_tr betaArg_tr betaArg_type
  simpa [bvarZetaState, noAccelState] using hrec

theorem bvarZetaStateInv (prims : Primitives .anon) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood support
      0 bvarZetaCtx (bvarZetaState prims) := by
  have hbase := noAccelStateInv prims
  exact ⟨⟨hbase.1.core.of_env_eq rfl,
      hbase.1.internSupport, hbase.1.caches⟩,
    bvarZetaCtxRecon prims, rfl⟩

theorem bvarZetaLiftSpec :
    KExpr.liftSpec betaArg 1 0 = betaArg := by
  unfold betaArg
  rw [KExpr.mkConst_shape]
  rfl

theorem bvarZetaLiftIntern (it : InternTable .anon) :
    lift betaArg 1 0 it = (betaArg, it) := by
  unfold lift betaArg
  rw [KExpr.mkConst_lbr]
  rfl

theorem bvarZetaLiftEval (prims : Primitives .anon) :
    TcM.runIntern (lift betaArg 1 0) (bvarZetaState prims) =
      .ok betaArg (bvarZetaState prims) := by
  unfold TcM.runIntern
  rw [bvarZetaLiftIntern]

theorem bvarZetaLookupEval (prims : Primitives .anon) :
    TcM.lookupLetVal 0 (bvarZetaState prims) =
      .ok (some betaArg) (bvarZetaState prims) := by
  apply TcM.lookupLetVal_eval
  · simp [bvarZetaState]
  · rfl
  · exact bvarZetaLiftEval prims

theorem bvarZetaMeaning (prims : Primitives .anon) :
    WhnfMeaning RawProjRel.none worldGood 0 bvarZetaCtx betaBody betaArg := by
  rw [← bvarZetaLiftSpec]
  unfold betaBody
  rw [KExpr.mkVar_shape]
  apply WhnfMeaning.zetaVar (bvarZetaCtxRecon prims)
    (RawProjRel.none_ok worldGood.venv 0)
  · simp [bvarZetaState]
  · simp [bvarZetaState]
    decide
  · rfl
  · rfl
  · decide

/-- The real bounded structural-WHNF driver reads the legacy let frame,
runs the production lifting walker, and returns Nat.zero. -/
theorem bvarZetaCoreUncachedEval (prims : Primitives .anon)
    (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsUncached betaBody flags).run betaHarnessMethods
      (bvarZetaState prims) = .ok betaArg (bvarZetaState prims) := by
  unfold betaBody
  rw [KExpr.mkVar_shape]
  apply RecM.whnfCoreWithFlagsUncached_varZeta
  · exact bvarZetaLookupEval prims
  · exact .const

theorem bvarZetaAcceptance (prims : Primitives .anon)
    (flags : WhnfFlags) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood support
        0 bvarZetaCtx (bvarZetaState prims) ∧
      (RecM.whnfCoreWithFlagsUncached betaBody flags).run betaHarnessMethods
        (bvarZetaState prims) = .ok betaArg (bvarZetaState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 bvarZetaCtx betaBody betaArg :=
  ⟨bvarZetaStateInv prims, bvarZetaCoreUncachedEval prims flags,
    bvarZetaMeaning prims⟩

/-! ### K1d let-bound fvar zeta witness -/

def fvarZetaId : FVarId := ⟨0⟩

def fvarZetaSource : KExpr .anon := KExpr.mkFVar fvarZetaId ()

def fvarZetaCtx : KVLCtx :=
  [(some (fvarZetaId, []),
    .vlet (.const natName []) (.const zeroName []))]

def fvarZetaState (prims : Primitives .anon) : TcState .anon :=
  let base := noAccelState prims
  { base with
    env := { base.env with nextFVarId := 1 }
    lctx := base.lctx.push fvarZetaId (.ldecl () supportExpr betaArg) }

theorem fvarZetaFind (prims : Primitives .anon) :
    (fvarZetaState prims).lctx.find? fvarZetaId =
      some (.ldecl () supportExpr betaArg) := by
  simp [fvarZetaState, noAccelState, LocalContext.find?, LocalContext.push,
    fvarZetaId]

theorem fvarZetaCtxRecon (prims : Primitives .anon) :
    CtxRecon worldGood.venv 0 worldGood.nameOf RawProjRel.none
      (fvarZetaState prims) fvarZetaCtx := by
  refine {
    size_eq := rfl
    recon := ?_
    lwf := ?_
    incr := by
      simp [fvarZetaState, noAccelState, state, LocalContext.push]
    fresh := ?_
    lets := rfl }
  · have hrec :
        CtxRecon' worldGood.venv 0 worldGood.nameOf RawProjRel.none
          [] [(fvarZetaId, .ldecl () supportExpr betaArg)] fvarZetaCtx :=
      .fvar .nil (.vlet betaTy_tr betaArg_tr betaArg_type) (by simp)
    simpa [fvarZetaState, noAccelState, LocalContext.push] using hrec
  · apply LocalContext.WF.push .empty
    simp [fvarZetaId]
  · intro p hp
    simp [fvarZetaState, noAccelState, state, LocalContext.push] at hp
    subst p
    simp [fvarZetaState, fvarZetaId]

theorem fvarZetaStateInv (prims : Primitives .anon) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood support
      0 fvarZetaCtx (fvarZetaState prims) := by
  have hbase := noAccelStateInv prims
  refine ⟨?_, fvarZetaCtxRecon prims, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hbase.1.core.of_consts_eq (by rfl) (by
      simpa [fvarZetaState] using hbase.1.core.intern)
  · simpa [fvarZetaState] using hbase.1.internSupport
  · intro entry hentry
    apply hbase.1.caches
    cases hentry <;> (constructor; assumption)

/-- The real bounded structural-WHNF driver resolves a let-valued fvar and
returns its closed Nat.zero value without changing checker state. -/
theorem fvarZetaCoreUncachedEval (prims : Primitives .anon)
    (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsUncached fvarZetaSource flags).run
      betaHarnessMethods (fvarZetaState prims) =
        .ok betaArg (fvarZetaState prims) := by
  unfold fvarZetaSource
  rw [KExpr.mkFVar_shape]
  apply RecM.whnfCoreWithFlagsUncached_fvarZeta
  · exact fvarZetaFind prims
  · exact .const

theorem fvarZetaMeaning (prims : Primitives .anon) :
    WhnfMeaning RawProjRel.none worldGood 0 fvarZetaCtx
      fvarZetaSource betaArg := by
  unfold fvarZetaSource
  rw [KExpr.mkFVar_shape]
  apply WhnfMeaning.zetaFVar (fvarZetaCtxRecon prims)
    (RawProjRel.none_ok worldGood.venv 0)
    (fvarZetaFind prims) betaArg_constructed
  · rfl
  · decide

theorem fvarZetaAcceptance (prims : Primitives .anon)
    (flags : WhnfFlags) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood support
        0 fvarZetaCtx (fvarZetaState prims) ∧
      (RecM.whnfCoreWithFlagsUncached fvarZetaSource flags).run
        betaHarnessMethods (fvarZetaState prims) =
          .ok betaArg (fvarZetaState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 fvarZetaCtx
        fvarZetaSource betaArg :=
  ⟨fvarZetaStateInv prims, fvarZetaCoreUncachedEval prims flags,
    fvarZetaMeaning prims⟩

/-! ### K1e adversarial projection witness -/

/-- A constructor application that the syntax-directed projection helper can
index even though `Nat` is not admitted as a structure projection in this
fixture's Theory relation. -/
def projectionValue : KExpr .anon :=
  KExpr.mkApp (KExpr.mkConst succId #[] ()) betaArg

def projectionSource : KExpr .anon :=
  KExpr.mkPrj natId 0 projectionValue

theorem loadedEnv_succ_k1e :
    loadedEnv.get? succId = some succConcrete := by
  simp only [loadedEnv, KEnv.get?, KEnv.insert,
    Std.HashMap.getElem?_insert]
  split
  · next h => exact False.elim (badId_ne_succId (eq_of_beq h))
  split
  · next h => exact False.elim (goodId_ne_succId (eq_of_beq h))
  · rfl

theorem loadedEnv_zero_k1e :
    loadedEnv.get? zeroId = some zeroConcrete := by
  simp only [loadedEnv, KEnv.get?, KEnv.insert,
    Std.HashMap.getElem?_insert]
  split
  · next h => exact False.elim (badId_ne_zeroId (eq_of_beq h))
  split
  · next h => exact False.elim (goodId_ne_zeroId (eq_of_beq h))
  split
  · next h => exact False.elim (zeroId_ne_succId (eq_of_beq h).symm)
  · rfl

theorem tryGetConst_succ_k1e (prims : Primitives .anon) :
    TcM.tryGetConst succId (noAccelState prims) =
      .ok (some succConcrete) (noAccelState prims) := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _
    (noAccelState prims) = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) (noAccelState prims) =
    .ok (noAccelState prims) (noAccelState prims) from rfl]
  simp only
  have henv : (noAccelState prims).env.get? succId =
      some succConcrete := by
    simpa [noAccelState, state] using loadedEnv_succ_k1e
  rw [henv]
  rfl

theorem projectionValueWhnf (prims : Primitives .anon)
    (flags : WhnfFlags) :
    (if flags.cheapProj then
        (RecM.whnfCoreFlagsRec projectionValue flags).run
          betaHarnessMethods (noAccelState prims)
      else (RecM.whnfRec projectionValue).run
          betaHarnessMethods (noAccelState prims)) =
      .ok projectionValue (noAccelState prims) := by
  cases flags.cheapProj <;>
    simp [RecM.whnfCoreFlagsRec, RecM.whnfRec, betaHarnessMethods] <;> rfl

theorem projectionReduceEval (prims : Primitives .anon) :
    (RecM.tryProjReduce natId 0 projectionValue).run betaHarnessMethods
      (noAccelState prims) =
        .ok (some betaArg) (noAccelState prims) := by
  unfold RecM.tryProjReduce projectionValue
  rw [KExpr.mkApp_shape, KExpr.mkConst_shape]
  simp only [KExpr.collectSpine]
  rw [ReaderT.run_bind, ReaderT.run_pure, pure_bind]
  simp only [KExpr.collectSpine.go]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run
      (RecM.tryReduceFinValDecidableRec natId 0
        (.const succId #[] (KExpr.mkConst succId #[] ()).info) #[betaArg])
        betaHarnessMethods) _
      (noAccelState prims) = _
  unfold EStateM.bind
  rw [RecM.tryReduceFinValDecidableRec_noAccel rfl]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_pure, pure_bind]
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst succId) _ (noAccelState prims) = _
  unfold EStateM.bind
  rw [tryGetConst_succ_k1e]
  rfl

theorem projectionStepEval (prims : Primitives .anon)
    (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep projectionSource flags).run
      betaHarnessMethods (noAccelState prims) =
        .ok (.next betaArg) (noAccelState prims) := by
  unfold projectionSource
  rw [KExpr.mkPrj_shape]
  apply RecM.whnfCoreWithFlagsStep_projection
    (projectionValueWhnf prims flags)
  exact projectionReduceEval prims

theorem projectionCoreEval (prims : Primitives .anon)
    (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsUncached projectionSource flags).run
      betaHarnessMethods (noAccelState prims) =
        .ok betaArg (noAccelState prims) := by
  apply RecM.whnfCoreWithFlagsUncached_nextLeaf
  · exact projectionStepEval prims flags
  · exact .const

/-- With `RawProjRel.none`, no projection source has a Theory translation.
The successful execution above therefore cannot be promoted to
`WhnfMeaning`; the generic K1e theorem's source-translation premise is
essential. -/
theorem projectionSource_not_translated :
    ¬∃ sourceV,
      TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
        projectionSource sourceV := by
  rintro ⟨sourceV, hsource⟩
  unfold projectionSource at hsource
  rw [KExpr.mkPrj_shape] at hsource
  cases hsource with
  | prj _ _ hproj => exact hproj

theorem projectionAdversarialWitness (prims : Primitives .anon)
    (flags : WhnfFlags) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood support
        0 [] (noAccelState prims) ∧
      (RecM.whnfCoreWithFlagsUncached projectionSource flags).run
        betaHarnessMethods (noAccelState prims) =
          .ok betaArg (noAccelState prims) ∧
      ¬∃ sourceV,
        TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
          projectionSource sourceV :=
  ⟨noAccelStateInv prims, projectionCoreEval prims flags,
    projectionSource_not_translated⟩

/-! ### K1e adversarial iota witness -/

def iotaPrims (prims : Primitives .anon) : Primitives .anon :=
  { prims with natZero := zeroId }

def iotaState (prims : Primitives .anon) : TcState .anon :=
  let base := noAccelState (iotaPrims prims)
  { base with env := base.env.insert iotaId iotaConcrete }

def iotaHead : KExpr .anon := KExpr.mkConst iotaId #[] ()
def iotaSource : KExpr .anon := KExpr.mkApp iotaHead iotaResult

theorem iotaStateInv (prims : Primitives .anon) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood support
      0 [] (iotaState prims) := by
  have hbase := noAccelStateInv (iotaPrims prims)
  refine ⟨?_, ?_, rfl⟩
  · refine ⟨?_, ?_, ?_⟩
    · have hcat : worldGood.catalog iotaId = some iotaConcrete := by
        exact catalog_iota
      simpa [iotaState] using hbase.1.core.load hcat
    · simpa [iotaState] using hbase.1.internSupport
    · intro entry hentry
      apply hbase.1.caches
      cases hentry <;> (constructor; assumption)
  · apply CtxRecon.empty <;> rfl

theorem iotaGetRec (prims : Primitives .anon) :
    TcM.tryGetConst iotaId (iotaState prims) =
      .ok (some iotaConcrete) (iotaState prims) := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _
    (iotaState prims) = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) (iotaState prims) =
    .ok (iotaState prims) (iotaState prims) from rfl]
  simp only
  have henv : (iotaState prims).env.get? iotaId =
      some iotaConcrete := by
    simp [iotaState, KEnv.get?, KEnv.insert]
  rw [henv]
  rfl

theorem iotaGetZero (prims : Primitives .anon) :
    TcM.tryGetConst zeroId (iotaState prims) =
      .ok (some zeroConcrete) (iotaState prims) := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _
    (iotaState prims) = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) (iotaState prims) =
    .ok (iotaState prims) (iotaState prims) from rfl]
  simp only
  have hne : iotaId ≠ zeroId := by
    intro h
    exact address_ne (a := 14) (b := 11) (by decide)
      (congrArg KId.addr h)
  have henv : (iotaState prims).env.get? zeroId = some zeroConcrete := by
    simp only [iotaState, KEnv.get?, KEnv.insert,
      Std.HashMap.getElem?_insert]
    split
    · next h => exact False.elim (hne (eq_of_beq h))
    · simpa [noAccelState, state] using loadedEnv_zero_k1e
  rw [henv]
  rfl

theorem iotaMajorWhnf (prims : Primitives .anon) (flags : WhnfFlags) :
    (if flags.cheapRec then
        (RecM.whnfCoreFlagsRec iotaResult flags).run betaHarnessMethods
          (iotaState prims)
      else (RecM.whnfRec iotaResult).run betaHarnessMethods
          (iotaState prims)) = .ok iotaResult (iotaState prims) := by
  cases flags.cheapRec <;>
    simp [RecM.whnfCoreFlagsRec, RecM.whnfRec, betaHarnessMethods] <;> rfl

theorem iotaCleanup (prims : Primitives .anon) :
    (RecM.cleanupNatOffsetMajor iotaResult).run betaHarnessMethods
      (iotaState prims) = .ok none (iotaState prims) := by
  have hextract : extractNatValue iotaResult (iotaPrims prims) = some 0 := by
    unfold iotaResult extractNatValue extractNatLit
    simp [iotaPrims]
  have heval :
      (RecM.evalNatOffsetLiteral iotaResult 0).run betaHarnessMethods
        (iotaState prims) = .ok (some 0) (iotaState prims) := by
    unfold RecM.evalNatOffsetLiteral RecM.evalNatOffsetLiteralFuel
    rw [ReaderT.run_bind]
    change EStateM.bind
      (ReaderT.run RecM.prims betaHarnessMethods) _ (iotaState prims) = _
    unfold EStateM.bind
    rw [show ReaderT.run RecM.prims betaHarnessMethods (iotaState prims) =
      .ok (iotaPrims prims) (iotaState prims) from rfl]
    simp only
    rw [hextract]
    rfl
  unfold RecM.cleanupNatOffsetMajor
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (RecM.evalNatOffsetLiteral iotaResult 0)
      betaHarnessMethods) _ (iotaState prims) = _
  unfold EStateM.bind
  rw [heval]
  rfl

theorem iotaInstantiateRule (prims : Primitives .anon) :
    TcM.instantiateUnivParams iotaRule.rhs #[] (iotaState prims) =
      .ok iotaResult (iotaState prims) := by
  rfl

/-- Exact execution of the real iota helper on the untrusted recursor-shaped
catalog entry.  All parameter/motive/minor/field/trailing loops are empty,
but recursor lookup, major cleanup/WHNF, constructor lookup, and universe
instantiation are the production operations. -/
theorem iotaTryEval (prims : Primitives .anon) (flags : WhnfFlags) :
    (RecM.tryIotaWithFlags iotaSource flags).run betaHarnessMethods
      (iotaState prims) = .ok (some iotaResult) (iotaState prims) := by
  unfold RecM.tryIotaWithFlags iotaSource iotaHead
  rw [KExpr.mkApp_shape, KExpr.mkConst_shape]
  simp only [KExpr.collectSpine, KExpr.collectSpine.go]
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst iotaId) _ (iotaState prims) = _
  unfold EStateM.bind
  rw [iotaGetRec]
  simp [iotaConcrete, iotaRule]
  change EStateM.bind
    (ReaderT.run (RecM.cleanupNatOffsetMajor iotaResult)
      betaHarnessMethods) _ (iotaState prims) = _
  unfold EStateM.bind
  rw [iotaCleanup]
  simp only [Option.getD]
  cases hcheap : flags.cheapRec <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    rw [ReaderT.run_bind]
    change EStateM.bind _ _ (iotaState prims) = _
    unfold EStateM.bind
    have hmajor := iotaMajorWhnf prims flags
    simp only [hcheap, Bool.false_eq_true, ↓reduceIte] at hmajor
    rw [hmajor]
    simp only
    rw [iotaResult]
    simp only
    rw [ReaderT.run_bind]
    change EStateM.bind
      (ReaderT.run
        (RecM.cleanupNatOffsetMajor
          (.const zeroId #[] (info iotaAddress)))
        betaHarnessMethods) _ (iotaState prims) = _
    unfold EStateM.bind
    have hcleanup := iotaCleanup prims
    rw [iotaResult] at hcleanup
    rw [hcleanup]
    simp only
    simp only [KExpr.collectSpine.go]
    rw [ReaderT.run_bind, ReaderT.run_monadLift]
    change EStateM.bind (TcM.tryGetConst zeroId) _ (iotaState prims) = _
    unfold EStateM.bind
    rw [iotaGetZero]
    simp [zeroConcrete]
    have hinst := iotaInstantiateRule prims
    simp only [iotaRule] at hinst
    rw [iotaResult] at hinst
    show EStateM.map _ _ (iotaState prims) = _
    unfold EStateM.map
    rw [hinst]

theorem iotaStepEval (prims : Primitives .anon) (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep iotaSource flags).run betaHarnessMethods
      (iotaState prims) = .ok (.next iotaResult) (iotaState prims) := by
  unfold iotaSource iotaHead
  rw [KExpr.mkApp_shape, KExpr.mkConst_shape]
  apply RecM.whnfCoreWithFlagsStep_iota
    (recId := iotaId) (us := #[])
    (headInfo := (KExpr.mkConst iotaId #[] ()).info)
    (args := #[iotaResult])
  · simp [KExpr.collectSpine, KExpr.collectSpine.go]
  · rfl
  · change Bool.not ((KExpr.mkConst iotaId #[] ()).info.addr ==
        (KExpr.mkConst iotaId #[] ()).info.addr) = false
    rw [beq_self_eq_true]
    rfl
  · exact iotaTryEval prims flags

theorem iotaCoreEval (prims : Primitives .anon) (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsUncached iotaSource flags).run
      betaHarnessMethods (iotaState prims) =
        .ok iotaResult (iotaState prims) := by
  apply RecM.whnfCoreWithFlagsUncached_nextLeaf
  · exact iotaStepEval prims flags
  · exact .const

theorem nameOf_iota_none : nameOf iotaAddress = none := by
  rfl

theorem iotaHead_not_translated :
    ¬∃ headV,
      TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
        iotaHead headV := by
  rintro ⟨headV, hhead⟩
  unfold iotaHead at hhead
  rw [KExpr.mkConst_shape] at hhead
  cases hhead with
  | const hname _ _ _ =>
      change nameOf iotaAddress = some _ at hname
      rw [nameOf_iota_none] at hname
      contradiction

theorem iotaSource_not_translated :
    ¬∃ sourceV,
      TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
        iotaSource sourceV := by
  rintro ⟨sourceV, hsource⟩
  unfold iotaSource at hsource
  rw [KExpr.mkApp_shape] at hsource
  cases hsource with
  | app _ _ hhead _ => exact iotaHead_not_translated ⟨_, hhead⟩

theorem iotaAdversarialWitness (prims : Primitives .anon)
    (flags : WhnfFlags) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood support
        0 [] (iotaState prims) ∧
      (RecM.whnfCoreWithFlagsUncached iotaSource flags).run
        betaHarnessMethods (iotaState prims) =
          .ok iotaResult (iotaState prims) ∧
      ¬∃ sourceV,
        TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
          iotaSource sourceV :=
  ⟨iotaStateInv prims, iotaCoreEval prims flags,
    iotaSource_not_translated⟩

/-! ### K1f structural-loop composition witness -/

/-- Literal closure for this finite ambient world.  Nat literals are typed by
the installed `Nat.zero`/`Nat.succ` constants; String literal support is
provably absent. -/
theorem structuralNatLit_type (n : Nat) :
    worldGood.venv.HasType 0 [] (VExpr.natLit n) (.const natName []) := by
  induction n with
  | zero =>
      simpa [VExpr.natLit, VExpr.natZero, zeroName] using betaArg_type
  | succ n ih =>
      have hsucc : worldGood.venv.HasType 0 [] (.const succName [])
          (.forallE (.const natName []) (.const natName [])) := by
        exact Lean4Lean.VEnv.HasType.const (env := worldGood.venv)
          (U := 0) (Γ := []) (ci := succConstant) (ls := [])
          (by simpa [worldGood, goodEnv, goodName, succName] using natEnv_succ)
          (by intro l hl; simp at hl) rfl
      simpa [VExpr.natLit, VExpr.natSucc, succName] using
        Lean4Lean.VEnv.HasType.app hsucc ih

/-- The finite Nat world supplies the uniform literal/projection facts needed
to compose arbitrary structural trace meanings. -/
def structuralWhnfTheory : WhnfTheory RawProjRel.none worldGood 0 where
  literalWF := by
    intro literal hliteral
    cases literal with
    | natVal n => exact ⟨_, structuralNatLit_type n⟩
    | strVal value =>
        simp [Lean4Lean.VEnv.ContainsLits, Lean4Lean.VEnv.contains,
          worldGood, goodEnv, natEnv, natEnv₂, natEnv₁, goodName,
          natName, zeroName, succName] at hliteral
  projections := RawProjRel.none_ok worldGood.venv 0

/-- Translation of the closed beta redex, used as the value stored in the
let-bound fvar below. -/
theorem structuralBetaSource_tr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
      betaSource
      (.app (.lam (.const natName []) (.bvar 0)) (.const zeroName [])) := by
  rw [betaSource, betaLam, KExpr.mkApp_shape, KExpr.mkLam_shape]
  exact .app (Lean4Lean.VEnv.HasType.lam betaA_type betaBody_type)
    betaArg_type (.lam ⟨_, betaA_type⟩ betaTy_tr betaBody_tr) betaArg_tr

theorem structuralBetaSource_type :
    worldGood.venv.HasType 0 []
      (.app (.lam (.const natName []) (.bvar 0)) (.const zeroName []))
      (.const natName []) := by
  simpa using Lean4Lean.VEnv.HasType.app
    (Lean4Lean.VEnv.HasType.lam betaA_type betaBody_type) betaArg_type

theorem structuralBetaSource_constructed : KExpr.Constructed betaSource := by
  unfold betaSource betaLam betaBody
  exact .app (.lam supportExpr_constructed (.var (by decide)))
    betaArg_constructed

theorem structuralBetaSource_closed : betaSource.lbr = 0 := by
  rfl

/-- A let-bound fvar whose value is itself the beta redex.  Production must
therefore take two `.next` transitions before reaching the constant leaf. -/
def structuralLoopSource : KExpr .anon := KExpr.mkFVar fvarZetaId ()

def structuralLoopCtx : KVLCtx :=
  [(some (fvarZetaId, []),
    .vlet (.const natName [])
      (.app (.lam (.const natName []) (.bvar 0)) (.const zeroName [])))]

def structuralLoopState (prims : Primitives .anon) : TcState .anon :=
  let base := noAccelState prims
  { base with
    env := { base.env with nextFVarId := 1 }
    lctx := base.lctx.push fvarZetaId
      (.ldecl () supportExpr betaSource) }

theorem structuralLoopFind (prims : Primitives .anon) :
    (structuralLoopState prims).lctx.find? fvarZetaId =
      some (.ldecl () supportExpr betaSource) := by
  simp [structuralLoopState, noAccelState, LocalContext.find?,
    LocalContext.push, fvarZetaId]

theorem structuralLoopCtxRecon (prims : Primitives .anon) :
    CtxRecon worldGood.venv 0 worldGood.nameOf RawProjRel.none
      (structuralLoopState prims) structuralLoopCtx := by
  refine {
    size_eq := rfl
    recon := ?_
    lwf := ?_
    incr := by
      simp [structuralLoopState, noAccelState, state, LocalContext.push]
    fresh := ?_
    lets := rfl }
  · have hrec :
        CtxRecon' worldGood.venv 0 worldGood.nameOf RawProjRel.none
          [] [(fvarZetaId, .ldecl () supportExpr betaSource)]
            structuralLoopCtx :=
      .fvar .nil
        (.vlet betaTy_tr structuralBetaSource_tr structuralBetaSource_type)
        (by simp)
    simpa [structuralLoopState, noAccelState, LocalContext.push] using hrec
  · apply LocalContext.WF.push .empty
    simp [fvarZetaId]
  · intro p hp
    simp [structuralLoopState, noAccelState, state, LocalContext.push] at hp
    subst p
    simp [structuralLoopState, fvarZetaId]

theorem structuralLoopStateInv (prims : Primitives .anon) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood support
      0 structuralLoopCtx (structuralLoopState prims) := by
  have hbase := noAccelStateInv prims
  refine ⟨?_, structuralLoopCtxRecon prims, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hbase.1.core.of_consts_eq (by rfl) (by
      simpa [structuralLoopState] using hbase.1.core.intern)
  · simpa [structuralLoopState] using hbase.1.internSupport
  · intro entry hentry
    apply hbase.1.caches
    cases hentry <;> (constructor; assumption)

/-- First local meaning: fvar zeta exposes the closed beta redex. -/
theorem structuralLoopSourceMeaning (prims : Primitives .anon) :
    WhnfMeaning RawProjRel.none worldGood 0 structuralLoopCtx
      structuralLoopSource betaSource := by
  unfold structuralLoopSource
  rw [KExpr.mkFVar_shape]
  apply WhnfMeaning.zetaFVar (structuralLoopCtxRecon prims)
    (RawProjRel.none_ok worldGood.venv 0)
    (structuralLoopFind prims) structuralBetaSource_constructed
    structuralBetaSource_closed
  decide

theorem structuralLoopTy_tr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none
      structuralLoopCtx supportExpr (.const natName []) := by
  rw [supportExpr_eq_mkConst, KExpr.mkConst_shape]
  exact .const (ci := natConstant) nameOf_nat
    (by simpa [worldGood, goodEnv, goodName, natName] using natEnv_nat)
    (by intro l hl; simp at hl) rfl

theorem structuralLoopBody_tr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none
      ((none, .vlam (.const natName [])) :: structuralLoopCtx)
      betaBody (.bvar 0) := by
  rw [betaBody, KExpr.mkVar_shape]
  exact .var rfl

theorem structuralLoopArg_tr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none
      structuralLoopCtx betaArg (.const zeroName []) := by
  rw [betaArg, KExpr.mkConst_shape]
  exact .const (ci := zeroConstant) nameOf_zero
    (by simpa [worldGood, goodEnv, goodName, zeroName] using natEnv_zero)
    (by intro l hl; simp at hl) rfl

theorem structuralLoopA_type :
    worldGood.venv.HasType 0 structuralLoopCtx.toCtx (.const natName [])
      (.sort (.succ .zero)) := by
  simpa [structuralLoopCtx] using betaA_type

theorem structuralLoopBody_type :
    worldGood.venv.HasType 0
      ((.const natName []) :: structuralLoopCtx.toCtx) (.bvar 0)
      (.const natName []) := by
  simpa [structuralLoopCtx] using betaBody_type

theorem structuralLoopArg_type :
    worldGood.venv.HasType 0 structuralLoopCtx.toCtx (.const zeroName [])
      (.const natName []) := by
  simpa [structuralLoopCtx] using betaArg_type

/-- Second local meaning: beta reduces the exposed identity application to
`Nat.zero` in the same mixed context. -/
theorem structuralLoopBetaMeaning :
    WhnfMeaning RawProjRel.none worldGood 0 structuralLoopCtx
      betaSource betaArg := by
  rw [← betaSimulResult]
  unfold betaSource betaLam
  rw [KExpr.mkApp_shape, KExpr.mkLam_shape]
  apply WhnfMeaning.betaSimul
  · apply WhnfMeaning.beta (RawProjRel.none_ok worldGood.venv 0)
      structuralLoopTy_tr structuralLoopBody_tr structuralLoopArg_tr
      structuralLoopA_type structuralLoopBody_type structuralLoopArg_type
    decide
  · exact betaSimulSpec

theorem structuralLoopLeafMeaning :
    WhnfMeaning RawProjRel.none worldGood 0 structuralLoopCtx
      betaArg betaArg := by
  apply WhnfMeaning.refl structuralLoopArg_tr
  exact ⟨_, structuralLoopArg_type⟩

theorem structuralLoopFVarStep (prims : Primitives .anon)
    (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep structuralLoopSource flags).run
      betaHarnessMethods (structuralLoopState prims) =
        .ok (.next betaSource) (structuralLoopState prims) := by
  unfold structuralLoopSource
  rw [KExpr.mkFVar_shape]
  exact RecM.whnfCoreWithFlagsStep_fvarZeta (structuralLoopFind prims)

theorem structuralLoopWalkerEval (prims : Primitives .anon) :
    TcM.runIntern (simulSubst betaBody #[betaArg] 0)
      (structuralLoopState prims) =
        .ok betaArg (structuralLoopState prims) := by
  unfold TcM.runIntern
  rw [betaWalker_intern]

theorem structuralLoopBetaStep (prims : Primitives .anon)
    (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep betaSource flags).run betaHarnessMethods
      (structuralLoopState prims) =
        .ok (.next betaArg) (structuralLoopState prims) := by
  unfold betaSource betaLam
  rw [KExpr.mkApp_shape, KExpr.mkLam_shape]
  simpa [betaSimulResult] using
    (RecM.whnfCoreWithFlagsStep_betaOne
      (methods := betaHarnessMethods) (s := structuralLoopState prims)
      (flags := flags) (hhead := rfl)
      (hwalk := structuralLoopWalkerEval prims))

theorem structuralLoopLeafStep (prims : Primitives .anon)
    (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep betaArg flags).run betaHarnessMethods
      (structuralLoopState prims) =
        .ok (.done betaArg) (structuralLoopState prims) :=
  RecM.whnfCoreWithFlagsStep_leaf .const flags

/-- Three exact iterations at production fuel: fvar-zeta, beta, then leaf.
The trace carries the same fixed world/context invariant throughout. -/
theorem structuralLoopTrace (prims : Primitives .anon)
    (flags : WhnfFlags) :
    RecM.WhnfCoreTrace .noAccel whnfSemantics RawProjRel.none worldGood
      support 0 structuralLoopCtx betaHarnessMethods flags maxWhnfFuel.toNat
      structuralLoopSource (structuralLoopState prims) betaArg
      (structuralLoopState prims) := by
  rw [show maxWhnfFuel.toNat = 10000 by rfl]
  refine .next (structuralLoopStateInv prims)
    (structuralLoopFVarStep prims flags) (structuralLoopStateInv prims)
    (structuralLoopSourceMeaning prims) ?_
  refine .next (structuralLoopStateInv prims)
    (structuralLoopBetaStep prims flags) (structuralLoopStateInv prims)
    structuralLoopBetaMeaning ?_
  exact .done (structuralLoopStateInv prims)
    (structuralLoopLeafStep prims flags) (structuralLoopStateInv prims)
    structuralLoopLeafMeaning

/-- Inhabited K1f acceptance: the real bounded driver executes more than one
`.next`, preserves the full invariant, and obtains the end-to-end meaning by
transitive composition rather than by asserting source/result equality. -/
theorem structuralLoopAcceptance (prims : Primitives .anon)
    (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsUncached structuralLoopSource flags).run
        betaHarnessMethods (structuralLoopState prims) =
          .ok betaArg (structuralLoopState prims) ∧
      WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood support
        0 structuralLoopCtx (structuralLoopState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 structuralLoopCtx
        structuralLoopSource betaArg := by
  have h := (structuralLoopTrace prims flags).uncached_acceptance
    structuralWhnfTheory
  exact ⟨h.1, h.2.1, h.2.2.2⟩

/-- Adversarial fuel boundary: the same source at zero fuel throws before
consulting the step function, and therefore cannot have a semantic trace. -/
theorem structuralLoopZeroFuel (prims : Primitives .anon)
    (flags : WhnfFlags) :
    (RecM.runBounded
      (fun cur => RecM.whnfCoreWithFlagsStep cur flags) 0
      structuralLoopSource).run betaHarnessMethods (structuralLoopState prims) =
        .error .maxRecDepth (structuralLoopState prims) ∧
      ¬RecM.WhnfCoreTrace .noAccel whnfSemantics RawProjRel.none worldGood
        support 0 structuralLoopCtx betaHarnessMethods flags 0
        structuralLoopSource (structuralLoopState prims) betaArg
        (structuralLoopState prims) :=
  ⟨rfl, RecM.WhnfCoreTrace.no_zero⟩

/-! ### K1g outer structural-WHNF cache composition witness -/

/-- The outer-cache fixture supports both the beta redex used as its key and
the reduced constant stored as its value.  Universal cache validity below
covers either supported source if their addresses happen to collide. -/
def coreCacheSupport : RunSupport where
  expr e := e = betaSource ∨ e = betaArg
  exprFinite := ⟨[betaSource, betaArg], by
    intro e he
    rcases he with rfl | rfl <;> simp⟩
  univ _ := False
  univFinite := FiniteSupport.empty

def coreCacheKey : Address × Address :=
  (betaSource.addr, emptyCtxAddr)

private theorem betaArg_references {id : KId .anon}
    (h : betaArg.References id) : id = zeroId := by
  change zeroId = id at h
  exact h.symm

private theorem betaSource_references {id : KId .anon}
    (h : betaSource.References id) : id = natId ∨ id = zeroId := by
  unfold betaSource betaLam at h
  rw [KExpr.mkApp_shape, KExpr.mkLam_shape] at h
  change (supportExpr.References id ∨ betaBody.References id) ∨
    betaArg.References id at h
  rcases h with (h | h) | h
  · change natId = id at h
    exact .inl h.symm
  · rw [betaBody, KExpr.mkVar_shape] at h
    exact False.elim h
  · exact .inr (betaArg_references h)

theorem betaArgMeaning :
    WhnfMeaning RawProjRel.none worldGood 0 [] betaArg betaArg := by
  exact WhnfMeaning.refl betaArg_tr ⟨_, betaArg_type⟩

private theorem coreCacheReferencesAuthorized (kind : ExprCacheKind) :
    (CacheEntry.expr kind coreCacheKey betaArg).ReferencesAuthorized
      (CacheAuthority.stable worldGood) coreCacheSupport := by
  intro id href
  left
  change CacheEntry.SourceReferences coreCacheSupport betaSource.addr id ∨
    betaArg.References id at href
  rcases href with href | href
  · obtain ⟨e, he, haddr, heref⟩ := href
    change e = betaSource ∨ e = betaArg at he
    rcases he with rfl | rfl
    · rcases betaSource_references heref with rfl | rfl
      · exact nat_trusted_good
      · exact zero_trusted_good
    · have hid := betaArg_references heref
      subst id
      exact zero_trusted_good
  · have hid := betaArg_references href
    subst id
    exact zero_trusted_good

/-- The validity proof is deliberately collision-robust: both supported
expressions that could inhabit the address key have the required meaning. -/
private theorem coreCacheWhnfValid (kind : ExprCacheKind)
    (hkind : kind = .whnfCore ∨ kind = .whnfCoreCheap) :
    WhnfCacheValid whnfContextKeys RawProjRel.none
      CacheSemantics.blockErrorsOnly (CacheAuthority.stable worldGood)
      coreCacheSupport (.expr kind coreCacheKey betaArg) := by
  rcases hkind with rfl | rfl <;>
    intro source hsource haddr Δ hctx
  all_goals
    change source = betaSource ∨ source = betaArg at hsource
    rcases hsource with rfl | rfl
    · have hΔ : Δ = [] := by
        simpa [whnfContextKeys, coreCacheKey] using hctx.2
      subst Δ
      exact betaResultMeaning
    · have hΔ : Δ = [] := by
        simpa [whnfContextKeys, coreCacheKey] using hctx.2
      subst Δ
      exact betaArgMeaning

theorem fullCoreProvenance :
    CacheProvenance whnfSemantics (CacheAuthority.stable worldGood)
      coreCacheSupport (.expr .whnfCore coreCacheKey betaArg) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨⟨betaSource, .inl rfl, rfl⟩, .inr rfl⟩
  · exact coreCacheReferencesAuthorized .whnfCore
  · exact coreCacheWhnfValid .whnfCore (.inl rfl)

theorem cheapCoreProvenance :
    CacheProvenance whnfSemantics (CacheAuthority.stable worldGood)
      coreCacheSupport (.expr .whnfCoreCheap coreCacheKey betaArg) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨⟨betaSource, .inl rfl, rfl⟩, .inr rfl⟩
  · exact coreCacheReferencesAuthorized .whnfCoreCheap
  · exact coreCacheWhnfValid .whnfCoreCheap (.inr rfl)

theorem coreCacheFreshStateInv (prims : Primitives .anon) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
      coreCacheSupport 0 [] (noAccelState prims) := by
  refine ⟨?_, ?_, rfl⟩
  · apply KernelStateWF.of_no_cache_entries
    · exact (stateWF prims).of_env_eq rfl
    · constructor
      · intro x hx
        obtain ⟨a, ha⟩ := hx
        simp [noAccelState, state, loadedEnv, KEnv.insert] at ha
      · intro x hx
        obtain ⟨a, ha⟩ := hx
        simp [noAccelState, state, loadedEnv, KEnv.insert] at ha
    · intro entry
      simpa [noAccelState, state] using loadedEnv_noCacheEntries entry
  · apply CtxRecon.empty <;> rfl

def fullCoreWarmState (prims : Primitives .anon) : TcState .anon :=
  let s := noAccelState prims
  {s with env := {s.env with
    whnfCoreCache := s.env.whnfCoreCache.insert coreCacheKey betaArg}}

def bothCoreWarmState (prims : Primitives .anon) : TcState .anon :=
  let s := fullCoreWarmState prims
  {s with env := {s.env with
    whnfCoreCheapCache := s.env.whnfCoreCheapCache.insert coreCacheKey betaArg}}

theorem fullCoreWarmStateInv (prims : Primitives .anon) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
      coreCacheSupport 0 [] (fullCoreWarmState prims) := by
  exact RecM.WhnfCoreCacheUpdate.full_whnfStateInv
    (coreCacheFreshStateInv prims) fullCoreProvenance

theorem bothCoreWarmStateInv (prims : Primitives .anon) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
      coreCacheSupport 0 [] (bothCoreWarmState prims) := by
  exact RecM.WhnfCoreCacheUpdate.cheap_whnfStateInv
    (fullCoreWarmStateInv prims) cheapCoreProvenance

theorem coreCacheKey_eval (s : TcState .anon) :
    TcM.whnfKey betaSource s = .ok coreCacheKey s := by
  simpa [coreCacheKey] using
    (TcM.whnfKey_closed (s := s) structuralBetaSource_closed)

theorem coreCacheKey_matches (s : TcState .anon)
    (hctx : CtxRecon worldGood.venv 0 worldGood.nameOf RawProjRel.none s []) :
    whnfContextKeys.Matches RawProjRel.none worldGood s [] betaSource
      coreCacheKey := by
  refine ⟨hctx, ?_, ⟨s, coreCacheKey_eval s⟩⟩
  simp [whnfContextKeys, coreCacheKey]

theorem betaTransientFalse (s : TcState .anon) :
    (RecM.isTransientNatLiteralWork betaSource).run betaHarnessMethods s =
      .ok false s := by
  unfold RecM.isTransientNatLiteralWork RecM.isNatLiteralRecursorApp
  unfold betaSource betaLam
  rw [KExpr.mkApp_shape, KExpr.mkLam_shape]
  simp [KExpr.collectSpine, KExpr.collectSpine.go]
  rfl

theorem betaWalker_eval_state (s : TcState .anon) :
    TcM.runIntern (simulSubst betaBody #[betaArg] 0) s = .ok betaArg s := by
  unfold TcM.runIntern
  rw [betaWalker_intern]

theorem betaStep_state (s : TcState .anon) (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep betaSource flags).run betaHarnessMethods s =
      .ok (.next betaArg) s := by
  unfold betaSource betaLam
  rw [KExpr.mkApp_shape, KExpr.mkLam_shape]
  simpa [betaSimulResult] using
    (RecM.whnfCoreWithFlagsStep_betaOne
      (methods := betaHarnessMethods) (s := s) (flags := flags)
      (hhead := rfl) (hwalk := betaWalker_eval_state s))

theorem coreCacheTrace {s : TcState .anon}
    (hI : WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
      coreCacheSupport 0 [] s) (flags : WhnfFlags) :
    RecM.WhnfCoreTrace .noAccel whnfSemantics RawProjRel.none worldGood
      coreCacheSupport 0 [] betaHarnessMethods flags maxWhnfFuel.toNat
      betaSource s betaArg s := by
  rw [show maxWhnfFuel.toNat = 10000 by rfl]
  refine .next hI (betaStep_state s flags) hI betaResultMeaning ?_
  exact .done hI (RecM.whnfCoreWithFlagsStep_leaf .const flags) hI
    betaArgMeaning

theorem coreCacheFresh_fullMiss (prims : Primitives .anon) :
    (noAccelState prims).env.whnfCoreCache[coreCacheKey]? = none := by
  simp [noAccelState, state, loadedEnv, KEnv.insert, coreCacheKey]

theorem fullCoreWarm_hit (prims : Primitives .anon) :
    (fullCoreWarmState prims).env.whnfCoreCache[coreCacheKey]? =
      some betaArg := by
  simp [fullCoreWarmState, coreCacheKey]

theorem fullCoreWarm_cheapMiss (prims : Primitives .anon) :
    (fullCoreWarmState prims).env.whnfCoreCheapCache[coreCacheKey]? = none := by
  simp [fullCoreWarmState, noAccelState, state, loadedEnv, KEnv.insert,
    coreCacheKey]

theorem bothCoreWarm_cheapHit (prims : Primitives .anon) :
    (bothCoreWarmState prims).env.whnfCoreCheapCache[coreCacheKey]? =
      some betaArg := by
  simp [bothCoreWarmState, coreCacheKey]

/-- First full-policy call: the real outer entry point misses, executes its
certified beta trace, inserts the result, and preserves the invariant. -/
theorem fullCoreColdAcceptance (prims : Primitives .anon) :
    (RecM.whnfCoreWithFlags betaSource .FULL).run betaHarnessMethods
        (noAccelState prims) = .ok betaArg (fullCoreWarmState prims) ∧
      WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (noAccelState prims) ∧
      WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullCoreWarmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  simpa [whnfSemantics, fullCoreWarmState] using
    (RecM.whnfCoreWithFlags_fullMiss_acceptance
      (keys := whnfContextKeys) (fallback := CacheSemantics.blockErrorsOnly)
      structuralWhnfTheory (.direct RecM.WhnfCoreNonLeaf.app) rfl
      (coreCacheKey_eval (noAccelState prims))
      (betaTransientFalse (noAccelState prims))
      (coreCacheFresh_fullMiss prims)
      (coreCacheTrace (coreCacheFreshStateInv prims) .FULL)
      fullCoreProvenance)

/-- Second full-policy call: the inserted entry is consumed as a semantic
hit and the entire checker state remains unchanged. -/
theorem fullCoreWarmAcceptance (prims : Primitives .anon) :
    (RecM.whnfCoreWithFlags betaSource .FULL).run betaHarnessMethods
        (fullCoreWarmState prims) = .ok betaArg (fullCoreWarmState prims) ∧
      WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullCoreWarmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  simpa [whnfSemantics] using
    (RecM.whnfCoreWithFlags_fullHit_acceptance
      (keys := whnfContextKeys) (fallback := CacheSemantics.blockErrorsOnly)
      (.direct RecM.WhnfCoreNonLeaf.app) rfl
      (coreCacheKey_eval (fullCoreWarmState prims))
      (betaTransientFalse (fullCoreWarmState prims))
      (fullCoreWarm_hit prims) (fullCoreWarmStateInv prims) (.inl rfl)
      (coreCacheKey_matches (fullCoreWarmState prims)
        (fullCoreWarmStateInv prims).2.1))

/-- A full-policy entry is intentionally invisible to the cheap policy.  The
cheap call therefore runs its own trace and inserts into only its partition. -/
theorem cheapCorePolicyMissAcceptance (prims : Primitives .anon) :
    (RecM.whnfCoreWithFlags betaSource .DEF_EQ_CORE).run betaHarnessMethods
        (fullCoreWarmState prims) = .ok betaArg (bothCoreWarmState prims) ∧
      WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullCoreWarmState prims) ∧
      WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (bothCoreWarmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  simpa [whnfSemantics, bothCoreWarmState] using
    (RecM.whnfCoreWithFlags_cheapMiss_acceptance
      (keys := whnfContextKeys) (fallback := CacheSemantics.blockErrorsOnly)
      structuralWhnfTheory (.direct RecM.WhnfCoreNonLeaf.app) rfl
      (coreCacheKey_eval (fullCoreWarmState prims))
      (betaTransientFalse (fullCoreWarmState prims))
      (fullCoreWarm_cheapMiss prims)
      (coreCacheTrace (fullCoreWarmStateInv prims) .DEF_EQ_CORE)
      cheapCoreProvenance)

/-- Once the cheap partition is populated, its next call is also a
state-preserving semantic hit. -/
theorem cheapCoreWarmAcceptance (prims : Primitives .anon) :
    (RecM.whnfCoreWithFlags betaSource .DEF_EQ_CORE).run betaHarnessMethods
        (bothCoreWarmState prims) = .ok betaArg (bothCoreWarmState prims) ∧
      WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (bothCoreWarmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  simpa [whnfSemantics] using
    (RecM.whnfCoreWithFlags_cheapHit_acceptance
      (keys := whnfContextKeys) (fallback := CacheSemantics.blockErrorsOnly)
      (.direct RecM.WhnfCoreNonLeaf.app) rfl
      (coreCacheKey_eval (bothCoreWarmState prims))
      (betaTransientFalse (bothCoreWarmState prims))
      (bothCoreWarm_cheapHit prims) (bothCoreWarmStateInv prims) (.inl rfl)
      (coreCacheKey_matches (bothCoreWarmState prims)
        (bothCoreWarmStateInv prims).2.1))

/-- Direct adversarial observation of the flag partition after only the full
call has warmed its map. -/
theorem coreCachePolicyIsolation (prims : Primitives .anon) :
    (fullCoreWarmState prims).env.whnfCoreCache[coreCacheKey]? =
        some betaArg ∧
      (fullCoreWarmState prims).env.whnfCoreCheapCache[coreCacheKey]? = none :=
  ⟨fullCoreWarm_hit prims, fullCoreWarm_cheapMiss prims⟩

/-! ### K1h no-delta/full-WHNF driver witness -/

theorem betaNoDeltaProjNone (prims : Primitives .anon) :
    (RecM.tryProjAppReduce betaArg .FULL).run betaHarnessMethods
      (fullCoreWarmState prims) = .ok none (fullCoreWarmState prims) := by
  unfold RecM.tryProjAppReduce betaArg
  rw [KExpr.mkConst_shape]
  rfl

theorem betaNoDeltaNatNone (prims : Primitives .anon) :
    (RecM.tryReduceNatWithSuccMode betaArg .collapse).run betaHarnessMethods
      (fullCoreWarmState prims) = .ok none (fullCoreWarmState prims) := by
  unfold RecM.tryReduceNatWithSuccMode betaArg
  rw [KExpr.mkConst_shape]
  simp [KExpr.collectSpine, KExpr.collectSpine.go, RecM.prims]
  rfl

theorem betaNoDeltaStringNone (prims : Primitives .anon) :
    (RecM.tryReduceString betaArg).run betaHarnessMethods
      (fullCoreWarmState prims) = .ok none (fullCoreWarmState prims) := by
  unfold RecM.tryReduceString betaArg
  rw [KExpr.mkConst_shape]
  rfl

theorem fullCoreWarm_getZero (prims : Primitives .anon) :
    TcM.tryGetConst zeroId (fullCoreWarmState prims) =
      .ok (some zeroConcrete) (fullCoreWarmState prims) := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _
    (fullCoreWarmState prims) = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) (fullCoreWarmState prims) =
    .ok (fullCoreWarmState prims) (fullCoreWarmState prims) from rfl]
  simp only
  have henv : (fullCoreWarmState prims).env.get? zeroId =
      some zeroConcrete := by
    simpa [fullCoreWarmState, noAccelState, state] using loadedEnv_zero_k1e
  rw [henv]
  rfl

theorem betaNoDeltaProjectionDefNone (prims : Primitives .anon) :
    (RecM.tryReduceProjectionDefinition betaArg).run betaHarnessMethods
      (fullCoreWarmState prims) = .ok none (fullCoreWarmState prims) := by
  unfold RecM.tryReduceProjectionDefinition betaArg
  rw [KExpr.mkConst_shape]
  simp only [KExpr.collectSpine, KExpr.collectSpine.go]
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.tryGetConst zeroId) _ (fullCoreWarmState prims) = _
  unfold EStateM.bind
  rw [fullCoreWarm_getZero prims]
  rfl

theorem betaNoDeltaQuotNone (prims : Primitives .anon) :
    (RecM.tryQuotReduce betaArg).run betaHarnessMethods
      (fullCoreWarmState prims) = .ok none (fullCoreWarmState prims) := by
  unfold RecM.tryQuotReduce betaArg
  rw [KExpr.mkConst_shape]
  simp [KExpr.collectSpine, KExpr.collectSpine.go, RecM.prims]
  rfl

/-- The no-delta driver consumes the already certified structural cache hit,
then checks every remaining reducer in production order before terminating. -/
theorem betaNoDeltaStep (prims : Primitives .anon) :
    (RecM.whnfNoDeltaImplStep .FULL .collapse betaSource).run
      betaHarnessMethods (fullCoreWarmState prims) =
      .ok (.done betaArg) (fullCoreWarmState prims) := by
  unfold RecM.whnfNoDeltaImplStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.whnfCoreWithFlags betaSource .FULL).run betaHarnessMethods) _
      (fullCoreWarmState prims) = _
  unfold EStateM.bind
  rw [(fullCoreWarmAcceptance prims).1]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.tryProjAppReduce betaArg .FULL).run betaHarnessMethods) _
      (fullCoreWarmState prims) = _
  unfold EStateM.bind
  rw [betaNoDeltaProjNone prims]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.tryReduceBitvec betaArg).run betaHarnessMethods) _
      (fullCoreWarmState prims) = _
  unfold EStateM.bind
  rw [RecM.tryReduceBitvec_noAccel rfl]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.tryReduceNatWithSuccMode betaArg .collapse).run betaHarnessMethods) _
      (fullCoreWarmState prims) = _
  unfold EStateM.bind
  rw [betaNoDeltaNatNone prims]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.tryReduceNative betaArg).run betaHarnessMethods) _
      (fullCoreWarmState prims) = _
  unfold EStateM.bind
  rw [RecM.tryReduceNative_noAccel rfl]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.tryReduceString betaArg).run betaHarnessMethods) _
      (fullCoreWarmState prims) = _
  unfold EStateM.bind
  rw [betaNoDeltaStringNone prims]
  simp [WhnfFlags.FULL, WhnfFlags.isFull]
  change EStateM.bind
    ((RecM.tryReduceProjectionDefinition betaArg).run betaHarnessMethods) _
      (fullCoreWarmState prims) = _
  unfold EStateM.bind
  rw [betaNoDeltaProjectionDefNone prims]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.tryQuotReduce betaArg).run betaHarnessMethods) _
      (fullCoreWarmState prims) = _
  unfold EStateM.bind
  rw [betaNoDeltaQuotNone prims]
  rfl

private theorem driverCacheWhnfValid (kind : ExprCacheKind)
    (hkind : kind = .whnf ∨ kind = .whnfNoDelta ∨
      kind = .whnfNoDeltaCheap) :
    WhnfCacheValid whnfContextKeys RawProjRel.none
      CacheSemantics.blockErrorsOnly (CacheAuthority.stable worldGood)
      coreCacheSupport (.expr kind coreCacheKey betaArg) := by
  rcases hkind with rfl | rfl | rfl <;>
    intro source hsource haddr Δ hctx
  all_goals
    change source = betaSource ∨ source = betaArg at hsource
    rcases hsource with rfl | rfl
    · have hΔ : Δ = [] := by
        simpa [whnfContextKeys, coreCacheKey] using hctx.2
      subst Δ
      exact betaResultMeaning
    · have hΔ : Δ = [] := by
        simpa [whnfContextKeys, coreCacheKey] using hctx.2
      subst Δ
      exact betaArgMeaning

theorem fullNoDeltaProvenance :
    CacheProvenance whnfSemantics (CacheAuthority.stable worldGood)
      coreCacheSupport (.expr .whnfNoDelta coreCacheKey betaArg) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨⟨betaSource, .inl rfl, rfl⟩, .inr rfl⟩
  · exact coreCacheReferencesAuthorized .whnfNoDelta
  · exact driverCacheWhnfValid .whnfNoDelta (.inr (.inl rfl))

theorem fullWhnfProvenance :
    CacheProvenance whnfSemantics (CacheAuthority.stable worldGood)
      coreCacheSupport (.expr .whnf coreCacheKey betaArg) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨⟨betaSource, .inl rfl, rfl⟩, .inr rfl⟩
  · exact coreCacheReferencesAuthorized .whnf
  · exact driverCacheWhnfValid .whnf (.inl rfl)

def fullNoDeltaWarmState (prims : Primitives .anon) : TcState .anon :=
  let s := fullCoreWarmState prims
  {s with env := {s.env with
    whnfNoDeltaCache := s.env.whnfNoDeltaCache.insert coreCacheKey betaArg}}

theorem fullNoDeltaWarmStateInv (prims : Primitives .anon) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
      coreCacheSupport 0 [] (fullNoDeltaWarmState prims) := by
  exact RecM.WhnfDriverCacheUpdate.noDelta_whnfStateInv
    (fullCoreWarmStateInv prims) fullNoDeltaProvenance

theorem noDeltaTrace (prims : Primitives .anon) :
    RecM.WhnfNoDeltaTrace .noAccel whnfSemantics RawProjRel.none worldGood
      coreCacheSupport 0 [] betaHarnessMethods .FULL .collapse
      maxWhnfFuel.toNat betaSource (fullCoreWarmState prims) betaArg
      (fullCoreWarmState prims) := by
  rw [show maxWhnfFuel.toNat = 10000 by rfl]
  exact .done (fullCoreWarmStateInv prims) (betaNoDeltaStep prims)
    (fullCoreWarmStateInv prims) betaResultMeaning

theorem fullCoreWarm_noDeltaMiss (prims : Primitives .anon) :
    (fullCoreWarmState prims).env.whnfNoDeltaCache[coreCacheKey]? = none := by
  simp [fullCoreWarmState, noAccelState, state, loadedEnv, KEnv.insert,
    coreCacheKey]

theorem fullNoDeltaWarm_hit (prims : Primitives .anon) :
    (fullNoDeltaWarmState prims).env.whnfNoDeltaCache[coreCacheKey]? =
      some betaArg := by
  simp [fullNoDeltaWarmState, coreCacheKey]

theorem fullNoDeltaWarm_cheapMiss (prims : Primitives .anon) :
    (fullNoDeltaWarmState prims).env.whnfNoDeltaCheapCache[coreCacheKey]? =
      none := by
  simp [fullNoDeltaWarmState, fullCoreWarmState, noAccelState, state,
    loadedEnv, KEnv.insert, coreCacheKey]

theorem fullNoDeltaColdAcceptance (prims : Primitives .anon) :
    (RecM.whnfNoDelta betaSource).run betaHarnessMethods
        (fullCoreWarmState prims) =
          .ok betaArg (fullNoDeltaWarmState prims) ∧
      WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullCoreWarmState prims) ∧
      WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullNoDeltaWarmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  simpa [RecM.whnfNoDelta, whnfSemantics, fullNoDeltaWarmState] using
    (RecM.whnfNoDeltaImpl_fullMiss_acceptance
      (keys := whnfContextKeys) (fallback := CacheSemantics.blockErrorsOnly)
      structuralWhnfTheory (.direct RecM.WhnfDriverNonLeaf.app) rfl
      (coreCacheKey_eval (fullCoreWarmState prims))
      (betaTransientFalse (fullCoreWarmState prims))
      (fullCoreWarm_noDeltaMiss prims) (noDeltaTrace prims) rfl
      fullNoDeltaProvenance)

theorem fullNoDeltaWarmAcceptance (prims : Primitives .anon) :
    (RecM.whnfNoDelta betaSource).run betaHarnessMethods
        (fullNoDeltaWarmState prims) =
          .ok betaArg (fullNoDeltaWarmState prims) ∧
      WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullNoDeltaWarmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  simpa [RecM.whnfNoDelta, whnfSemantics] using
    (RecM.whnfNoDeltaImpl_fullHit_acceptance
      (keys := whnfContextKeys) (fallback := CacheSemantics.blockErrorsOnly)
      (.direct RecM.WhnfDriverNonLeaf.app) rfl
      (coreCacheKey_eval (fullNoDeltaWarmState prims))
      (betaTransientFalse (fullNoDeltaWarmState prims))
      (fullNoDeltaWarm_hit prims) (fullNoDeltaWarmStateInv prims) (.inl rfl)
      (coreCacheKey_matches (fullNoDeltaWarmState prims)
        (fullNoDeltaWarmStateInv prims).2.1))

theorem noDeltaCachePolicyIsolation (prims : Primitives .anon) :
    (fullNoDeltaWarmState prims).env.whnfNoDeltaCache[coreCacheKey]? =
        some betaArg ∧
      (fullNoDeltaWarmState prims).env.whnfNoDeltaCheapCache[coreCacheKey]? =
        none :=
  ⟨fullNoDeltaWarm_hit prims, fullNoDeltaWarm_cheapMiss prims⟩

/-! #### Full-WHNF loop, outer cache, and fuel witness -/

/-- The exact state after a genuine outer full-WHNF cache miss has paid its
single recursive-fuel charge. -/
def fullWhnfChargedState (prims : Primitives .anon) : TcState .anon :=
  let s := fullNoDeltaWarmState prims
  {s with recFuel := s.recFuel - 1}

theorem fullWhnfChargedStateInv (prims : Primitives .anon) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
      coreCacheSupport 0 [] (fullWhnfChargedState prims) := by
  exact WhnfStateInv.of_semantic_fields_eq
    (fullNoDeltaWarmStateInv prims) rfl rfl rfl rfl rfl rfl

theorem fullWhnfPrefixCold (prims : Primitives .anon) :
    (RecM.whnfWithNatSuccModePrefix betaSource).run betaHarnessMethods
      (fullNoDeltaWarmState prims) =
      .ok () (fullNoDeltaWarmState prims) := by
  exact RecM.whnfWithNatSuccModePrefix_disabled rfl rfl

theorem fullWhnfMissCharge (prims : Primitives .anon) :
    (RecM.whnfWithNatSuccModeMissCharge : RecM .anon Unit).run
      betaHarnessMethods (fullNoDeltaWarmState prims) =
      .ok () (fullWhnfChargedState prims) := by
  exact RecM.whnfWithNatSuccModeMissCharge_disabled rfl rfl

/-- Fuel bookkeeping does not disturb the already populated no-delta cache. -/
theorem fullWhnfCharged_noDeltaHit (prims : Primitives .anon) :
    (RecM.whnfNoDeltaImpl betaSource .FULL .collapse).run
      betaHarnessMethods (fullWhnfChargedState prims) =
      .ok betaArg (fullWhnfChargedState prims) := by
  rw [(RecM.WhnfDriverEntry.direct
    (methods := betaHarnessMethods) (source := betaSource)
    (s := fullWhnfChargedState prims)
    RecM.WhnfDriverNonLeaf.app).noDelta_eval .FULL .collapse]
  apply RecM.whnfNoDeltaImplNonLeaf_fullHit rfl
    (coreCacheKey_eval (fullWhnfChargedState prims))
    (betaTransientFalse (fullWhnfChargedState prims))
  simp [fullWhnfChargedState, fullNoDeltaWarmState, coreCacheKey]

theorem betaFullChargedNatNone (prims : Primitives .anon) :
    (RecM.tryReduceNatWithSuccMode betaArg .collapse).run betaHarnessMethods
      (fullWhnfChargedState prims) =
      .ok none (fullWhnfChargedState prims) := by
  unfold RecM.tryReduceNatWithSuccMode betaArg
  rw [KExpr.mkConst_shape]
  simp [KExpr.collectSpine, KExpr.collectSpine.go, RecM.prims]
  rfl

theorem betaFullChargedStringNone (prims : Primitives .anon) :
    (RecM.tryReduceString betaArg).run betaHarnessMethods
      (fullWhnfChargedState prims) =
      .ok none (fullWhnfChargedState prims) := by
  unfold RecM.tryReduceString betaArg
  rw [KExpr.mkConst_shape]
  rfl

/-- `betaArg` is a bare constant: the offset-stuck probe either rejects its
head outright or the collected spine has no arguments — `none` either way,
for any primitive address assignment. -/
theorem betaFullChargedNatOffsetStuckNone (prims : Primitives .anon) :
    (RecM.tryNatOffsetStuck betaArg).run betaHarnessMethods
      (fullWhnfChargedState prims) =
      .ok none (fullWhnfChargedState prims) := by
  unfold RecM.tryNatOffsetStuck
  rw [ReaderT.run_bind]
  change EStateM.bind ((RecM.prims).run betaHarnessMethods) _
    (fullWhnfChargedState prims) = _
  unfold EStateM.bind
  rw [show (RecM.prims (m := .anon)).run betaHarnessMethods
    (fullWhnfChargedState prims) =
      .ok prims (fullWhnfChargedState prims) from rfl]
  simp only
  cases hprobe : RecM.natOffsetStuckHead prims betaArg with
  | false => rfl
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    unfold betaArg
    rw [KExpr.mkConst_shape]
    simp [KExpr.collectSpine, KExpr.collectSpine.go]
    rfl

theorem betaFullChargedGetZero (prims : Primitives .anon) :
    TcM.tryGetConst zeroId (fullWhnfChargedState prims) =
      .ok (some zeroConcrete) (fullWhnfChargedState prims) := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _
    (fullWhnfChargedState prims) = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon))
    (fullWhnfChargedState prims) =
      .ok (fullWhnfChargedState prims) (fullWhnfChargedState prims) from rfl]
  simp only
  have henv : (fullWhnfChargedState prims).env.get? zeroId =
      some zeroConcrete := by
    simpa [fullWhnfChargedState, fullNoDeltaWarmState, fullCoreWarmState,
      noAccelState, state] using loadedEnv_zero_k1e
  rw [henv]
  rfl

theorem betaFullChargedTryDeltaNone (prims : Primitives .anon) :
    (RecM.tryDeltaUnfold betaArg).run betaHarnessMethods
      (fullWhnfChargedState prims) =
      .ok none (fullWhnfChargedState prims) := by
  unfold RecM.tryDeltaUnfold betaArg
  rw [KExpr.mkConst_shape]
  simp only [KExpr.collectSpine, KExpr.collectSpine.go]
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.tryGetConst zeroId) _
    (fullWhnfChargedState prims) = _
  unfold EStateM.bind
  rw [betaFullChargedGetZero prims]
  rfl

theorem betaFullChargedDeltaNone (prims : Primitives .anon) :
    (RecM.deltaUnfoldOne betaArg).run betaHarnessMethods
      (fullWhnfChargedState prims) =
      .ok none (fullWhnfChargedState prims) := by
  unfold RecM.deltaUnfoldOne
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.tryDeltaUnfold betaArg).run betaHarnessMethods) _
      (fullWhnfChargedState prims) = _
  unfold EStateM.bind
  rw [betaFullChargedTryDeltaNone prims]
  unfold betaArg
  rw [KExpr.mkConst_shape]
  change EStateM.bind (TcM.tryGetConst zeroId) _
    (fullWhnfChargedState prims) = _
  unfold EStateM.bind
  rw [betaFullChargedGetZero prims]
  rfl

/-- One full-WHNF iteration first consumes the certified no-delta hit, proves
the fresh cycle set cannot stop it, and then checks native, bitvector, Nat,
Decidable, String, offset-stuck, and delta reducers in their production
order. -/
theorem betaFullWhnfStep (prims : Primitives .anon) :
    (RecM.whnfWithNatSuccModeStep .collapse (betaSource, {})).run
      betaHarnessMethods (fullWhnfChargedState prims) =
      .ok (.done betaArg) (fullWhnfChargedState prims) := by
  unfold RecM.whnfWithNatSuccModeStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.whnfNoDeltaImpl betaSource .FULL .collapse).run
      betaHarnessMethods) _ (fullWhnfChargedState prims) = _
  unfold EStateM.bind
  rw [fullWhnfCharged_noDeltaHit prims]
  simp only
  have hcycle : ({} : Std.HashSet Address).contains betaArg.addr = false := by
    change ({} : Std.HashMap Address Unit).contains betaArg.addr = false
    exact Std.HashMap.contains_empty
  simp only [hcycle, Bool.false_eq_true, if_false, pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.tryReduceNative betaArg).run betaHarnessMethods) _
      (fullWhnfChargedState prims) = _
  unfold EStateM.bind
  rw [RecM.tryReduceNative_noAccel rfl]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.tryReduceBitvec betaArg).run betaHarnessMethods) _
      (fullWhnfChargedState prims) = _
  unfold EStateM.bind
  rw [RecM.tryReduceBitvec_noAccel rfl]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.tryReduceNatWithSuccMode betaArg .collapse).run
      betaHarnessMethods) _ (fullWhnfChargedState prims) = _
  unfold EStateM.bind
  rw [betaFullChargedNatNone prims]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.tryReduceDecidable betaArg).run betaHarnessMethods) _
      (fullWhnfChargedState prims) = _
  unfold EStateM.bind
  rw [RecM.tryReduceDecidable_noAccel rfl]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.tryReduceString betaArg).run betaHarnessMethods) _
      (fullWhnfChargedState prims) = _
  unfold EStateM.bind
  rw [betaFullChargedStringNone prims]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.tryNatOffsetStuck betaArg).run betaHarnessMethods) _
      (fullWhnfChargedState prims) = _
  unfold EStateM.bind
  rw [betaFullChargedNatOffsetStuckNone prims]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.deltaUnfoldOne betaArg).run betaHarnessMethods) _
      (fullWhnfChargedState prims) = _
  unfold EStateM.bind
  rw [betaFullChargedDeltaNone prims]
  rfl

theorem fullWhnfTrace (prims : Primitives .anon) :
    RecM.WhnfFullTrace .noAccel whnfSemantics RawProjRel.none worldGood
      coreCacheSupport 0 [] betaHarnessMethods .collapse
      maxWhnfFuel.toNat (betaSource, {}) (fullWhnfChargedState prims)
      betaArg (fullWhnfChargedState prims) := by
  rw [show maxWhnfFuel.toNat = 10000 by rfl]
  exact .done (fullWhnfChargedStateInv prims) (betaFullWhnfStep prims)
    (fullWhnfChargedStateInv prims) betaResultMeaning

/-- The exact state after the full driver commits its semantic cache entry. -/
def fullWhnfWarmState (prims : Primitives .anon) : TcState .anon :=
  let s := fullWhnfChargedState prims
  {s with env := {s.env with
    whnfCache := s.env.whnfCache.insert coreCacheKey betaArg}}

theorem fullWhnfWarmStateInv (prims : Primitives .anon) :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
      coreCacheSupport 0 [] (fullWhnfWarmState prims) := by
  exact RecM.WhnfDriverCacheUpdate.full_whnfStateInv
    (fullWhnfChargedStateInv prims) fullWhnfProvenance

theorem fullWhnfCold_miss (prims : Primitives .anon) :
    (fullNoDeltaWarmState prims).env.whnfCache[coreCacheKey]? = none := by
  simp [fullNoDeltaWarmState, fullCoreWarmState, noAccelState, state,
    loadedEnv, KEnv.insert, coreCacheKey]

theorem fullWhnfWarm_hit (prims : Primitives .anon) :
    (fullWhnfWarmState prims).env.whnfCache[coreCacheKey]? =
      some betaArg := by
  simp [fullWhnfWarmState, coreCacheKey]

theorem fullWhnfPrefixWarm (prims : Primitives .anon) :
    (RecM.whnfWithNatSuccModePrefix betaSource).run betaHarnessMethods
      (fullWhnfWarmState prims) = .ok () (fullWhnfWarmState prims) := by
  exact RecM.whnfWithNatSuccModePrefix_disabled rfl rfl

/-- A cold public full-WHNF call pays one miss charge, executes its bounded
semantic trace, inserts the result, and preserves the complete invariant. -/
theorem fullWhnfColdAcceptance (prims : Primitives .anon) :
    (RecM.whnf betaSource).run betaHarnessMethods
        (fullNoDeltaWarmState prims) =
          .ok betaArg (fullWhnfWarmState prims) ∧
      WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullWhnfChargedState prims) ∧
      WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullWhnfWarmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  simpa [RecM.whnf, whnfSemantics, fullWhnfWarmState] using
    (RecM.whnfWithNatSuccMode_miss_acceptance
      (keys := whnfContextKeys) (fallback := CacheSemantics.blockErrorsOnly)
      structuralWhnfTheory (.direct RecM.WhnfDriverNonLeaf.app)
      (fullWhnfPrefixCold prims)
      (coreCacheKey_eval (fullNoDeltaWarmState prims))
      (betaTransientFalse (fullNoDeltaWarmState prims))
      (fullWhnfCold_miss prims) (fullWhnfMissCharge prims)
      (fullWhnfTrace prims) rfl fullWhnfProvenance)

/-- The next public call consumes the inserted entry as a semantic hit and
does not pay another fuel charge or mutate any checker state. -/
theorem fullWhnfWarmAcceptance (prims : Primitives .anon) :
    (RecM.whnf betaSource).run betaHarnessMethods
        (fullWhnfWarmState prims) =
          .ok betaArg (fullWhnfWarmState prims) ∧
      WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullWhnfWarmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  simpa [RecM.whnf, whnfSemantics] using
    (RecM.whnfWithNatSuccMode_hit_acceptance
      (keys := whnfContextKeys) (fallback := CacheSemantics.blockErrorsOnly)
      (.direct RecM.WhnfDriverNonLeaf.app) (fullWhnfPrefixWarm prims)
      (coreCacheKey_eval (fullWhnfWarmState prims))
      (betaTransientFalse (fullWhnfWarmState prims))
      (fullWhnfWarm_hit prims) (fullWhnfWarmStateInv prims) (.inl rfl)
      (coreCacheKey_matches (fullWhnfWarmState prims)
        (fullWhnfWarmStateInv prims).2.1))

/-- The cold outer miss consumes exactly one unit; cache insertion and the
subsequent warm hit consume none. -/
theorem fullWhnfFuelDiscipline (prims : Primitives .anon) :
    (fullNoDeltaWarmState prims).recFuel = maxRecFuel ∧
      (fullWhnfChargedState prims).recFuel = maxRecFuel - 1 ∧
      (fullWhnfWarmState prims).recFuel = maxRecFuel - 1 := by
  simp [fullWhnfWarmState, fullWhnfChargedState, fullNoDeltaWarmState,
    fullCoreWarmState, noAccelState, state]

/-- The final state retains all three independently certified cache layers:
structural core, no-delta, and full WHNF. -/
theorem fullWhnfCacheLayering (prims : Primitives .anon) :
    (fullWhnfWarmState prims).env.whnfCache[coreCacheKey]? = some betaArg ∧
      (fullWhnfWarmState prims).env.whnfNoDeltaCache[coreCacheKey]? =
        some betaArg ∧
      (fullWhnfWarmState prims).env.whnfCoreCache[coreCacheKey]? =
        some betaArg := by
  constructor
  · exact fullWhnfWarm_hit prims
  constructor <;> simp [fullWhnfWarmState, fullWhnfChargedState,
    fullNoDeltaWarmState, fullCoreWarmState, coreCacheKey]

/-- G2a acceptance witness: one concrete state simultaneously contains a
trusted, well-formed ambient Nat family; a successfully promoted standalone
declaration that uses Nat; and an independently loaded pending declaration
for which declaration WF is impossible. -/
theorem acceptance (prims : Primitives .anon) :
    TcInv RawProjRel.none worldGood (state prims) ∧
    worldGood.trusted natId ∧
    worldGood.trusted zeroId ∧
    worldGood.trusted succId ∧
    TrustedDecl RawProjRel.none worldGood goodId goodDecl ∧
    PendingDecl RawProjRel.none worldGood IllTypedPending.targetId
      IllTypedPending.theoryDecl ∧
    ¬∃ env', VDecl.WF worldGood.venv IllTypedPending.theoryDecl env' :=
  ⟨(stateWF prims).tcInv, nat_trusted_good, zero_trusted_good,
    succ_trusted_good, goodTrustedDecl, badPending, badDecl_not_wf⟩

end AmbientNat

end Ix.Tc
