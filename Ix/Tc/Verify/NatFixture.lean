import Ix.Tc.Verify.Run
import Ix.Tc.Verify.Whnf
import Ix.Tc.Verify.Whnf.Structural.BetaBoundary

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

/-- Deliberately untrusted recursor-shaped catalog entry used by the projection/iota branch
adversarial execution fixture.  Its rule is operationally consumable, but it
has no `nameOf` entry and is never added to the trusted log. -/
def iotaResult : KExpr .anon := .const zeroId #[] (info iotaAddress)

def iotaRule : RecRule .anon :=
  { ctor := (), fields := 0, rhs := iotaResult }

def iotaConcrete : KConst .anon :=
  .recr () () false false 0 0 0 0 0 natId 0 natRef #[iotaRule] ()

def iotaInfo : IotaInfo .anon :=
  { k := false, params := 0, motives := 0, minors := 0, indices := 0,
    majorIdx := 0, rules := #[iotaRule], lvls := 0 }

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
  structEtas := fun _ => False

def natEnv₂ : VEnv where
  constants := fun name =>
    if zeroName = name then some zeroConstant else natEnv₁.constants name
  defeqs := fun _ => False
  structEtas := fun _ => False

def natEnv : VEnv where
  constants := fun name =>
    if succName = name then some succConstant else natEnv₂.constants name
  defeqs := fun _ => False
  structEtas := fun _ => False

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
no recursor declaration, so `recursorFacts` and `recursorPatterns` are
vacuous; any later block that contains a `.recr` entry must supply both its
Theory equation and exact iota-pattern witnesses explicitly. -/
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
  recursorPatterns := by
    intro id c ruleIndex rule hmember hcatalog hrule
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
  blocks := BlockCatalog.empty
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
  structEtas := natEnv.structEtas

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
  exact ⟨rfl, rfl, rfl, TrustInsert.old, VEnv.addConst_le addGood⟩

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
    simpa [natConcrete, KConst.lvls] using hresolved.uvars.symm
  have htr0 := hresolved.trKExprS_const
    (ctx := []) (us := #[]) (info := supportExpr.info)
    (by simp) (by rfl)
  have htr :
      TrKExprS worldNat.venv 0 worldNat.nameOf RawProjRel.none []
        supportExpr (.const name []) := by
    simpa [supportExpr, ← KExpr.mkConst_shape, huvars] using htr0
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
  · intro source hsource haddr Δ hctx _hscoped
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
  · rfl
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

/-- The concrete ambient-Nat state inhabits the syntax-directed K1 fixture
layer with acceleration disabled. Its primitive table remains intentionally
parametric; production closure uses `productionNoAccelStateInv` below. -/
theorem noAccelStateInv (prims : Primitives .anon) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood support
      0 [] (noAccelState prims) := by
  refine ⟨?_, ?_, rfl⟩
  · have h := freshKernelStateWF prims
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact h.core.of_env_eq rfl
    · simpa [noAccelState] using h.internSupport
    · simpa [noAccelState] using h.caches
    · simpa [noAccelState] using h.equivalences
  · apply CtxRecon.empty <;> rfl

/-- WHNF layer policy retains the old primitive reduction witness only in the explicitly structural layer:
two arbitrary primitive tables leave every semantic/cache/context field
identical. This layer may test syntax-directed branches but cannot close the
production reducer oracle. -/
theorem structuralInvariant_does_not_bind_primitives
    (left right : Primitives .anon) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood support
        0 [] (noAccelState left) ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood support
        0 [] (noAccelState right) ∧
      (noAccelState left).env = (noAccelState right).env ∧
      (noAccelState left).ctx = (noAccelState right).ctx ∧
      (noAccelState left).letVals = (noAccelState right).letVals ∧
      (noAccelState left).lctx = (noAccelState right).lctx ∧
      (noAccelState left).prims = left ∧
      (noAccelState right).prims = right := by
  exact ⟨noAccelStateInv left, noAccelStateInv right,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The real no-acceleration layer is inhabited by the production anon table.
This is the state-level primitive ingress fact used by subsequent active
reducer proofs. -/
theorem productionNoAccelStateInv :
    WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood support
      0 [] (noAccelState Primitives.ofAnonAddrs) := by
  have h := noAccelStateInv Primitives.ofAnonAddrs
  exact ⟨h.1, h.2.1, rfl, Primitives.ofAnonAddrs_canonical⟩

/-- Any non-production primitive table is rejected by the production layer,
even though the weaker structural fixture invariant still accepts it. -/
theorem noAccelInvariant_rejects_mismatched_primitives
    (prims : Primitives .anon)
    (hne : ¬prims.CanonicalAnon) :
    ¬WhnfStateInv .noAccel whnfSemantics RawProjRel.none worldGood support
      0 [] (noAccelState prims) := by
  intro h
  exact hne h.noAccel_primitives

/-- A real Nat-containing state instantiates the first conditional
`RecM.whnf` theorem.  This branch returns before any cache, fuel, native, or
recursive-method operation, but still preserves the complete K1 invariant on
both EStateM outcomes. -/
theorem whnfLeaf_noAccel_wf (prims : Primitives .anon) :
    RecM.WF .structuralNoAccel whnfSemantics RawProjRel.none worldGood support 0 []
      (noAccelState prims) (RecM.whnf whnfLeafExpr)
      (fun result _ => WhnfPost RawProjRel.none worldGood 0 []
        (.sort .zero) result) :=
  RecM.whnf_leaf_wf .sort whnfLeafTranslates whnfLeafTheoryWF

/-- Non-vacuity package for the first no-acceleration algorithmic slice. -/
theorem whnfLeaf_noAccel_acceptance (prims : Primitives .anon) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood support
        0 [] (noAccelState prims) ∧
      RecM.WF .structuralNoAccel whnfSemantics RawProjRel.none worldGood support 0 []
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
  refine ⟨warmCoreWF prims, ?_, warmCache_worldTransport, ?_⟩
  · simpa [warmState, warmEnv, state] using (checkSupport prims).initial
  · exact EquivManager.WF.empty

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

theorem warmStateInvAccelerated :
    WhnfStateInv .accelerated whnfSemantics RawProjRel.none worldGood support
      0 [] (warmState Primitives.ofAnonAddrs) := by
  exact ⟨warmKernelStateWF _, (warmKey_matches _).1,
    Primitives.ofAnonAddrs_canonical⟩

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
      CtxRecon worldGood.venv whnfContextKeys.uvars worldGood.nameOf
          RawProjRel.none (warmState prims) [] →
      TcM.whnfKey supportExpr (warmState prims) = .ok key s' →
      whnfContextKeys.Represents supportExpr.lbr key.2 [] := by
    intro key s' _ hrun
    have hexact := TcM.whnfKey_closed
      (s := warmState prims) supportExpr_lbr
    rw [hexact] at hrun
    cases hrun
    simp [whnfContextKeys]
  simpa [whnfContextKeys, WhnfContextKeys.closed] using
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
      (by simp [KExpr.ContextScoped, KExpr.VarsScoped, supportExpr])

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
    RecM.WF .structuralNoAccel whnfSemantics RawProjRel.none worldGood support 0 []
      (noAccelState prims) (RecM.whnfCoreWithFlags supportExpr flags)
      (fun result _ => WhnfPost RawProjRel.none worldGood 0 []
        (.const natName []) result) :=
  RecM.whnfCoreWithFlags_leaf_wf .const betaTy_tr betaTy_wf

theorem whnfCoreConst_noAccel_acceptance (prims : Primitives .anon)
    (flags : WhnfFlags) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood support
        0 [] (noAccelState prims) ∧
      RecM.WF .structuralNoAccel whnfSemantics RawProjRel.none worldGood support 0 []
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

/-- The concrete identity body has coherent variable metadata. -/
theorem betaBody_constructed : KExpr.Constructed betaBody := by
  unfold betaBody
  exact .var (by decide)

/-- The concrete beta argument is smart-constructor coherent, which makes
lifting it by zero syntactically exact. -/
theorem betaArg_constructed : KExpr.Constructed betaArg := by
  unfold betaArg
  exact .const

/-- Substitution's operational seam is inhabited by the ambient Nat identity redex:
the production transient helper returns the verified substitution spec and
leaves the complete typechecker state untouched. -/
theorem betaIotaArgRun (methods : Methods .anon) (s : TcState .anon) :
    (RecM.applyIotaArg betaLam betaArg true).run methods s =
      .ok (KExpr.substSpec betaBody betaArg 0) s := by
  unfold betaLam
  rw [KExpr.mkLam_shape]
  exact RecM.applyIotaArg_true_lam_run methods s _ _ _ _ _ _
    betaBody_constructed betaArg_constructed (by decide)

/-- The exact non-interning term returned by that production branch carries
the same Theory beta meaning as the verified pure substitution result. -/
theorem betaNoInternMeaning :
    WhnfMeaning RawProjRel.none worldGood 0 [] betaSource
      (substNoIntern betaBody betaArg 0) := by
  unfold betaSource betaLam
  rw [KExpr.mkApp_shape, KExpr.mkLam_shape]
  exact WhnfMeaning.betaNoIntern (RawProjRel.none_ok worldGood.venv 0)
    betaTy_tr betaBody_tr betaArg_tr betaA_type betaBody_type betaArg_type
    betaBody_constructed betaArg_constructed (by decide)

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

/-- interning frame acceptance package: the concrete production execution preserves the
inhabited no-acceleration invariant, and its exact syntactic result has the
Theory beta meaning proved above. -/
theorem betaCoreUncached_acceptance (prims : Primitives .anon)
    (flags : WhnfFlags) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood support
        0 [] (noAccelState prims) ∧
      (RecM.whnfCoreWithFlagsUncached betaSource flags).run
        betaHarnessMethods (noAccelState prims) =
          .ok betaArg (noAccelState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg :=
  ⟨noAccelStateInv prims, betaCoreUncached_eval prims flags,
    betaResultMeaning⟩

/-! ### zeta reduction legacy de-Bruijn zeta witness -/

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
  simpa [state, bvarZetaState, noAccelState] using hrec

theorem bvarZetaStateInv (prims : Primitives .anon) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood support
      0 bvarZetaCtx (bvarZetaState prims) := by
  have hbase := noAccelStateInv prims
  exact ⟨⟨hbase.1.core.of_env_eq rfl,
      hbase.1.internSupport, hbase.1.caches, hbase.1.equivalences⟩,
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
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood support
        0 bvarZetaCtx (bvarZetaState prims) ∧
      (RecM.whnfCoreWithFlagsUncached betaBody flags).run betaHarnessMethods
        (bvarZetaState prims) = .ok betaArg (bvarZetaState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 bvarZetaCtx betaBody betaArg :=
  ⟨bvarZetaStateInv prims, bvarZetaCoreUncachedEval prims flags,
    bvarZetaMeaning prims⟩

/-! ### zeta reduction let-bound fvar zeta witness -/

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
    simpa [state, fvarZetaState, noAccelState, LocalContext.push] using hrec
  · apply LocalContext.WF.push .empty
    simp [fvarZetaId]
  · intro p hp
    simp [fvarZetaState, noAccelState, state, LocalContext.push] at hp
    subst p
    simp [fvarZetaState, fvarZetaId]

theorem fvarZetaStateInv (prims : Primitives .anon) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood support
      0 fvarZetaCtx (fvarZetaState prims) := by
  have hbase := noAccelStateInv prims
  refine ⟨?_, fvarZetaCtxRecon prims, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hbase.1.core.of_consts_eq (by rfl) (by
      simpa [fvarZetaState] using hbase.1.core.intern)
  · simpa [fvarZetaState] using hbase.1.internSupport
  · intro entry hentry
    apply hbase.1.caches
    cases hentry <;> (constructor; assumption)
  · simpa [fvarZetaState] using hbase.1.equivalences

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
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood support
        0 fvarZetaCtx (fvarZetaState prims) ∧
      (RecM.whnfCoreWithFlagsUncached fvarZetaSource flags).run
        betaHarnessMethods (fvarZetaState prims) =
          .ok betaArg (fvarZetaState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 fvarZetaCtx
        fvarZetaSource betaArg :=
  ⟨fvarZetaStateInv prims, fvarZetaCoreUncachedEval prims flags,
    fvarZetaMeaning prims⟩

/-! ### projection/iota branch adversarial projection witness -/

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
  rw [RecM.tryProjReduce_eq, RecM.tryProjPrepare_eq]
  unfold projectionValue
  rw [KExpr.mkApp_shape, KExpr.mkConst_shape]
  rw [ReaderT.run_bind]
  unfold RecM.tryProjReduceTail
  simp only
  rw [ReaderT.run_pure, pure_bind, ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run
      (RecM.tryReduceFinValDecidableRec natId 0
        (.const succId #[] (KExpr.mkConst succId #[] ()).info) #[betaArg])
        betaHarnessMethods) _
      (noAccelState prims) = _
  unfold EStateM.bind
  rw [RecM.tryReduceFinValDecidableRec_noAccel rfl]
  simp only
  simp only [KExpr.collectSpine, KExpr.collectSpine.go]
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
`WhnfMeaning`; the generic projection/iota branch theorem's source-translation premise is
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
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood support
        0 [] (noAccelState prims) ∧
      (RecM.whnfCoreWithFlagsUncached projectionSource flags).run
        betaHarnessMethods (noAccelState prims) =
          .ok betaArg (noAccelState prims) ∧
      ¬∃ sourceV,
        TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
          projectionSource sourceV :=
  ⟨noAccelStateInv prims, projectionCoreEval prims flags,
    projectionSource_not_translated⟩

/-! ### projection/iota branch adversarial iota witness -/

def iotaPrims (prims : Primitives .anon) : Primitives .anon :=
  { prims with natZero := zeroId }

def iotaState (prims : Primitives .anon) : TcState .anon :=
  let base := noAccelState (iotaPrims prims)
  { base with env := base.env.insert iotaId iotaConcrete }

def iotaHead : KExpr .anon := KExpr.mkConst iotaId #[] ()
def iotaSource : KExpr .anon := KExpr.mkApp iotaHead iotaResult

/-! NatLiteral runs the same deliberately untrusted operational recursor with a
literal major.  The expanded zero constructor has production-computed
metadata, so it is kept distinct from the rule's adversarial RHS above. -/
def iotaNatZero : KExpr .anon := RecM.natExprFromValue 0
def iotaNatCtor : KExpr .anon := KExpr.mkConst zeroId #[]
def iotaNatSource : KExpr .anon := KExpr.mkApp iotaHead iotaNatZero

theorem iotaStateInv (prims : Primitives .anon) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood support
      0 [] (iotaState prims) := by
  have hbase := noAccelStateInv (iotaPrims prims)
  refine ⟨?_, ?_, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have hcat : worldGood.catalog iotaId = some iotaConcrete := by
        exact catalog_iota
      simpa [iotaState] using hbase.1.core.load hcat
    · simpa [iotaState, KEnv.insert] using hbase.1.internSupport
    · intro entry hentry
      apply hbase.1.caches
      cases hentry <;> (constructor; assumption)
    · simpa [iotaState] using hbase.1.equivalences
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
    · simpa [KEnv.get?, noAccelState, state] using loadedEnv_zero_k1e
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
    rw [show (256 - 0 : Nat) = Nat.succ 255 from rfl]
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

theorem iotaApplyRule (prims : Primitives .anon) :
    (RecM.applyIotaRule iotaRule #[] iotaInfo #[iotaResult] #[] 0 false).run
        betaHarnessMethods (iotaState prims) =
      .ok iotaResult (iotaState prims) := by
  unfold RecM.applyIotaRule
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.instantiateUnivParams iotaRule.rhs #[]) _
    (iotaState prims) = _
  unfold EStateM.bind
  rw [iotaInstantiateRule]
  rfl

theorem iotaApplyCtor (prims : Primitives .anon) :
    (RecM.tryApplyIotaCtor iotaInfo #[] #[iotaResult] #[] 0 0 false).run
        betaHarnessMethods (iotaState prims) =
      .ok (some iotaResult) (iotaState prims) := by
  exact (RecM.TryApplyIotaCtorSuccessTrace.mk rfl rfl (by decide)
    (iotaApplyRule prims)).eval

theorem iotaCleanupOfNatValue (prims : Primitives .anon)
    (e : KExpr .anon) (value : Nat)
    (hextract : extractNatValue e (iotaPrims prims) = some value) :
    (RecM.cleanupNatOffsetMajor e).run betaHarnessMethods
      (iotaState prims) = .ok none (iotaState prims) := by
  have heval :
      (RecM.evalNatOffsetLiteral e 0).run betaHarnessMethods
        (iotaState prims) = .ok (some value) (iotaState prims) := by
    unfold RecM.evalNatOffsetLiteral RecM.evalNatOffsetLiteralFuel
    rw [show (256 - 0 : Nat) = Nat.succ 255 from rfl]
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
    (ReaderT.run (RecM.evalNatOffsetLiteral e 0) betaHarnessMethods) _
      (iotaState prims) = _
  unfold EStateM.bind
  rw [heval]
  rfl

theorem iotaNatCleanup (prims : Primitives .anon) :
    (RecM.cleanupNatOffsetMajor iotaNatZero).run betaHarnessMethods
      (iotaState prims) = .ok none (iotaState prims) := by
  apply iotaCleanupOfNatValue prims iotaNatZero 0
  unfold iotaNatZero RecM.natExprFromValue extractNatValue extractNatLit
  rw [KExpr.mkNat_shape]

theorem iotaNatCtorCleanup (prims : Primitives .anon) :
    (RecM.cleanupNatOffsetMajor iotaNatCtor).run betaHarnessMethods
      (iotaState prims) = .ok none (iotaState prims) := by
  apply iotaCleanupOfNatValue prims iotaNatCtor 0
  unfold iotaNatCtor extractNatValue extractNatLit
  rw [KExpr.mkConst_shape]
  simp [iotaPrims]

theorem iotaNatMajorWhnf (prims : Primitives .anon) (flags : WhnfFlags) :
    (if flags.cheapRec then
        (RecM.whnfCoreFlagsRec iotaNatZero flags).run betaHarnessMethods
          (iotaState prims)
      else (RecM.whnfRec iotaNatZero).run betaHarnessMethods
          (iotaState prims)) = .ok iotaNatZero (iotaState prims) := by
  cases flags.cheapRec <;>
    simp [RecM.whnfCoreFlagsRec, RecM.whnfRec, betaHarnessMethods] <;> rfl

theorem iotaNatZeroExpand (prims : Primitives .anon) :
    (RecM.natToConstructor 0).run betaHarnessMethods (iotaState prims) =
      .ok iotaNatCtor (iotaState prims) := by
  simpa [iotaNatCtor, iotaState, iotaPrims, noAccelState, state] using
    (RecM.natToConstructor_zero betaHarnessMethods (iotaState prims))

theorem iotaNatSuccExpand (prims : Primitives .anon) (predecessor : Nat) :
    (RecM.natToConstructor (predecessor + 1)).run betaHarnessMethods
      (iotaState prims) =
      .ok (KExpr.mkApp (KExpr.mkConst prims.natSucc #[])
        (RecM.natExprFromValue predecessor)) (iotaState prims) := by
  simpa [iotaState, iotaPrims, noAccelState, state] using
    (RecM.natToConstructor_succ betaHarnessMethods (iotaState prims)
      predecessor)

theorem iotaNatApplyRule (prims : Primitives .anon) :
    (RecM.applyIotaRule iotaRule #[] iotaInfo #[iotaNatZero] #[] 0 true).run
        betaHarnessMethods (iotaState prims) =
      .ok iotaResult (iotaState prims) := by
  unfold RecM.applyIotaRule
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.instantiateUnivParams iotaRule.rhs #[]) _
    (iotaState prims) = _
  unfold EStateM.bind
  rw [iotaInstantiateRule]
  rfl

theorem iotaNatApplyCtor (prims : Primitives .anon) :
    (RecM.tryApplyIotaCtor iotaInfo #[] #[iotaNatZero] #[] 0 0 true).run
        betaHarnessMethods (iotaState prims) =
      .ok (some iotaResult) (iotaState prims) := by
  exact (RecM.TryApplyIotaCtorSuccessTrace.mk rfl rfl (by decide)
    (iotaNatApplyRule prims)).eval

/-- Inhabited NatLiteral path: a literal zero survives the major callback, expands
to the active `Nat.zero` constructor, and executes the selected rule with
transient application semantics. -/
theorem iotaNatTryEval (prims : Primitives .anon) (flags : WhnfFlags) :
    (RecM.tryIotaWithFlags iotaNatSource flags).run betaHarnessMethods
      (iotaState prims) = .ok (some iotaResult) (iotaState prims) := by
  apply RecM.tryIotaWithFlags_natCtor
    (recId := iotaId) (recUs := #[]) (spine := #[iotaNatZero])
    (recursor := iotaConcrete) (recr := iotaInfo)
    (major := iotaNatZero) (value := 0)
    (blob := KExpr.natBlob 0) (ctorMajor := iotaNatCtor)
    (ctorId := zeroId) (ctorUs := #[]) (ctorArgs := #[])
    (ctor := zeroConcrete) (cidx := 0) (ctorFields := 0)
  · unfold iotaNatSource iotaHead
    rw [KExpr.mkApp_shape, KExpr.mkConst_shape]
    rfl
  · exact iotaGetRec prims
  · rfl
  · decide
  · rfl
  · rfl
  · exact iotaNatCleanup prims
  · exact iotaNatMajorWhnf prims flags
  · exact iotaNatZeroExpand prims
  · unfold iotaNatCtor
    exact .const
  · exact iotaNatCtorCleanup prims
  · unfold iotaNatCtor
    rw [KExpr.mkConst_shape]
    rfl
  · exact iotaGetZero prims
  · rfl
  · exact iotaNatApplyCtor prims

theorem iotaNatStepEval (prims : Primitives .anon) (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep iotaNatSource flags).run betaHarnessMethods
      (iotaState prims) = .ok (.next iotaResult) (iotaState prims) := by
  unfold iotaNatSource iotaHead
  rw [KExpr.mkApp_shape, KExpr.mkConst_shape]
  apply RecM.whnfCoreWithFlagsStep_iota
    (recId := iotaId) (us := #[])
    (headInfo := (KExpr.mkConst iotaId #[] ()).info)
    (args := #[iotaNatZero])
  · simp [KExpr.collectSpine, KExpr.collectSpine.go]
  · rfl
  · change Bool.not ((KExpr.mkConst iotaId #[] ()).info.addr ==
        (KExpr.mkConst iotaId #[] ()).info.addr) = false
    rw [beq_self_eq_true]
    rfl
  · exact iotaNatTryEval prims flags

theorem iotaNatCoreEval (prims : Primitives .anon) (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsUncached iotaNatSource flags).run
      betaHarnessMethods (iotaState prims) =
        .ok iotaResult (iotaState prims) := by
  apply RecM.whnfCoreWithFlagsUncached_nextLeaf
  · exact iotaNatStepEval prims flags
  · exact .const

/-! ### StringLiteral inhabited empty-String preprocessing path -/

def iotaStringCtorAddress : Address := address 15
def iotaStringCtorId : KId .anon := ⟨iotaStringCtorAddress, ()⟩

/-- Operational constructor metadata for the generated `String.ofList` head.
The zero field count keeps this deliberately untrusted fixture focused on
String preprocessing; ordinary nonzero-field execution is inhabited by the
ConstructorDispatch multi-argument fixture. -/
def iotaStringCtorConcrete : KConst .anon :=
  .ctor () () false 0 natId 0 0 0 natRef

def iotaStringPrims : Primitives .anon :=
  { iotaPrims Primitives.ofAnonAddrs with stringOfList := iotaStringCtorId }

def iotaStringState : TcState .anon :=
  let base := iotaState iotaStringPrims
  { base with env := base.env.insert iotaStringCtorId iotaStringCtorConcrete }

def iotaStringMajor : KExpr .anon := KExpr.mkStrLit ""

def iotaStringNil : KExpr .anon :=
  KExpr.mkApp
    (KExpr.mkConst iotaStringPrims.listNil #[KUniv.mkZero])
    (KExpr.mkConst iotaStringPrims.charType #[])

def iotaStringCtor : KExpr .anon :=
  KExpr.mkApp (KExpr.mkConst iotaStringCtorId #[]) iotaStringNil

def iotaStringSource : KExpr .anon := KExpr.mkApp iotaHead iotaStringMajor

/-- The new production induction seam is inhabited at the empty character
list without touching state.  Fixed String setup/final interns remain an
explicit later helper-closure obligation. -/
theorem iotaStringEmptyFold (charOfNat cons : KExpr .anon) :
    (RecM.strLitListToConstructor charOfNat cons [] iotaStringNil).run
        betaHarnessMethods iotaStringState =
      .ok iotaStringNil iotaStringState :=
  RecM.strLitListToConstructor_empty _ _ _ _ _

/-- The post-WHNF fixture callback makes the generated String spine converge
to the already loaded zero constructor under either recursive policy.  The
fixture starts at `tryIotaAfterMajorWhnf`, so this does not interfere with an
earlier major callback. -/
def iotaStringHarnessMethods : Methods .anon where
  whnf := fun _ => pure iotaResult
  whnfCore := fun e => pure e
  whnfMode := fun e _ => pure e
  whnfCoreFlags := fun _ _ => pure iotaResult
  infer := fun e => pure e
  isDefEq := fun _ _ => pure false

theorem iotaStringExpand :
    ∃ strCtor s',
      (RecM.strLitToConstructor "").run iotaStringHarnessMethods
          iotaStringState =
          .ok strCtor s' ∧
        InternUpdateFrame iotaStringState s' :=
  RecM.strLitToConstructor_success_frame _ _ _

theorem iotaStringCallback (flags : WhnfFlags)
    (strCtor : KExpr .anon) (s : TcState .anon) :
    (if flags.cheapRec then
        (RecM.whnfCoreFlagsRec strCtor flags).run iotaStringHarnessMethods s
      else (RecM.whnfRec strCtor).run iotaStringHarnessMethods s) =
      .ok iotaResult s := by
  cases flags.cheapRec <;>
    simp [RecM.whnfCoreFlagsRec, RecM.whnfRec,
      iotaStringHarnessMethods] <;> rfl

theorem iotaStringCleanup :
    (RecM.cleanupNatOffsetMajor iotaStringMajor).run
      iotaStringHarnessMethods iotaStringState =
        .ok none iotaStringState := by
  unfold iotaStringMajor KExpr.mkStrLit
  rw [KExpr.mkStr_shape]
  exact RecM.cleanupNatOffsetMajor_str _ _ _ _ _

/-- String expansion may grow the intern table, but it cannot disturb the
constructor catalog used by the following ordinary-iota dispatch. -/
theorem iotaStringGetZeroOfFrame {s' : TcState .anon}
    (hframe : InternUpdateFrame iotaStringState s') :
    TcM.tryGetConst zeroId s' = .ok (some zeroConcrete) s' := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s' = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s' = .ok s' s' from rfl]
  simp only
  have hconsts : s'.env.consts = iotaStringState.env.consts := by
    simpa [InternUpdateFrame] using
      congrArg (fun st : TcState .anon => st.env.consts) hframe
  have hneString : iotaStringCtorId ≠ zeroId := by
    intro h
    exact address_ne (a := 15) (b := 11) (by decide)
      (congrArg KId.addr h)
  have hneIota : iotaId ≠ zeroId := by
    intro h
    exact address_ne (a := 14) (b := 11) (by decide)
      (congrArg KId.addr h)
  have hinitial : iotaStringState.env.get? zeroId = some zeroConcrete := by
    simp only [iotaStringState, KEnv.get?, KEnv.insert,
      Std.HashMap.getElem?_insert]
    split
    · next h => exact False.elim (hneString (eq_of_beq h))
    · simp only [iotaState, KEnv.insert]
      rw [Std.HashMap.getElem?_insert]
      split
      · next h => exact False.elim (hneIota (eq_of_beq h))
      · simpa [KEnv.get?, noAccelState, state] using loadedEnv_zero_k1e
  have hget : s'.env.get? zeroId = iotaStringState.env.get? zeroId := by
    unfold KEnv.get?
    rw [hconsts]
  rw [hget, hinitial]
  rfl

/-- The deliberately nullary fixture rule is state-preserving for every
post-expansion state; its right-hand side has no universes to instantiate. -/
theorem iotaStringApplyRule (s : TcState .anon) :
    (RecM.applyIotaRule iotaRule #[] iotaInfo #[iotaStringMajor] #[] 0 false).run
        iotaStringHarnessMethods s = .ok iotaResult s := by
  unfold RecM.applyIotaRule
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.instantiateUnivParams iotaRule.rhs #[]) _ s = _
  unfold EStateM.bind
  rw [show TcM.instantiateUnivParams iotaRule.rhs #[] s =
    .ok iotaResult s from rfl]
  rfl

theorem iotaStringApplyCtor (s : TcState .anon) :
    (RecM.tryApplyIotaCtor iotaInfo #[] #[iotaStringMajor] #[] 0 0 false).run
        iotaStringHarnessMethods s = .ok (some iotaResult) s := by
  exact (RecM.TryApplyIotaCtorSuccessTrace.mk rfl rfl (by decide)
    (iotaStringApplyRule s)).eval

/-- Inhabited StringLiteral post-WHNF path: the empty String is expanded through the
real intern-heavy helper, normalized under either callback policy, recognized
as the loaded zero constructor, and dispatched with `transient = false`. -/
theorem iotaStringAfterEval (flags : WhnfFlags) :
    ∃ s',
      (RecM.tryIotaAfterMajorWhnf flags iotaId iotaInfo #[]
        #[iotaStringMajor] iotaStringMajor).run iotaStringHarnessMethods
          iotaStringState = .ok (some iotaResult) s' := by
  obtain ⟨strCtor, sStr, hstr, hframe⟩ := iotaStringExpand
  have hlookup := iotaStringGetZeroOfFrame hframe
  have hdispatch :
      (RecM.tryIotaCtorOrStructEta iotaId iotaInfo #[]
        #[iotaStringMajor] iotaResult false).run iotaStringHarnessMethods sStr =
          .ok (some iotaResult) sStr := by
    apply RecM.tryIotaCtorOrStructEta_regular
      (ctorId := zeroId) (ctorUs := #[]) (ctorArgs := #[])
      (ctor := zeroConcrete) (cidx := 0) (ctorFields := 0)
    · unfold iotaResult
      rfl
    · exact hlookup
    · rfl
    · exact iotaStringApplyCtor sStr
  refine ⟨sStr, ?_⟩
  have hcleanup := iotaStringCleanup
  unfold iotaStringMajor KExpr.mkStrLit at hcleanup ⊢
  rw [KExpr.mkStr_shape] at hcleanup ⊢
  exact RecM.tryIotaAfterMajorWhnf_str
    (flags := flags) hcleanup hstr
      (iotaStringCallback flags strCtor sStr) hdispatch

/-! ### ConstructorSynthesis inhabited K-synthesis path -/

def kMajorAddress : Address := address 16
def kMajorId : KId .anon := ⟨kMajorAddress, ()⟩

def kMajor : KExpr .anon := KExpr.mkConst kMajorId #[]

def kMajorConcrete : KConst .anon :=
  .axio () () false 0 natRef

/-- A single major premise is enough for production's bounded inductive-head
scan because this K-like fixture has no parameters, motives, minors, or
indices before the major. -/
def kRecType : KExpr .anon :=
  .all () () natRef natRef (info kMajorAddress)

def kIotaConcrete : KConst .anon :=
  .recr () () true false 0 0 0 0 0 natId 0 kRecType #[iotaRule] ()

def kIotaInfo : IotaInfo .anon :=
  { k := true, params := 0, motives := 0, minors := 0, indices := 0,
    majorIdx := 0, rules := #[iotaRule], lvls := 0 }

def kIotaState : TcState .anon :=
  let base := noAccelState (iotaPrims Primitives.ofAnonAddrs)
  let withRec := { base with env := base.env.insert iotaId kIotaConcrete }
  { withRec with env := withRec.env.insert kMajorId kMajorConcrete }

def kIotaSource : KExpr .anon := KExpr.mkApp iotaHead kMajor
def kSynthCtor : KExpr .anon := KExpr.mkConst zeroId #[]

def kIotaAfterIntern : TcState .anon :=
  { kIotaState with env := { kIotaState.env with
      intern := (internExprM kSynthCtor kIotaState.env.intern).2 } }

/-- The harness models exactly the predecessor method-table facts consumed by
K synthesis: both the arbitrary major and the generated nullary constructor
have type `Nat`, WHNF is already reached, and their types are definitionally
equal. -/
def kIotaHarnessMethods : Methods .anon where
  whnf := fun e => pure e
  whnfCore := fun e => pure e
  whnfMode := fun e _ => pure e
  whnfCoreFlags := fun e _ => pure e
  infer := fun _ => pure natRef
  isDefEq := fun _ _ => pure true

theorem kIotaIntern :
    TcM.intern kSynthCtor kIotaState =
      .ok kSynthCtor kIotaAfterIntern := by
  unfold kIotaAfterIntern TcM.intern TcM.runIntern internExprM
  have hempty : kIotaState.env.intern.exprs[kSynthCtor.internKey]? = none := by
    have hloaded : loadedEnv.intern.exprs =
        ({} : Std.HashMap Address (KExpr .anon)) := by
      rfl
    simp [kIotaState, noAccelState, state, KEnv.insert, hloaded]
  simp only [InternTable.internExpr, hempty]

theorem kIotaMajorInfer :
    (RecM.tryOptional (RecM.inferOnlyRec kMajor)).run
      kIotaHarnessMethods kIotaState =
      .ok (some natRef) kIotaState := by
  rfl

theorem kIotaMajorWhnf :
    (RecM.tryOptional (RecM.whnfRec natRef)).run
      kIotaHarnessMethods kIotaState =
      .ok (some natRef) kIotaState := by
  rfl

theorem kIotaGetRec :
    TcM.tryGetConst iotaId kIotaState =
      .ok (some kIotaConcrete) kIotaState := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ kIotaState = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) kIotaState =
    .ok kIotaState kIotaState from rfl]
  simp only
  have hne : kMajorId ≠ iotaId := by
    intro h
    exact address_ne (a := 16) (b := 14) (by decide)
      (congrArg KId.addr h)
  have henv : kIotaState.env.get? iotaId = some kIotaConcrete := by
    simp only [kIotaState, KEnv.get?, KEnv.insert,
      Std.HashMap.getElem?_insert]
    split
    · next h => exact False.elim (hne (eq_of_beq h))
    · simp
  rw [henv]
  rfl

theorem kIotaGetNat :
    TcM.tryGetConst natId kIotaState =
      .ok (some natConcrete) kIotaState := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ kIotaState = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) kIotaState =
    .ok kIotaState kIotaState from rfl]
  simp only
  have hmajor : kMajorId ≠ natId := by
    intro h
    exact address_ne (a := 16) (b := 10) (by decide)
      (congrArg KId.addr h)
  have hrec : iotaId ≠ natId := by
    intro h
    exact address_ne (a := 14) (b := 10) (by decide)
      (congrArg KId.addr h)
  have henv : kIotaState.env.get? natId = some natConcrete := by
    simp only [kIotaState, KEnv.get?, KEnv.insert,
      Std.HashMap.getElem?_insert]
    split
    · next h => exact False.elim (hmajor (eq_of_beq h))
    · split
      · next h => exact False.elim (hrec (eq_of_beq h))
      · change loadedEnv.get? natId = some natConcrete
        exact loadedEnv_nat
  rw [henv]
  rfl

theorem kIotaMajorInductive :
    (RecM.tryOptional (RecM.getMajorInductiveId kRecType 0)).run
      kIotaHarnessMethods kIotaState = .ok (some natId) kIotaState := by
  have hzero : (0 : UInt64).toNat = 0 := by decide
  have hget :
      (RecM.getMajorInductiveId kRecType 0).run
        kIotaHarnessMethods kIotaState = .ok natId kIotaState := by
    rw [RecM.scratch_getMajorInductiveId_run]
    apply RecM.scratch_tryFinally_ok
    · rw [hzero]
      simp only [RecM.peelMajorForalls, pure_bind]
      unfold RecM.scanMajorInductive
      rw [ReaderT.run_bind]
      change EStateM.bind
        (ReaderT.run (RecM.whnfRec kRecType) kIotaHarnessMethods) _
          kIotaState = _
      unfold EStateM.bind
      rw [show (RecM.whnfRec kRecType).run kIotaHarnessMethods kIotaState =
        .ok kRecType kIotaState from rfl]
      simp only
      change EStateM.bind (TcM.tryGetConst natId) _ kIotaState = _
      unfold EStateM.bind
      rw [kIotaGetNat]
      rfl
    · rfl
  exact RecM.tryOptional_success hget

theorem kIotaCtorInfer :
    (RecM.tryOptional (RecM.inferOnlyRec kSynthCtor)).run
      kIotaHarnessMethods kIotaAfterIntern =
        .ok (some natRef) kIotaAfterIntern := by
  rfl

theorem kIotaAttemptStats :
    TcM.bumpStats
      (fun st : TcState .anon =>
        { st with kSynthAttempts := st.kSynthAttempts + 1 })
      kIotaAfterIntern = .ok () kIotaAfterIntern := by
  exact TcM.bumpStats_disabled rfl _

theorem kIotaTypeDefEq :
    (RecM.callIsDefEq natRef natRef).run kIotaHarnessMethods
      kIotaAfterIntern = .ok true kIotaAfterIntern := by
  rfl

def kIotaCandidateTrace :
    RecM.VerifyKSynthCandidateSuccessTrace kIotaHarnessMethods natRef zeroId
      #[] #[] 0 kIotaState kSynthCtor kIotaAfterIntern where
  ctorHead := kSynthCtor
  ctorTy := natRef
  sCtorHead := kIotaAfterIntern
  sCtorApp := kIotaAfterIntern
  sCtorTy := kIotaAfterIntern
  sAttempt := kIotaAfterIntern
  ctorHeadIntern := kIotaIntern
  ctorApps := by rfl
  ctorInfer := kIotaCtorInfer
  attemptStats := kIotaAttemptStats
  typeDefEq := kIotaTypeDefEq

theorem kIotaCandidate :
    (RecM.verifyKSynthCandidate natRef zeroId #[] #[] 0).run
      kIotaHarnessMethods kIotaState =
        .ok (.synthesized kSynthCtor) kIotaAfterIntern :=
  kIotaCandidateTrace.eval

def kIotaSynthTrace :
    RecM.SynthCtorWhenKSuccessTrace kIotaHarnessMethods kMajor iotaId
      kIotaInfo #[] kIotaState kSynthCtor kIotaAfterIntern where
  majorTy := natRef
  majorTyW := natRef
  tyHeadId := natId
  tyUs := #[]
  tyHeadInfo := natRef.info
  tyArgs := #[]
  recursor := kIotaConcrete
  recursorTy := kRecType
  indId := natId
  ctorId := zeroId
  indLvls := 0
  indParams := 0
  indIndices := 0
  indUnsafe := false
  indBlock := natId
  indMemberIdx := 0
  indTy := natType
  ctors := #[zeroId, succId]
  sMajorTy := kIotaState
  sMajorTyW := kIotaState
  sRecursor := kIotaState
  sInductive := kIotaState
  sIndLookup := kIotaState
  levelArity := by decide
  majorInfer := kIotaMajorInfer
  majorWhnf := kIotaMajorWhnf
  majorSpine := by
    unfold natRef
    rfl
  recursorLookup := kIotaGetRec
  recursorType := rfl
  majorInductive := kIotaMajorInductive
  sameInductive := rfl
  inductiveLookup := kIotaGetNat
  firstCtor := rfl
  candidate := kIotaCandidate

theorem kIotaSynth :
    (RecM.synthCtorWhenK kMajor iotaId kIotaInfo #[]).run
      kIotaHarnessMethods kIotaState =
        .ok (.synthesized kSynthCtor) kIotaAfterIntern :=
  kIotaSynthTrace.eval

theorem kIotaInternFrame :
    InternUpdateFrame kIotaState kIotaAfterIntern := by
  rfl

theorem kIotaSynthCleanup :
    (RecM.cleanupNatOffsetMajor kSynthCtor).run kIotaHarnessMethods
      kIotaAfterIntern = .ok none kIotaAfterIntern := by
  have hextract :
      extractNatValue kSynthCtor (iotaPrims Primitives.ofAnonAddrs) = some 0 := by
    unfold kSynthCtor
    rw [KExpr.mkConst_shape]
    unfold extractNatValue extractNatLit
    simp [iotaPrims]
  have heval :
      (RecM.evalNatOffsetLiteral kSynthCtor 0).run kIotaHarnessMethods
        kIotaAfterIntern = .ok (some 0) kIotaAfterIntern := by
    unfold RecM.evalNatOffsetLiteral RecM.evalNatOffsetLiteralFuel
    rw [show (256 - 0 : Nat) = Nat.succ 255 from rfl]
    rw [ReaderT.run_bind]
    change EStateM.bind
      (ReaderT.run RecM.prims kIotaHarnessMethods) _ kIotaAfterIntern = _
    unfold EStateM.bind
    rw [show ReaderT.run RecM.prims kIotaHarnessMethods kIotaAfterIntern =
      .ok (iotaPrims Primitives.ofAnonAddrs) kIotaAfterIntern from rfl]
    simp only
    rw [hextract]
    rfl
  unfold RecM.cleanupNatOffsetMajor
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (RecM.evalNatOffsetLiteral kSynthCtor 0)
      kIotaHarnessMethods) _ kIotaAfterIntern = _
  unfold EStateM.bind
  rw [heval]
  rfl

theorem kIotaSynthWhnf (flags : WhnfFlags) :
    (if flags.cheapRec then
        (RecM.whnfCoreFlagsRec kSynthCtor flags).run kIotaHarnessMethods
          kIotaAfterIntern
      else (RecM.whnfRec kSynthCtor).run kIotaHarnessMethods
          kIotaAfterIntern) = .ok kSynthCtor kIotaAfterIntern := by
  cases flags.cheapRec <;>
    simp [RecM.whnfCoreFlagsRec, RecM.whnfRec,
      kIotaHarnessMethods] <;> rfl

theorem kIotaGetZeroAfter :
    TcM.tryGetConst zeroId kIotaAfterIntern =
      .ok (some zeroConcrete) kIotaAfterIntern := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _
    kIotaAfterIntern = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) kIotaAfterIntern =
    .ok kIotaAfterIntern kIotaAfterIntern from rfl]
  simp only
  have hconsts : kIotaAfterIntern.env.consts = kIotaState.env.consts := by
    simpa [InternUpdateFrame] using
      congrArg (fun st : TcState .anon => st.env.consts) kIotaInternFrame
  have hmajor : kMajorId ≠ zeroId := by
    intro h
    exact address_ne (a := 16) (b := 11) (by decide)
      (congrArg KId.addr h)
  have hrec : iotaId ≠ zeroId := by
    intro h
    exact address_ne (a := 14) (b := 11) (by decide)
      (congrArg KId.addr h)
  have hinitial : kIotaState.env.get? zeroId = some zeroConcrete := by
    simp only [kIotaState, KEnv.get?, KEnv.insert,
      Std.HashMap.getElem?_insert]
    split
    · next h => exact False.elim (hmajor (eq_of_beq h))
    · split
      · next h => exact False.elim (hrec (eq_of_beq h))
      · change loadedEnv.get? zeroId = some zeroConcrete
        exact loadedEnv_zero_k1e
  have hget :
      kIotaAfterIntern.env.get? zeroId = kIotaState.env.get? zeroId := by
    unfold KEnv.get?
    rw [hconsts]
  rw [hget, hinitial]
  rfl

theorem kIotaApplyRule :
    (RecM.applyIotaRule iotaRule #[] kIotaInfo #[kMajor] #[] 0 false).run
        kIotaHarnessMethods kIotaAfterIntern =
      .ok iotaResult kIotaAfterIntern := by
  unfold RecM.applyIotaRule
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.instantiateUnivParams iotaRule.rhs #[]) _
    kIotaAfterIntern = _
  unfold EStateM.bind
  rw [show TcM.instantiateUnivParams iotaRule.rhs #[] kIotaAfterIntern =
    .ok iotaResult kIotaAfterIntern from rfl]
  rfl

theorem kIotaApplyCtor :
    (RecM.tryApplyIotaCtor kIotaInfo #[] #[kMajor] #[] 0 0 false).run
        kIotaHarnessMethods kIotaAfterIntern =
      .ok (some iotaResult) kIotaAfterIntern := by
  exact (RecM.TryApplyIotaCtorSuccessTrace.mk rfl rfl (by decide)
    kIotaApplyRule).eval

/-- Inhabited ConstructorSynthesis path: the arbitrary major is assigned `Nat`, synthesis
selects `Nat.zero`, and the resulting constructor is dispatched by the real
iota helper.  The sole state change is constructor interning. -/
theorem kIotaTryEval (flags : WhnfFlags) :
    (RecM.tryIotaWithFlags kIotaSource flags).run kIotaHarnessMethods
      kIotaState = .ok (some iotaResult) kIotaAfterIntern := by
  apply RecM.tryIotaWithFlags_kCtor
    (recId := iotaId) (recUs := #[]) (spine := #[kMajor])
    (recursor := kIotaConcrete) (recr := kIotaInfo)
    (major := kMajor) (synthesized := kSynthCtor)
    (majorWhnf := kSynthCtor)
    (ctorId := zeroId) (ctorUs := #[]) (ctorArgs := #[])
    (ctor := zeroConcrete) (cidx := 0) (ctorFields := 0)
  · unfold kIotaSource iotaHead
    rw [KExpr.mkApp_shape, KExpr.mkConst_shape]
    rfl
  · exact kIotaGetRec
  · rfl
  · decide
  · rfl
  · rfl
  · exact kIotaSynth
  · exact kIotaSynthCleanup
  · exact kIotaSynthWhnf flags
  · unfold kSynthCtor
    exact .const
  · exact kIotaSynthCleanup
  · unfold kSynthCtor
    rfl
  · exact kIotaGetZeroAfter
  · rfl
  · exact kIotaApplyCtor

theorem kIotaStepEval (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep kIotaSource flags).run kIotaHarnessMethods
      kIotaState = .ok (.next iotaResult) kIotaAfterIntern := by
  unfold kIotaSource iotaHead
  rw [KExpr.mkApp_shape, KExpr.mkConst_shape]
  apply RecM.whnfCoreWithFlagsStep_iota
    (recId := iotaId) (us := #[])
    (headInfo := (KExpr.mkConst iotaId #[] ()).info)
    (args := #[kMajor])
  · simp [KExpr.collectSpine, KExpr.collectSpine.go]
  · rfl
  · change Bool.not ((KExpr.mkConst iotaId #[] ()).info.addr ==
        (KExpr.mkConst iotaId #[] ()).info.addr) = false
    rw [beq_self_eq_true]
    rfl
  · exact kIotaTryEval flags

theorem kIotaCoreEval (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsUncached kIotaSource flags).run
      kIotaHarnessMethods kIotaState = .ok iotaResult kIotaAfterIntern := by
  apply RecM.whnfCoreWithFlagsUncached_nextLeaf
  · exact kIotaStepEval flags
  · exact .const

/-! ### ConstructorSynthesisFallback inhabited K-synthesis fallback paths -/

/-- A callback that mutates recursive fuel and then fails.  `inferOnlyRec`
must restore its policy flag, while `tryOptional` must retain the fuel
mutation. -/
def kInferErrorMethods : Methods .anon :=
  { kIotaHarnessMethods with
    infer := fun _ => do
      modify fun s => { s with recFuel := s.recFuel - 1 }
      throw .maxRecFuel }

def kMajorInferErrorState : TcState .anon :=
  { kIotaState with recFuel := kIotaState.recFuel - 1 }

def kCandidateInferErrorState : TcState .anon :=
  { kIotaAfterIntern with recFuel := kIotaAfterIntern.recFuel - 1 }

theorem kMajorInferRawError :
    (RecM.inferOnlyRec kMajor).run kInferErrorMethods kIotaState =
      .error .maxRecFuel kMajorInferErrorState := by
  rfl

/-- The first K-synthesis callback error is swallowed, but its consumed fuel
is observable in the final state. -/
theorem kMajorInferCaughtMiss :
    (RecM.synthCtorWhenK kMajor iotaId kIotaInfo #[]).run
      kInferErrorMethods kIotaState = .ok .inconclusive kMajorInferErrorState :=
  RecM.synthCtorWhenK_majorInferError (by decide) kMajorInferRawError

theorem kCandidateInferRawError :
    (RecM.inferOnlyRec kSynthCtor).run kInferErrorMethods kIotaAfterIntern =
      .error .maxRecFuel kCandidateInferErrorState := by
  rfl

/-- Candidate inference fails after constructor interning.  The fallback
therefore retains both the intern-table update and the callback's fuel use,
without incrementing either K-synthesis counter. -/
theorem kCandidateInferCaughtMiss :
    (RecM.verifyKSynthCandidate natRef zeroId #[] #[] 0).run
      kInferErrorMethods kIotaState =
        .ok .inconclusive kCandidateInferErrorState := by
  exact RecM.verifyKSynthCandidate_inferError kIotaIntern (by rfl)
    kCandidateInferRawError

/-- A DefEq callback with the same fuel mutation.  This callback is outside
`tryOptional`, so its error must remain an error. -/
def kDefEqErrorMethods : Methods .anon :=
  { kIotaHarnessMethods with
    isDefEq := fun _ _ => do
      modify fun s => { s with recFuel := s.recFuel - 1 }
      throw .maxRecFuel }

def kDefEqErrorState : TcState .anon :=
  { kIotaAfterIntern with recFuel := kIotaAfterIntern.recFuel - 1 }

theorem kDefEqRawError :
    (RecM.callIsDefEq natRef natRef).run kDefEqErrorMethods
      kIotaAfterIntern = .error .maxRecFuel kDefEqErrorState := by
  rfl

theorem kDefEqCandidateError :
    (RecM.verifyKSynthCandidate natRef zeroId #[] #[] 0).run
      kDefEqErrorMethods kIotaState =
        .error .maxRecFuel kDefEqErrorState := by
  exact RecM.verifyKSynthCandidate_defEqError kIotaIntern (by rfl)
    (by rfl) kIotaAttemptStats kDefEqRawError

def kDefEqSelectionTrace :
    RecM.SynthCtorWhenKSelectionTrace kDefEqErrorMethods kMajor iotaId
      kIotaInfo #[] kIotaState where
  majorTy := natRef
  majorTyW := natRef
  tyHeadId := natId
  tyUs := #[]
  tyHeadInfo := natRef.info
  tyArgs := #[]
  recursor := kIotaConcrete
  recTy := kRecType
  indId := natId
  sInfer := kIotaState
  sWhnf := kIotaState
  sRec := kIotaState
  sScan := kIotaState
  levelArity := by decide
  majorInfer := by rfl
  majorWhnf := by rfl
  majorSpine := by
    unfold natRef
    rfl
  recursorLookup := kIotaGetRec
  recursorType := rfl
  majorInductive := by
    change (RecM.tryOptional (RecM.getMajorInductiveId kRecType 0)).run
      kDefEqErrorMethods kIotaState = .ok (some natId) kIotaState
    have hzero : (0 : UInt64).toNat = 0 := by decide
    have hget :
        (RecM.getMajorInductiveId kRecType 0).run
          kDefEqErrorMethods kIotaState = .ok natId kIotaState := by
      rw [RecM.scratch_getMajorInductiveId_run]
      apply RecM.scratch_tryFinally_ok
      · rw [hzero]
        simp only [RecM.peelMajorForalls, pure_bind]
        unfold RecM.scanMajorInductive
        rw [ReaderT.run_bind]
        change EStateM.bind
          (ReaderT.run (RecM.whnfRec kRecType) kDefEqErrorMethods) _
            kIotaState = _
        unfold EStateM.bind
        rw [show (RecM.whnfRec kRecType).run kDefEqErrorMethods kIotaState =
          .ok kRecType kIotaState from rfl]
        simp only
        change EStateM.bind (TcM.tryGetConst natId) _ kIotaState = _
        unfold EStateM.bind
        rw [kIotaGetNat]
        rfl
      · rfl
    exact RecM.tryOptional_success hget

/-- The same error that candidate verification exposes propagates through
the complete K-synthesis helper; it is not converted to fallback absence. -/
theorem kDefEqSynthError :
    (RecM.synthCtorWhenK kMajor iotaId kIotaInfo #[]).run
      kDefEqErrorMethods kIotaState =
        .error .maxRecFuel kDefEqErrorState := by
  apply kDefEqSelectionTrace.selectedError (by rfl) kIotaGetNat rfl
  exact kDefEqCandidateError

/-- Malformed inductive catalog entry used to inhabit the reachable
empty-constructor fallback after the bounded major scan. -/
def kEmptyNatConcrete : KConst .anon :=
  .indc () () 0 0 0 false natId 0 natType #[] ()

def kEmptyInductiveState : TcState .anon :=
  { kIotaState with env := kIotaState.env.insert natId kEmptyNatConcrete }

theorem kEmptyGetRec :
    TcM.tryGetConst iotaId kEmptyInductiveState =
      .ok (some kIotaConcrete) kEmptyInductiveState := by
  rw [TcM.tryGetConst_noLazy (by rfl)]
  have hnat : natId ≠ iotaId := by
    intro h
    exact address_ne (a := 10) (b := 14) (by decide)
      (congrArg KId.addr h)
  have hbase : kIotaState.env.get? iotaId = some kIotaConcrete := by
    have h := kIotaGetRec
    rw [TcM.tryGetConst_noLazy (by rfl)] at h
    exact (EStateM.Result.ok.inj h).1
  have hlookup :
      kEmptyInductiveState.env.get? iotaId = kIotaState.env.get? iotaId := by
    simp only [kEmptyInductiveState, KEnv.get?, KEnv.insert,
      Std.HashMap.getElem?_insert]
    split
    · next h => exact False.elim (hnat (eq_of_beq h))
    · rfl
  rw [hlookup, hbase]

theorem kEmptyGetNat :
    TcM.tryGetConst natId kEmptyInductiveState =
      .ok (some kEmptyNatConcrete) kEmptyInductiveState := by
  rw [TcM.tryGetConst_noLazy (by rfl)]
  simp [kEmptyInductiveState, KEnv.get?, KEnv.insert]

theorem kEmptyMajorInductive :
    (RecM.tryOptional (RecM.getMajorInductiveId kRecType 0)).run
      kIotaHarnessMethods kEmptyInductiveState =
        .ok (some natId) kEmptyInductiveState := by
  have hzero : (0 : UInt64).toNat = 0 := by decide
  have hget :
      (RecM.getMajorInductiveId kRecType 0).run
        kIotaHarnessMethods kEmptyInductiveState =
          .ok natId kEmptyInductiveState := by
    rw [RecM.scratch_getMajorInductiveId_run]
    apply RecM.scratch_tryFinally_ok
    · rw [hzero]
      simp only [RecM.peelMajorForalls, pure_bind]
      unfold RecM.scanMajorInductive
      rw [ReaderT.run_bind]
      change EStateM.bind
        (ReaderT.run (RecM.whnfRec kRecType) kIotaHarnessMethods) _
          kEmptyInductiveState = _
      unfold EStateM.bind
      rw [show (RecM.whnfRec kRecType).run kIotaHarnessMethods
        kEmptyInductiveState = .ok kRecType kEmptyInductiveState from rfl]
      simp only
      change EStateM.bind (TcM.tryGetConst natId) _ kEmptyInductiveState = _
      unfold EStateM.bind
      rw [kEmptyGetNat]
      rfl
    · rfl
  exact RecM.tryOptional_success hget

def kEmptySelectionTrace :
    RecM.SynthCtorWhenKSelectionTrace kIotaHarnessMethods kMajor iotaId
      kIotaInfo #[] kEmptyInductiveState where
  majorTy := natRef
  majorTyW := natRef
  tyHeadId := natId
  tyUs := #[]
  tyHeadInfo := natRef.info
  tyArgs := #[]
  recursor := kIotaConcrete
  recTy := kRecType
  indId := natId
  sInfer := kEmptyInductiveState
  sWhnf := kEmptyInductiveState
  sRec := kEmptyInductiveState
  sScan := kEmptyInductiveState
  levelArity := by decide
  majorInfer := by rfl
  majorWhnf := by rfl
  majorSpine := by
    unfold natRef
    rfl
  recursorLookup := kEmptyGetRec
  recursorType := rfl
  majorInductive := kEmptyMajorInductive

/-- A scanned inductive with no constructors reaches the defensive silent
fallback without changing checker state. -/
theorem kEmptyInductiveMiss :
    (RecM.synthCtorWhenK kMajor iotaId kIotaInfo #[]).run
      kIotaHarnessMethods kEmptyInductiveState =
        .ok .inconclusive kEmptyInductiveState := by
  apply kEmptySelectionTrace.empty (by rfl)
  exact kEmptyGetNat

/-! ### StructEtaControl inhabited struct-eta paths -/

/-- A deliberately small non-recursive, one-constructor structure fixture.
The selected rule has one field, so success must intern both a projection and
its application rather than discharging only empty loops. -/
def structEtaIndAddress : Address := address 17
def structEtaCtorAddress : Address := address 18
def structEtaRecAddress : Address := address 19
def structEtaMajorAddress : Address := address 20

def structEtaIndId : KId .anon := ⟨structEtaIndAddress, ()⟩
def structEtaCtorId : KId .anon := ⟨structEtaCtorAddress, ()⟩
def structEtaRecId : KId .anon := ⟨structEtaRecAddress, ()⟩
def structEtaMajorId : KId .anon := ⟨structEtaMajorAddress, ()⟩

def structEtaType : KExpr .anon := .sort oneLevel (info structEtaIndAddress)
def structEtaRef : KExpr .anon :=
  .const structEtaIndId #[] (info structEtaCtorAddress)
def structEtaMajor : KExpr .anon :=
  .const structEtaMajorId #[] (info structEtaMajorAddress)
def structEtaRhs : KExpr .anon := KExpr.mkConst succId #[]
def structEtaCtorType : KExpr .anon :=
  .all () () natRef structEtaRef (info structEtaCtorAddress)
def structEtaRecType : KExpr .anon :=
  .all () () structEtaRef natRef (info structEtaRecAddress)

def structEtaInductive : KConst .anon :=
  .indc () () 0 0 0 false structEtaIndId 0 structEtaType
    #[structEtaCtorId] ()
def structEtaConstructor : KConst .anon :=
  .ctor () () false 0 structEtaIndId 0 0 1 structEtaCtorType
def structEtaMajorConst : KConst .anon :=
  .axio () () false 0 structEtaRef
def structEtaRule : RecRule .anon :=
  { ctor := (), fields := 1, rhs := structEtaRhs }
def structEtaRecursor : KConst .anon :=
  .recr () () false false 0 0 0 0 0 structEtaIndId 0 structEtaRecType
    #[structEtaRule] ()
def structEtaInfo : IotaInfo .anon :=
  { k := false, params := 0, motives := 0, minors := 0, indices := 0,
    majorIdx := 0, rules := #[structEtaRule], lvls := 0 }

/-- The cached `false` recursion result isolates StructEtaControl from the internals of
inductive recursion analysis while still running the real classifier. -/
def structEtaState : TcState .anon :=
  let base := noAccelState (iotaPrims Primitives.ofAnonAddrs)
  let withRec := { base with
    env := base.env.insert structEtaRecId structEtaRecursor }
  let withInd := { withRec with
    env := withRec.env.insert structEtaIndId structEtaInductive }
  let withCtor := { withInd with
    env := withInd.env.insert structEtaCtorId structEtaConstructor }
  let withMajor := { withCtor with
    env := withCtor.env.insert structEtaMajorId structEtaMajorConst }
  { withMajor with env := { withMajor.env with
      isRecCache := withMajor.env.isRecCache.insert structEtaIndAddress false } }

/-- Minimal predecessor callbacks for the operational fixture.  The two
inference probes return a universe-bearing sort and WHNF is already reached.
This harness is intentionally not claimed to satisfy `Methods.WF`. -/
def structEtaMethods : Methods .anon where
  whnf := fun e => pure e
  whnfCore := fun e => pure e
  whnfMode := fun e _ => pure e
  whnfCoreFlags := fun e _ => pure e
  infer := fun _ => pure structEtaType
  isDefEq := fun _ _ => pure true

/-- Inhabited CallbackPrefix infer-only scope: the production callback observes the
enabled flag internally, returns the fixture type, and restores the caller's
flag without changing the remaining state. -/
theorem structEtaInferOnlyRun :
    (RecM.inferOnlyRec structEtaMajor).run structEtaMethods structEtaState =
      .ok structEtaType structEtaState := by
  rw [RecM.inferOnlyRec_run, TcM.withInferOnly_eq]
  rfl

/-- The same concrete callback through production's optional catch returns a
present value and retains the exact restored state. -/
theorem structEtaOptionalInferOnlyRun :
    (RecM.tryOptional (RecM.inferOnlyRec structEtaMajor)).run
      structEtaMethods structEtaState =
        .ok (some structEtaType) structEtaState :=
  RecM.tryOptional_success structEtaInferOnlyRun

theorem structEtaGetRecursor :
    TcM.tryGetConst structEtaRecId structEtaState =
      .ok (some structEtaRecursor) structEtaState := by
  rw [TcM.tryGetConst_noLazy (by rfl)]
  have hmajor : structEtaMajorId ≠ structEtaRecId := by
    intro h
    exact address_ne (a := 20) (b := 19) (by decide)
      (congrArg KId.addr h)
  have hctor : structEtaCtorId ≠ structEtaRecId := by
    intro h
    exact address_ne (a := 18) (b := 19) (by decide)
      (congrArg KId.addr h)
  have hind : structEtaIndId ≠ structEtaRecId := by
    intro h
    exact address_ne (a := 17) (b := 19) (by decide)
      (congrArg KId.addr h)
  simp only [structEtaState, KEnv.get?, KEnv.insert,
    Std.HashMap.getElem?_insert]
  split
  · next h => exact False.elim (hmajor (eq_of_beq h))
  · split
    · next h => exact False.elim (hctor (eq_of_beq h))
    · split
      · next h => exact False.elim (hind (eq_of_beq h))
      · simp

theorem structEtaGetInductive :
    TcM.tryGetConst structEtaIndId structEtaState =
      .ok (some structEtaInductive) structEtaState := by
  rw [TcM.tryGetConst_noLazy (by rfl)]
  have hmajor : structEtaMajorId ≠ structEtaIndId := by
    intro h
    exact address_ne (a := 20) (b := 17) (by decide)
      (congrArg KId.addr h)
  have hctor : structEtaCtorId ≠ structEtaIndId := by
    intro h
    exact address_ne (a := 18) (b := 17) (by decide)
      (congrArg KId.addr h)
  simp only [structEtaState, KEnv.get?, KEnv.insert,
    Std.HashMap.getElem?_insert]
  split
  · next h => exact False.elim (hmajor (eq_of_beq h))
  · split
    · next h => exact False.elim (hctor (eq_of_beq h))
    · simp

theorem structEtaGetMajor :
    TcM.tryGetConst structEtaMajorId structEtaState =
      .ok (some structEtaMajorConst) structEtaState := by
  rw [TcM.tryGetConst_noLazy (by rfl)]
  simp [structEtaState, KEnv.get?, KEnv.insert]

theorem structEtaComputedNotRec (methods : Methods .anon) :
    (RecM.computedIsRec structEtaIndId).run methods structEtaState =
      .ok false structEtaState := by
  have hcache :
      structEtaState.env.isRecCache[structEtaIndId.addr]? = some false := by
    simp [structEtaState, structEtaIndId]
  unfold RecM.computedIsRec
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ structEtaState = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) structEtaState =
    .ok structEtaState structEtaState from rfl]
  simp only
  rw [hcache]
  rfl

theorem structEtaClassified (methods : Methods .anon) :
    (RecM.isStructLike structEtaIndId).run methods structEtaState =
      .ok true structEtaState := by
  have h := RecM.isStructLike_shapeQualified structEtaGetInductive
    (show ((0 : UInt64) != 0 || (#[structEtaCtorId]).size != 1) = false by
      decide)
    (structEtaComputedNotRec methods)
  simpa using h

theorem structEtaMajorInductive (methods : Methods .anon)
    (hwhnf : (RecM.whnfRec structEtaRecType).run methods structEtaState =
      .ok structEtaRecType structEtaState) :
    (RecM.tryOptional (RecM.getMajorInductiveId structEtaRecType 0)).run
      methods structEtaState =
        .ok (some structEtaIndId) structEtaState := by
  have hzero : (0 : UInt64).toNat = 0 := by decide
  have hget :
      (RecM.getMajorInductiveId structEtaRecType 0).run
        methods structEtaState =
          .ok structEtaIndId structEtaState := by
    rw [RecM.scratch_getMajorInductiveId_run]
    apply RecM.scratch_tryFinally_ok
    · rw [hzero]
      simp only [RecM.peelMajorForalls, pure_bind]
      unfold RecM.scanMajorInductive
      rw [ReaderT.run_bind]
      change EStateM.bind
        (ReaderT.run (RecM.whnfRec structEtaRecType) methods) _
          structEtaState = _
      unfold EStateM.bind
      rw [hwhnf]
      simp only
      change EStateM.bind (TcM.tryGetConst structEtaIndId) _ structEtaState = _
      unfold EStateM.bind
      rw [structEtaGetInductive]
      rfl
    · rfl
  exact RecM.tryOptional_success hget

def structEtaSelectionTrace :
    RecM.StructEtaSelectionTrace structEtaMethods structEtaRecId structEtaInfo
      #[] #[structEtaMajor] structEtaState where
  rule := structEtaRule
  recursor := structEtaRecursor
  recTy := structEtaRecType
  indId := structEtaIndId
  sRec := structEtaState
  sScan := structEtaState
  ruleCount := by decide
  levelArity := by decide
  selectedRule := rfl
  recursorLookup := structEtaGetRecursor
  recursorType := rfl
  majorInductive := structEtaMajorInductive structEtaMethods (by rfl)

def structEtaProbeTrace :
    RecM.StructEtaProbeTrace structEtaMethods #[] #[structEtaMajor]
      structEtaInfo structEtaRule structEtaIndId structEtaState where
  majorTy := structEtaType
  majorSort := structEtaType
  majorSortW := structEtaType
  sStruct := structEtaState
  sMajorTy := structEtaState
  sMajorSort := structEtaState
  sMajorSortW := structEtaState
  structLike := structEtaClassified structEtaMethods
  majorInfer := by rfl
  sortInfer := by rfl
  sortWhnf := by rfl

theorem structEtaInstantiate :
    TcM.instantiateUnivParams structEtaRule.rhs #[] structEtaState =
      .ok structEtaRhs structEtaState := by
  rfl

/-! #### Rebuild exact finite rebuild witness -/

/-- The one projection requested by the fixture's single struct field. -/
def structEtaProjection : KExpr .anon :=
  KExpr.mkPrj structEtaIndId 0 structEtaMajor

/-- The exact accumulator after applying the selected rule RHS to that
projection. -/
def structEtaRebuildResult : KExpr .anon :=
  KExpr.mkApp structEtaRhs structEtaProjection

/-- Both direct intern requests made by the one-field rebuild, in production
order. -/
def structEtaRebuildRequests : List WalkerRequest :=
  [.internExpr structEtaProjection, .internExpr structEtaRebuildResult]

/-- Non-vacuous Rebuild certificate for the actual struct-eta fixture.  Empty
prefix and trailing slices leave exactly the projection/application pair. -/
def structEtaBuildRequests :
    RecM.StructEtaBuildRequests structEtaRebuildRequests structEtaIndId
      structEtaMajor structEtaRhs 1 #[] #[] structEtaRebuildResult := by
  refine {
    prefixResult := structEtaRhs
    fieldsResult := structEtaRebuildResult
    prefixCert := RecM.FinishAppRequests.nil structEtaRhs
    fieldCert := ?_
    trailingCert := RecM.FinishAppRequests.nil structEtaRebuildResult }
  apply RecM.StructEtaFieldRequests.cons
  · simp [structEtaRebuildRequests, structEtaProjection]
  · simp [structEtaRebuildRequests, structEtaProjection,
      structEtaRebuildResult]
  · simpa [structEtaProjection, structEtaRebuildResult] using
      (RecM.StructEtaFieldRequests.nil
        (requests := structEtaRebuildRequests)
        (indId := structEtaIndId) (major := structEtaMajor)
        1 structEtaRebuildResult)

/-- Inhabited successful StructEtaControl path.  The existential post-state is genuine:
the one-field rule performs the production projection and application intern
requests, whose concrete table result is intentionally not assumed
collision-free by this operational fixture. -/
theorem structEtaIotaSuccess :
    ∃ result sf,
      ∃ _ : RecM.StructEtaIotaSuccessTrace structEtaMethods structEtaRecId
        structEtaInfo #[] #[structEtaMajor] structEtaState result sf,
      (RecM.tryStructEtaIota structEtaRecId structEtaInfo #[]
        #[structEtaMajor]).run structEtaMethods structEtaState =
          .ok (some result) sf := by
  obtain ⟨result, sf, hbuild⟩ :=
    RecM.finishStructEtaResult_total structEtaMethods structEtaState
      structEtaIndId structEtaMajor structEtaRhs 1 #[] #[]
  let trace : RecM.StructEtaIotaSuccessTrace structEtaMethods structEtaRecId
      structEtaInfo #[] #[structEtaMajor] structEtaState result sf :=
    { selection := structEtaSelectionTrace
      probes := structEtaProbeTrace
      rhs := structEtaRhs
      sInst := structEtaState
      admissible := by
        simp only [RecM.StructEtaSortAdmissible, structEtaProbeTrace,
          RecM.structEtaSortRejected, structEtaType]
        exact KUniv.isSemanticZero_eq_false (ρ := []) (by decide) (by decide)
      instantiation := structEtaInstantiate
      rebuild := by
        simpa [structEtaSelectionTrace, structEtaProbeTrace, structEtaInfo,
          structEtaRule]
          using hbuild }
  exact ⟨result, sf, trace, trace.eval⟩

/-- The final constructor dispatcher genuinely takes its non-constructor
constant fallthrough before the successful struct-eta path. -/
theorem structEtaDispatchSuccess :
    ∃ result sf,
      (RecM.tryIotaCtorOrStructEta structEtaRecId structEtaInfo #[]
        #[structEtaMajor] structEtaMajor false).run structEtaMethods
          structEtaState = .ok (some result) sf := by
  obtain ⟨result, sf, _, heta⟩ := structEtaIotaSuccess
  refine ⟨result, sf, ?_⟩
  apply RecM.tryIotaCtorOrStructEta_notConstructor
    (ctorId := structEtaMajorId) (ctorUs := #[]) (ctorArgs := #[])
    (entry := structEtaMajorConst)
  · rfl
  · exact structEtaGetMajor
  · rfl
  · exact heta

/-- The complementary absent environment stops at the repeated recursor
lookup without mutating checker state. -/
def structEtaAbsentState : TcState .anon :=
  let base := noAccelState (iotaPrims Primitives.ofAnonAddrs)
  { base with env := { base.env with consts := {} } }

theorem structEtaRecursorAbsent :
    TcM.tryGetConst structEtaRecId structEtaAbsentState =
      .ok none structEtaAbsentState := by
  rw [TcM.tryGetConst_noLazy (by rfl)]
  have henv : structEtaAbsentState.env.get? structEtaRecId = none := by
    simp [structEtaAbsentState, KEnv.get?]
  rw [henv]

theorem structEtaIotaAbsent :
    (RecM.tryStructEtaIota structEtaRecId structEtaInfo #[]
      #[structEtaMajor]).run structEtaMethods structEtaAbsentState =
        .ok none structEtaAbsentState := by
  exact RecM.tryStructEtaIota_recursorMissing (by decide)
    (by decide) structEtaRecursorAbsent

/-- A mutating inference failure inhabits the caught-error path: its fuel
consumption remains observable even though struct eta reports absence. -/
def structEtaInferErrorMethods : Methods .anon :=
  { structEtaMethods with infer := fun _ => do
      modify fun s => { s with recFuel := s.recFuel - 1 }
      throw .maxRecFuel }

def structEtaInferErrorState : TcState .anon :=
  { structEtaState with recFuel := structEtaState.recFuel - 1 }

theorem structEtaMajorInferRawError :
    (RecM.inferOnlyRec structEtaMajor).run structEtaInferErrorMethods
      structEtaState = .error .maxRecFuel structEtaInferErrorState := by
  rfl

def structEtaErrorSelectionTrace :
    RecM.StructEtaSelectionTrace structEtaInferErrorMethods structEtaRecId
      structEtaInfo #[] #[structEtaMajor] structEtaState where
  rule := structEtaRule
  recursor := structEtaRecursor
  recTy := structEtaRecType
  indId := structEtaIndId
  sRec := structEtaState
  sScan := structEtaState
  ruleCount := by decide
  levelArity := by decide
  selectedRule := rfl
  recursorLookup := structEtaGetRecursor
  recursorType := rfl
  majorInductive := structEtaMajorInductive structEtaInferErrorMethods (by rfl)

theorem structEtaClassifiedWithErrorMethods :
    (RecM.isStructLike structEtaIndId).run structEtaInferErrorMethods
      structEtaState = .ok true structEtaState := by
  exact structEtaClassified structEtaInferErrorMethods

theorem structEtaIotaCaughtInferError :
    (RecM.tryStructEtaIota structEtaRecId structEtaInfo #[]
      #[structEtaMajor]).run structEtaInferErrorMethods structEtaState =
        .ok none structEtaInferErrorState := by
  apply structEtaErrorSelectionTrace.eval
  exact RecM.tryStructEtaAfterInductive_majorInferError
    structEtaClassifiedWithErrorMethods structEtaMajorInferRawError

/-- Exact execution of the real iota helper on the untrusted recursor-shaped
catalog entry.  All parameter/motive/minor/field/trailing loops are empty,
but recursor lookup, major cleanup/WHNF, constructor lookup, and universe
instantiation are the production operations. -/
theorem iotaTryEval (prims : Primitives .anon) (flags : WhnfFlags) :
    (RecM.tryIotaWithFlags iotaSource flags).run betaHarnessMethods
      (iotaState prims) = .ok (some iotaResult) (iotaState prims) := by
  apply RecM.tryIotaWithFlags_regularCtor
    (recId := iotaId) (recUs := #[]) (spine := #[iotaResult])
    (recursor := iotaConcrete) (recr := iotaInfo)
    (major := iotaResult) (majorWhnf := iotaResult)
    (ctorId := zeroId) (ctorUs := #[]) (ctorArgs := #[])
    (ctor := zeroConcrete) (cidx := 0) (ctorFields := 0)
  · unfold iotaSource iotaHead
    rw [KExpr.mkApp_shape, KExpr.mkConst_shape]
    rfl
  · exact iotaGetRec prims
  · rfl
  · decide
  · rfl
  · rfl
  · exact iotaCleanup prims
  · exact iotaMajorWhnf prims flags
  · unfold iotaResult
    exact .const
  · exact iotaCleanup prims
  · unfold iotaResult
    rfl
  · exact iotaGetZero prims
  · rfl
  · exact iotaApplyCtor prims

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
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood support
        0 [] (iotaState prims) ∧
      (RecM.whnfCoreWithFlagsUncached iotaSource flags).run
        betaHarnessMethods (iotaState prims) =
          .ok iotaResult (iotaState prims) ∧
      ¬∃ sourceV,
        TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
          iotaSource sourceV :=
  ⟨iotaStateInv prims, iotaCoreEval prims flags,
    iotaSource_not_translated⟩

/-! ### structural trace structural-loop composition witness -/

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
      simpa [Lean4Lean.VExpr.inst, VExpr.natLit, VExpr.natSucc, succName] using
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
  simpa [Lean4Lean.VExpr.inst] using Lean4Lean.VEnv.HasType.app
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
    simpa [state, structuralLoopState, noAccelState, LocalContext.push] using hrec
  · apply LocalContext.WF.push .empty
    simp [fvarZetaId]
  · intro p hp
    simp [structuralLoopState, noAccelState, state, LocalContext.push] at hp
    subst p
    simp [structuralLoopState, fvarZetaId]

theorem structuralLoopStateInv (prims : Primitives .anon) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood support
      0 structuralLoopCtx (structuralLoopState prims) := by
  have hbase := noAccelStateInv prims
  refine ⟨?_, structuralLoopCtxRecon prims, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hbase.1.core.of_consts_eq (by rfl) (by
      simpa [structuralLoopState] using hbase.1.core.intern)
  · simpa [structuralLoopState] using hbase.1.internSupport
  · intro entry hentry
    apply hbase.1.caches
    cases hentry <;> (constructor; assumption)
  · simpa [structuralLoopState] using hbase.1.equivalences

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
  simpa [KVLCtx.toCtx, structuralLoopCtx] using betaA_type

theorem structuralLoopBody_type :
    worldGood.venv.HasType 0
      ((.const natName []) :: structuralLoopCtx.toCtx) (.bvar 0)
      (.const natName []) := by
  simpa [KVLCtx.toCtx, structuralLoopCtx] using betaBody_type

theorem structuralLoopArg_type :
    worldGood.venv.HasType 0 structuralLoopCtx.toCtx (.const zeroName [])
      (.const natName []) := by
  simpa [KVLCtx.toCtx, structuralLoopCtx] using betaArg_type

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
    RecM.WhnfCoreTrace .structuralNoAccel whnfSemantics RawProjRel.none worldGood
      support 0 structuralLoopCtx betaHarnessMethods flags maxWhnfCoreFuel.toNat
      structuralLoopSource (structuralLoopState prims) betaArg
      (structuralLoopState prims) := by
  rw [show maxWhnfCoreFuel.toNat = 10000000 by rfl]
  refine .next (structuralLoopStateInv prims)
    (structuralLoopFVarStep prims flags) (structuralLoopStateInv prims)
    (structuralLoopSourceMeaning prims) ?_
  refine .next (structuralLoopStateInv prims)
    (structuralLoopBetaStep prims flags) (structuralLoopStateInv prims)
    structuralLoopBetaMeaning ?_
  exact .done (structuralLoopStateInv prims)
    (structuralLoopLeafStep prims flags) (structuralLoopStateInv prims)
    structuralLoopLeafMeaning

/-- Inhabited structural trace acceptance: the real bounded driver executes more than one
`.next`, preserves the full invariant, and obtains the end-to-end meaning by
transitive composition rather than by asserting source/result equality. -/
theorem structuralLoopAcceptance (prims : Primitives .anon)
    (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsUncached structuralLoopSource flags).run
        betaHarnessMethods (structuralLoopState prims) =
          .ok betaArg (structuralLoopState prims) ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood support
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
      ¬RecM.WhnfCoreTrace .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        support 0 structuralLoopCtx betaHarnessMethods flags 0
        structuralLoopSource (structuralLoopState prims) betaArg
        (structuralLoopState prims) :=
  ⟨rfl, RecM.WhnfCoreTrace.no_zero⟩

/-! ### structural cache outer structural-WHNF cache composition witness -/

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
    intro source hsource haddr Δ hctx _hscoped
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
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
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
    · rfl
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
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
      coreCacheSupport 0 [] (fullCoreWarmState prims) := by
  exact RecM.WhnfCoreCacheUpdate.full_whnfStateInv
    (coreCacheFreshStateInv prims) fullCoreProvenance

theorem bothCoreWarmStateInv (prims : Primitives .anon) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
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
  simp [whnfContextKeys, coreCacheKey, structuralBetaSource_closed]

theorem betaTransientFalse (s : TcState .anon) :
    (RecM.isTransientNatLiteralWork betaSource).run betaHarnessMethods s =
      .ok false s := by
  unfold RecM.isTransientNatLiteralWork RecM.isNatLiteralRecursorApp
  unfold betaSource betaLam
  rw [KExpr.mkApp_shape, KExpr.mkLam_shape]
  simp [KExpr.collectSpine, KExpr.collectSpine.go]

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
    (hI : WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
      coreCacheSupport 0 [] s) (flags : WhnfFlags) :
    RecM.WhnfCoreTrace .structuralNoAccel whnfSemantics RawProjRel.none worldGood
      coreCacheSupport 0 [] betaHarnessMethods flags maxWhnfCoreFuel.toNat
      betaSource s betaArg s := by
  rw [show maxWhnfCoreFuel.toNat = 10000000 by rfl]
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
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (noAccelState prims) ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullCoreWarmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  simpa [whnfContextKeys, WhnfContextKeys.closed, betaSource, KExpr.mkApp, whnfSemantics, fullCoreWarmState] using
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
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullCoreWarmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  simpa [whnfContextKeys, WhnfContextKeys.closed, betaSource, KExpr.mkApp, whnfSemantics] using
    (RecM.whnfCoreWithFlags_fullHit_acceptance
      (keys := whnfContextKeys) (fallback := CacheSemantics.blockErrorsOnly)
      (.direct RecM.WhnfCoreNonLeaf.app) rfl
      (coreCacheKey_eval (fullCoreWarmState prims))
      (betaTransientFalse (fullCoreWarmState prims))
      (fullCoreWarm_hit prims) (fullCoreWarmStateInv prims) (.inl rfl)
      (coreCacheKey_matches (fullCoreWarmState prims)
        (fullCoreWarmStateInv prims).2.1)
      structuralBetaSource_tr.contextScoped)

/-- A full-policy entry is intentionally invisible to the cheap policy.  The
cheap call therefore runs its own trace and inserts into only its partition. -/
theorem cheapCorePolicyMissAcceptance (prims : Primitives .anon) :
    (RecM.whnfCoreWithFlags betaSource .DEF_EQ_CORE).run betaHarnessMethods
        (fullCoreWarmState prims) = .ok betaArg (bothCoreWarmState prims) ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullCoreWarmState prims) ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (bothCoreWarmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  simpa [whnfContextKeys, WhnfContextKeys.closed, betaSource, KExpr.mkApp, whnfSemantics, bothCoreWarmState] using
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
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (bothCoreWarmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  simpa [whnfContextKeys, WhnfContextKeys.closed, betaSource, KExpr.mkApp, whnfSemantics] using
    (RecM.whnfCoreWithFlags_cheapHit_acceptance
      (keys := whnfContextKeys) (fallback := CacheSemantics.blockErrorsOnly)
      (.direct RecM.WhnfCoreNonLeaf.app) rfl
      (coreCacheKey_eval (bothCoreWarmState prims))
      (betaTransientFalse (bothCoreWarmState prims))
      (bothCoreWarm_cheapHit prims) (bothCoreWarmStateInv prims) (.inl rfl)
      (coreCacheKey_matches (bothCoreWarmState prims)
        (bothCoreWarmStateInv prims).2.1)
      structuralBetaSource_tr.contextScoped)

/-- Direct adversarial observation of the flag partition after only the full
call has warmed its map. -/
theorem coreCachePolicyIsolation (prims : Primitives .anon) :
    (fullCoreWarmState prims).env.whnfCoreCache[coreCacheKey]? =
        some betaArg ∧
      (fullCoreWarmState prims).env.whnfCoreCheapCache[coreCacheKey]? = none :=
  ⟨fullCoreWarm_hit prims, fullCoreWarm_cheapMiss prims⟩

/-! ### outer WHNF driver no-delta/full-WHNF driver witness -/

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
    simpa [KEnv.get?, fullCoreWarmState, noAccelState, state] using loadedEnv_zero_k1e
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
  apply RecM.whnfNoDeltaImplStep_ofCore (fullCoreWarmAcceptance prims).1
  apply RecM.whnfNoDeltaReducersStep_doneFull
  · exact RecM.tryProjAppReduceFinished_none (betaNoDeltaProjNone prims)
  · exact RecM.tryReduceBitvec_noAccel rfl betaArg
  · exact betaNoDeltaNatNone prims
  · exact RecM.tryReduceNative_noAccel rfl betaArg
  · exact betaNoDeltaStringNone prims
  · rfl
  · exact betaNoDeltaProjectionDefNone prims
  · exact betaNoDeltaQuotNone prims

/-! #### ordered no-delta reduction ordered no-delta reducer witness -/

/-- Closed operational source for observing the precedence of the no-delta
reducer chain.  The canonical primitive address is intentionally independent
of the small ambient catalog above, so this is a branch-order witness rather
than a Theory-translation claim; `betaNoDeltaStep` supplies the inhabited
semantic stuck-path witness. -/
def noDeltaNatAddSource : KExpr .anon :=
  KExpr.mkApp
    (KExpr.mkApp (.mkConst Primitives.ofAnonAddrs.natAdd #[])
      (RecM.natExprFromValue 2))
    (RecM.natExprFromValue 3)

def noDeltaNatAddResult : KExpr .anon :=
  RecM.natExprFromValue 5

theorem noDeltaNatAddSpine :
    noDeltaNatAddSource.collectSpine =
      (.mkConst Primitives.ofAnonAddrs.natAdd #[],
        #[RecM.natExprFromValue 2, RecM.natExprFromValue 3]) := by
  unfold noDeltaNatAddSource
  rw [KExpr.mkApp_shape]
  unfold KExpr.collectSpine
  rw [KExpr.collectSpine.go, KExpr.mkApp_shape,
    KExpr.collectSpine.go, KExpr.mkConst_shape]
  change
    (KExpr.const Primitives.ofAnonAddrs.natAdd #[]
        (KExpr.mkConst Primitives.ofAnonAddrs.natAdd #[]).info,
      ((#[].push (RecM.natExprFromValue 3)).push
        (RecM.natExprFromValue 2)).reverse) = _
  simp

private theorem natAdd_ne_natSucc :
    (Primitives.ofAnonAddrs.natAdd.addr ==
      Primitives.ofAnonAddrs.natSucc.addr) = false := by
  native_decide

private theorem natAdd_ne_natBeq :
    (Primitives.ofAnonAddrs.natAdd.addr ==
      Primitives.ofAnonAddrs.natBeq.addr) = false := by
  native_decide

private theorem natAdd_ne_natBle :
    (Primitives.ofAnonAddrs.natAdd.addr ==
      Primitives.ofAnonAddrs.natBle.addr) = false := by
  native_decide

theorem noDeltaNatAddIsArith :
    (RecM.isNatBinArithAddr Primitives.ofAnonAddrs.natAdd.addr).run
      betaHarnessMethods (noAccelState Primitives.ofAnonAddrs) =
      .ok true (noAccelState Primitives.ofAnonAddrs) := by
  unfold RecM.isNatBinArithAddr RecM.prims
  rfl

theorem noDeltaNatAddIsPred :
    (RecM.isNatBinPredAddr Primitives.ofAnonAddrs.natAdd.addr).run
      betaHarnessMethods (noAccelState Primitives.ofAnonAddrs) =
      .ok false (noAccelState Primitives.ofAnonAddrs) := by
  unfold RecM.isNatBinPredAddr RecM.prims
  change EStateM.Result.ok
    (Primitives.ofAnonAddrs.natAdd.addr ==
        Primitives.ofAnonAddrs.natBeq.addr ||
      Primitives.ofAnonAddrs.natAdd.addr ==
        Primitives.ofAnonAddrs.natBle.addr)
      (noAccelState Primitives.ofAnonAddrs) = _
  rw [natAdd_ne_natBeq, natAdd_ne_natBle]
  rfl

theorem noDeltaNatArg (n : Nat) :
    (RecM.whnfNatReducerArg (RecM.natExprFromValue n)).run
      betaHarnessMethods (noAccelState Primitives.ofAnonAddrs) =
      .ok (some (RecM.natExprFromValue n))
        (noAccelState Primitives.ofAnonAddrs) := by
  unfold RecM.whnfNatReducerArg RecM.natExprFromValue
  rw [KExpr.mkNat_shape]
  rfl

private theorem noDeltaNatExtract (n : Nat) :
    extractNatLit (RecM.natExprFromValue n) Primitives.ofAnonAddrs =
      some n := by
  unfold extractNatLit RecM.natExprFromValue
  rw [KExpr.mkNat_shape]

private theorem noDeltaNatCompute :
    computeNatBin Primitives.ofAnonAddrs.natAdd.addr
      PrimAddrs.canonical 2 3 = some 5 := by
  rfl

theorem noDeltaNatAddProjectionMiss :
    (RecM.tryProjAppReduce noDeltaNatAddSource .FULL).run
      betaHarnessMethods (noAccelState Primitives.ofAnonAddrs) =
      .ok none (noAccelState Primitives.ofAnonAddrs) := by
  unfold RecM.tryProjAppReduce
  rw [noDeltaNatAddSpine]
  rfl

theorem noDeltaNatAddReduction :
    (RecM.tryReduceNatWithSuccMode noDeltaNatAddSource .collapse).run
      betaHarnessMethods (noAccelState Primitives.ofAnonAddrs) =
      .ok (some noDeltaNatAddResult)
        (noAccelState Primitives.ofAnonAddrs) := by
  unfold RecM.tryReduceNatWithSuccMode
  rw [noDeltaNatAddSpine]
  rw [KExpr.mkConst_shape]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (RecM.prims.run betaHarnessMethods) _
    (noAccelState Primitives.ofAnonAddrs) = _
  unfold EStateM.bind
  rw [show RecM.prims.run betaHarnessMethods
    (noAccelState Primitives.ofAnonAddrs) =
      .ok Primitives.ofAnonAddrs
        (noAccelState Primitives.ofAnonAddrs) from rfl]
  simp only
  rw [natAdd_ne_natSucc]
  simp only [Bool.false_and, Bool.false_eq_true, if_false, pure_bind]
  have hsize : ¬((#[RecM.natExprFromValue 2,
      RecM.natExprFromValue 3] : Array (KExpr .anon)).size < 2) := by decide
  simp only [hsize, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.isNatBinArithAddr Primitives.ofAnonAddrs.natAdd.addr).run
      betaHarnessMethods) _ (noAccelState Primitives.ofAnonAddrs) = _
  unfold EStateM.bind
  rw [noDeltaNatAddIsArith]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.isNatBinPredAddr Primitives.ofAnonAddrs.natAdd.addr).run
      betaHarnessMethods) _ (noAccelState Primitives.ofAnonAddrs) = _
  unfold EStateM.bind
  rw [noDeltaNatAddIsPred]
  simp only [Bool.not_true, Bool.not_false, Bool.false_and,
    Bool.false_eq_true, if_false, if_true]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.whnfNatReducerArg (RecM.natExprFromValue 2)).run
      betaHarnessMethods) _ (noAccelState Primitives.ofAnonAddrs) = _
  unfold EStateM.bind
  rw [noDeltaNatArg]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.whnfNatReducerArg (RecM.natExprFromValue 3)).run
      betaHarnessMethods) _ (noAccelState Primitives.ofAnonAddrs) = _
  unfold EStateM.bind
  rw [noDeltaNatArg]
  simp only
  rw [noDeltaNatExtract, noDeltaNatExtract]
  simp only
  rw [noDeltaNatCompute]
  simp [RecM.finishAppResult, noDeltaNatAddResult]

/-! #### Nat suffix reduction arbitrary Nat suffix witness -/

/-- An intentionally over-applied Nat primitive.  The third argument is not
consumed by `Nat.add`; production must rebuild it after reducing `2 + 3`. -/
def noDeltaNatAddSuffixSource : KExpr .anon :=
  KExpr.mkApp noDeltaNatAddSource betaArg

def noDeltaNatAddSuffixResult : KExpr .anon :=
  KExpr.mkApp noDeltaNatAddResult betaArg

theorem noDeltaNatAddSuffixSpine :
    noDeltaNatAddSuffixSource.collectSpine =
      (.mkConst Primitives.ofAnonAddrs.natAdd #[],
        #[RecM.natExprFromValue 2, RecM.natExprFromValue 3, betaArg]) := by
  unfold noDeltaNatAddSuffixSource noDeltaNatAddSource
  rw [KExpr.mkApp_shape]
  unfold KExpr.collectSpine
  rw [KExpr.collectSpine.go, KExpr.mkApp_shape,
    KExpr.collectSpine.go, KExpr.mkApp_shape,
    KExpr.collectSpine.go, KExpr.mkConst_shape]
  change
    (KExpr.const Primitives.ofAnonAddrs.natAdd #[]
        (KExpr.mkConst Primitives.ofAnonAddrs.natAdd #[]).info,
      (((#[].push betaArg).push (RecM.natExprFromValue 3)).push
        (RecM.natExprFromValue 2)).reverse) = _
  simp

/-- The sole dynamically rebuilt application is named in the finite request
list.  Starting the fold at either original argument cannot inhabit this
certificate. -/
def noDeltaNatAddSuffixRequests : List WalkerRequest :=
  [.internExpr noDeltaNatAddSuffixResult]

theorem noDeltaNatAddSuffixFinishRequests :
    RecM.FinishAppRequests noDeltaNatAddSuffixRequests
      (#[RecM.natExprFromValue 2, RecM.natExprFromValue 3, betaArg].extract
        2 3).toList
      noDeltaNatAddResult noDeltaNatAddSuffixResult := by
  change RecM.FinishAppRequests noDeltaNatAddSuffixRequests [betaArg]
    noDeltaNatAddResult noDeltaNatAddSuffixResult
  apply RecM.FinishAppRequests.cons
  · simp [noDeltaNatAddSuffixRequests, noDeltaNatAddSuffixResult]
  · simpa [noDeltaNatAddSuffixResult] using
      (RecM.FinishAppRequests.nil
        (requests := noDeltaNatAddSuffixRequests)
        noDeltaNatAddSuffixResult)

private theorem noDeltaNatAddSuffixIntern :
    ∃ s', TcM.intern noDeltaNatAddSuffixResult
        (noAccelState Primitives.ofAnonAddrs) =
      .ok noDeltaNatAddSuffixResult s' := by
  unfold TcM.intern TcM.runIntern noDeltaNatAddSuffixResult
  simp [internExprM, InternTable.internExpr, noAccelState, state,
    loadedEnv, KEnv.insert]

/-- Concrete Nat suffix reduction witness: the actual dispatcher reduces `(Nat.add 2 3) extra`
to `5 extra`, changes state only through the rebuilt application's intern,
and its successful execution admits the exhaustive general-spine trace. -/
theorem noDeltaNatAddSuffixReduction :
    ∃ s',
      (RecM.tryReduceNatWithSuccMode noDeltaNatAddSuffixSource .collapse).run
          betaHarnessMethods (noAccelState Primitives.ofAnonAddrs) =
        .ok (some noDeltaNatAddSuffixResult) s' ∧
      RecM.NatSpineSuccessTrace betaHarnessMethods .collapse
        noDeltaNatAddSuffixSource Primitives.ofAnonAddrs.natAdd #[]
        (KExpr.mkConst Primitives.ofAnonAddrs.natAdd #[]).info
        #[RecM.natExprFromValue 2, RecM.natExprFromValue 3, betaArg]
        (RecM.natExprFromValue 2) (RecM.natExprFromValue 3)
        (noAccelState Primitives.ofAnonAddrs) noDeltaNatAddSuffixResult s' := by
  obtain ⟨s', hintern⟩ := noDeltaNatAddSuffixIntern
  have hfinish :
      (RecM.finishAppResult noDeltaNatAddResult
        #[RecM.natExprFromValue 2, RecM.natExprFromValue 3, betaArg] 2).run
          betaHarnessMethods (noAccelState Primitives.ofAnonAddrs) =
        .ok noDeltaNatAddSuffixResult s' :=
    RecM.finishAppResult_one (by
      simpa [noDeltaNatAddSuffixResult] using hintern)
  have hrun := RecM.tryReduceNatWithSuccMode_binArithSuffixExact
    (natSuccMode := .collapse) (result := 5) (suffix := #[betaArg])
    (us := #[])
    (headInfo := (KExpr.mkConst Primitives.ofAnonAddrs.natAdd #[]).info)
    (args := #[RecM.natExprFromValue 2, RecM.natExprFromValue 3, betaArg])
    noDeltaNatAddSuffixSpine rfl rfl noDeltaNatAddIsArith
    noDeltaNatAddIsPred (noDeltaNatArg 2) (noDeltaNatArg 3)
    (noDeltaNatExtract 2) (noDeltaNatExtract 3) noDeltaNatCompute hfinish
  exact ⟨s', hrun,
    RecM.NatSpineSuccessTrace.complete (suffix := #[betaArg])
      noDeltaNatAddSuffixSpine rfl hrun⟩

/-- Nat suffix closure enriches the same observed success with its one finite suffix
request.  In particular, the certificate starts rebuilding from `5`, not
from either consumed argument. -/
theorem noDeltaNatAddSuffixCertifiedSuccess :
    ∃ s',
      RecM.NatSpineCertifiedSuccess noDeltaNatAddSuffixRequests
        betaHarnessMethods .collapse noDeltaNatAddSuffixSource
        Primitives.ofAnonAddrs.natAdd #[]
        (KExpr.mkConst Primitives.ofAnonAddrs.natAdd #[]).info
        #[RecM.natExprFromValue 2, RecM.natExprFromValue 3, betaArg]
        (RecM.natExprFromValue 2) (RecM.natExprFromValue 3)
        (noAccelState Primitives.ofAnonAddrs)
        noDeltaNatAddSuffixResult s' := by
  obtain ⟨s', hintern⟩ := noDeltaNatAddSuffixIntern
  have hfinish :
      (RecM.finishAppResult noDeltaNatAddResult
        #[RecM.natExprFromValue 2, RecM.natExprFromValue 3, betaArg] 2).run
          betaHarnessMethods (noAccelState Primitives.ofAnonAddrs) =
        .ok noDeltaNatAddSuffixResult s' :=
    RecM.finishAppResult_one (by
      simpa [noDeltaNatAddSuffixResult] using hintern)
  refine ⟨s', .arithmetic noDeltaNatAddIsArith noDeltaNatAddIsPred
    (noDeltaNatArg 2) (noDeltaNatArg 3) (noDeltaNatExtract 2)
    (noDeltaNatExtract 3) noDeltaNatCompute hfinish ?_⟩
  simpa [noDeltaNatAddResult] using noDeltaNatAddSuffixFinishRequests

/-- The universal-looking coverage interface remains execution-indexed:
determinism identifies any successful trace at this fixed source/state with
the single finitely certified run above. -/
theorem noDeltaNatAddSuffixFinishCoverage :
    RecM.NatSpineFinishCoverage noDeltaNatAddSuffixRequests
      betaHarnessMethods .collapse noDeltaNatAddSuffixSource
      Primitives.ofAnonAddrs.natAdd #[]
      (KExpr.mkConst Primitives.ofAnonAddrs.natAdd #[]).info
      #[RecM.natExprFromValue 2, RecM.natExprFromValue 3, betaArg]
      (RecM.natExprFromValue 2) (RecM.natExprFromValue 3)
      (noAccelState Primitives.ofAnonAddrs) := by
  intro result s' trace
  obtain ⟨certState, cert⟩ := noDeltaNatAddSuffixCertifiedSuccess
  have htraceRun := trace.eval (suffix := #[betaArg])
    noDeltaNatAddSuffixSpine rfl
  have hcertRun := cert.trace.eval (suffix := #[betaArg])
    noDeltaNatAddSuffixSpine rfl
  have heq := htraceRun.symm.trans hcertRun
  have hresultEq := Option.some.inj (EStateM.Result.ok.inj heq).1
  have hstateEq : s' = certState := (EStateM.Result.ok.inj heq).2
  subst result
  subst s'
  exact cert

/-! #### successor-collapse loop successor-collapse witness -/

/-- Closed literal argument for the production successor loop. -/
def succCollapseArg : KExpr .anon := RecM.natExprFromValue 2

/-- Exact one-argument canonical `Nat.succ` spine. -/
def succCollapseSource : KExpr .anon :=
  KExpr.mkApp
    (KExpr.mkConst Primitives.ofAnonAddrs.natSucc #[])
    succCollapseArg

def succCollapseResult : KExpr .anon := RecM.natExprFromValue 3

theorem succCollapseSpine :
    succCollapseSource.collectSpine =
      (KExpr.mkConst Primitives.ofAnonAddrs.natSucc #[],
        #[succCollapseArg]) := by
  unfold succCollapseSource
  rw [KExpr.mkApp_shape]
  unfold KExpr.collectSpine
  rw [KExpr.collectSpine.go, KExpr.mkConst_shape]
  rfl

/-- The linear-recognizer runs first and misses without invoking either
recursive callback on this literal argument. -/
theorem succCollapseLinearMiss :
    (RecM.tryReduceNatSuccLinearRec succCollapseArg 1).run
      betaHarnessMethods (noAccelState Primitives.ofAnonAddrs) =
      .ok none (noAccelState Primitives.ofAnonAddrs) := by
  unfold RecM.tryReduceNatSuccLinearRec RecM.natRecLiteralParts
    succCollapseArg RecM.natExprFromValue
  rw [KExpr.mkNat_shape]
  rfl

/-- The fixture callback is state-pure and exposes the same literal. -/
theorem succCollapseWhnf :
    (RecM.whnfModeRec succCollapseArg .stuck).run
      betaHarnessMethods (noAccelState Primitives.ofAnonAddrs) =
      .ok succCollapseArg (noAccelState Primitives.ofAnonAddrs) := by
  rfl

theorem succCollapseExtract :
    extractNatLit succCollapseArg Primitives.ofAnonAddrs = some 2 := by
  unfold succCollapseArg RecM.natExprFromValue extractNatLit
  rw [KExpr.mkNat_shape]

/-- The named production step follows linear miss, callback success, then
literal hit and terminates before successor classification or memo writes. -/
theorem succCollapseStep :
    (RecM.tryReduceNatSuccIterStep
      (succCollapseArg, 1,
        #[(succCollapseArg.addr, emptyCtxAddr)])).run betaHarnessMethods
      (noAccelState Primitives.ofAnonAddrs) =
      .ok (.done (some succCollapseResult))
        (noAccelState Primitives.ofAnonAddrs) := by
  apply RecM.tryReduceNatSuccIterStep_afterWhnf succCollapseLinearMiss
    succCollapseWhnf
  simpa [succCollapseResult] using
    (RecM.tryReduceNatSuccAfterWhnf_literal
      (methods := betaHarnessMethods)
      (s := noAccelState Primitives.ofAnonAddrs)
      (w := succCollapseArg) (offset := 1)
      (visited := #[(succCollapseArg.addr, emptyCtxAddr)])
      (p := Primitives.ofAnonAddrs) rfl succCollapseExtract)

theorem succCollapseKey :
    TcM.whnfKey succCollapseArg (noAccelState Primitives.ofAnonAddrs) =
      .ok (succCollapseArg.addr, emptyCtxAddr)
        (noAccelState Primitives.ofAnonAddrs) := by
  apply TcM.whnfKey_closed
  rfl

theorem succCollapseMemoMiss :
    (noAccelState Primitives.ofAnonAddrs).env.natSuccStuck.contains
      (succCollapseArg.addr, emptyCtxAddr) = false := by
  simp [noAccelState, state, loadedEnv, KEnv.insert]

/-- The real bounded driver executes one `.done` iteration from the exact
closed key and leaves the state—and in particular the stuck memo—unchanged. -/
theorem succCollapseIter :
    (RecM.tryReduceNatSuccIter succCollapseArg).run betaHarnessMethods
      (noAccelState Primitives.ofAnonAddrs) =
      .ok (some succCollapseResult)
        (noAccelState Primitives.ofAnonAddrs) := by
  rw [RecM.tryReduceNatSuccIter_entryMiss succCollapseKey
    succCollapseMemoMiss]
  rw [show maxWhnfFuel.toNat = 10000 by rfl]
  rw [RecM.runBounded, ReaderT.run_bind]
  change EStateM.bind
    ((RecM.tryReduceNatSuccIterStep
      (succCollapseArg, 1, #[(succCollapseArg.addr, emptyCtxAddr)])).run
        betaHarnessMethods) _ (noAccelState Primitives.ofAnonAddrs) = _
  unfold EStateM.bind
  rw [succCollapseStep]
  rfl

/-- End-to-end successor-collapse loop branch witness: canonical `Nat.succ 2` collapses to the
literal `3` through the production dispatcher, bounded loop, and callback
order, with no cache or intern mutation. -/
theorem succCollapseReduction :
    (RecM.tryReduceNatWithSuccMode succCollapseSource .collapse).run
      betaHarnessMethods (noAccelState Primitives.ofAnonAddrs) =
      .ok (some succCollapseResult)
        (noAccelState Primitives.ofAnonAddrs) := by
  apply RecM.tryReduceNatWithSuccMode_succ_collapse
    (p := Primitives.ofAnonAddrs) (arg := succCollapseArg)
  · exact succCollapseSpine
  · rfl
  · rfl
  · exact succCollapseIter

/-- The same concrete unary successor is an exact state-pure miss in the
internal stuck policy.  This witnesses the branch used by recursive successor
normalization and guards against accidentally re-entering collapse mode. -/
theorem succStuckReduction :
    (RecM.tryReduceNatWithSuccMode succCollapseSource .stuck).run
      betaHarnessMethods (noAccelState Primitives.ofAnonAddrs) =
      .ok none (noAccelState Primitives.ofAnonAddrs) := by
  exact RecM.tryReduceNatWithSuccMode_succ_stuck succCollapseSpine rfl rfl

/-- Adversarial precedence witness: projection-app and BitVec miss, Nat.add
succeeds, and the production tail returns immediately.  Any reordering that
moves Nat behind native/string/projection/quotient invalidates this exact
execution equation. -/
theorem noDeltaNatBranchOrder :
    (RecM.whnfNoDeltaReducersStep .FULL .collapse
      noDeltaNatAddSource).run betaHarnessMethods
        (noAccelState Primitives.ofAnonAddrs) =
      .ok (.next noDeltaNatAddResult)
        (noAccelState Primitives.ofAnonAddrs) := by
  apply RecM.whnfNoDeltaReducersStep_nat
  · exact RecM.tryProjAppReduceFinished_none
      noDeltaNatAddProjectionMiss
  · exact RecM.tryReduceBitvec_noAccel rfl noDeltaNatAddSource
  · exact noDeltaNatAddReduction

private theorem driverCacheWhnfValid (kind : ExprCacheKind)
    (hkind : kind = .whnf ∨ kind = .whnfNoDelta ∨
      kind = .whnfNoDeltaCheap) :
    WhnfCacheValid whnfContextKeys RawProjRel.none
      CacheSemantics.blockErrorsOnly (CacheAuthority.stable worldGood)
      coreCacheSupport (.expr kind coreCacheKey betaArg) := by
  rcases hkind with rfl | rfl | rfl <;>
    intro source hsource haddr Δ hctx _hscoped
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
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
      coreCacheSupport 0 [] (fullNoDeltaWarmState prims) := by
  exact RecM.WhnfDriverCacheUpdate.noDelta_whnfStateInv
    (fullCoreWarmStateInv prims) fullNoDeltaProvenance

theorem noDeltaTrace (prims : Primitives .anon) :
    RecM.WhnfNoDeltaTrace .structuralNoAccel whnfSemantics RawProjRel.none worldGood
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
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullCoreWarmState prims) ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullNoDeltaWarmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  simpa [whnfContextKeys, WhnfContextKeys.closed, betaSource, KExpr.mkApp, RecM.whnfNoDelta, whnfSemantics, fullNoDeltaWarmState] using
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
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullNoDeltaWarmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  simpa [whnfContextKeys, WhnfContextKeys.closed, betaSource, KExpr.mkApp, RecM.whnfNoDelta, whnfSemantics] using
    (RecM.whnfNoDeltaImpl_fullHit_acceptance
      (keys := whnfContextKeys) (fallback := CacheSemantics.blockErrorsOnly)
      (.direct RecM.WhnfDriverNonLeaf.app) rfl
      (coreCacheKey_eval (fullNoDeltaWarmState prims))
      (betaTransientFalse (fullNoDeltaWarmState prims))
      (fullNoDeltaWarm_hit prims) (fullNoDeltaWarmStateInv prims) (.inl rfl)
      (coreCacheKey_matches (fullNoDeltaWarmState prims)
        (fullNoDeltaWarmStateInv prims).2.1)
      structuralBetaSource_tr.contextScoped)

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
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
      coreCacheSupport 0 [] (fullWhnfChargedState prims) := by
  exact WhnfStateInv.of_semantic_fields_eq
    (fullNoDeltaWarmStateInv prims) rfl rfl rfl rfl rfl rfl rfl rfl

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
    simpa [KEnv.get?, fullWhnfChargedState, fullNoDeltaWarmState, fullCoreWarmState,
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
    RecM.WhnfFullTrace .structuralNoAccel whnfSemantics RawProjRel.none worldGood
      coreCacheSupport 0 [] betaHarnessMethods .collapse
      maxWhnfFuel.toNat (betaSource, {}) (fullWhnfChargedState prims)
      betaArg (fullWhnfChargedState prims) := by
  rw [show maxWhnfFuel.toNat = 10000 by rfl]
  exact .done (fullWhnfChargedStateInv prims) (betaFullWhnfStep prims)
    (fullWhnfChargedStateInv prims) betaResultMeaning

/-! #### total-outcome boundary total-outcome boundary witnesses -/

/-- No-delta exhaustion happens before the first semantic step and cannot be
    repackaged as a successful trace. -/
theorem noDeltaZeroFuel (prims : Primitives .anon) :
    (RecM.runBounded (RecM.whnfNoDeltaImplStep .FULL .collapse) 0
      betaSource).run betaHarnessMethods (fullCoreWarmState prims) =
        .error .maxRecDepth (fullCoreWarmState prims) ∧
      ¬RecM.WhnfNoDeltaTrace .structuralNoAccel whnfSemantics RawProjRel.none
        worldGood coreCacheSupport 0 [] betaHarnessMethods .FULL .collapse 0
        betaSource (fullCoreWarmState prims) betaArg
        (fullCoreWarmState prims) :=
  ⟨rfl, RecM.WhnfNoDeltaTrace.no_zero⟩

/-- Full-WHNF has the same hostile zero-fuel boundary even though its loop
    state also carries a cycle-detection set. -/
theorem fullWhnfZeroFuel (prims : Primitives .anon) :
    (RecM.runBounded (RecM.whnfWithNatSuccModeStep .collapse) 0
      (betaSource, {})).run betaHarnessMethods (fullWhnfChargedState prims) =
        .error .maxRecDepth (fullWhnfChargedState prims) ∧
      ¬RecM.WhnfFullTrace .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] betaHarnessMethods .collapse 0
        (betaSource, {}) (fullWhnfChargedState prims) betaArg
        (fullWhnfChargedState prims) :=
  ⟨rfl, RecM.WhnfFullTrace.no_zero⟩

/-- The loop-error contract does not identify method/fuel exhaustion
    (`.maxRecFuel`) with bounded-loop exhaustion (`.maxRecDepth`). -/
theorem whnfLoopErrorSeparation (prims : Primitives .anon) :
    RecM.WhnfLoopError (fun _ _ => False) .maxRecDepth
        (fullWhnfChargedState prims) ∧
      ¬RecM.WhnfLoopError (fun _ _ => False) .maxRecFuel
        (fullWhnfChargedState prims) := by
  constructor
  · exact Or.inl rfl
  · rintro (h | h)
    · cases h
    · exact h

/-- The exact state after the full driver commits its semantic cache entry. -/
def fullWhnfWarmState (prims : Primitives .anon) : TcState .anon :=
  let s := fullWhnfChargedState prims
  {s with env := {s.env with
    whnfCache := s.env.whnfCache.insert coreCacheKey betaArg}}

theorem fullWhnfWarmStateInv (prims : Primitives .anon) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
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
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullWhnfChargedState prims) ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullWhnfWarmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  simpa [whnfContextKeys, WhnfContextKeys.closed, betaSource, KExpr.mkApp, RecM.whnf, whnfSemantics, fullWhnfWarmState] using
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
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        coreCacheSupport 0 [] (fullWhnfWarmState prims) ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] betaSource betaArg := by
  simpa [whnfContextKeys, WhnfContextKeys.closed, betaSource, KExpr.mkApp, RecM.whnf, whnfSemantics] using
    (RecM.whnfWithNatSuccMode_hit_acceptance
      (keys := whnfContextKeys) (fallback := CacheSemantics.blockErrorsOnly)
      (.direct RecM.WhnfDriverNonLeaf.app) (fullWhnfPrefixWarm prims)
      (coreCacheKey_eval (fullWhnfWarmState prims))
      (betaTransientFalse (fullWhnfWarmState prims))
      (fullWhnfWarm_hit prims) (fullWhnfWarmStateInv prims) (.inl rfl)
      (coreCacheKey_matches (fullWhnfWarmState prims)
        (fullWhnfWarmStateInv prims).2.1)
      structuralBetaSource_tr.contextScoped)

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

/-! ### regular-binder fallback regular-binder fallback witnesses -/

/-- The fallback fixture includes both open variable forms as well as the
    original support root used by the concrete state's intern invariant. -/
def stuckSupport : RunSupport where
  expr e := support e ∨ e = betaBody ∨ e = fvarZetaSource
  exprFinite := ⟨[supportExpr, betaBody, fvarZetaSource], by
    intro e he
    rcases he with he | he | he
    · change e = supportExpr at he
      subst e
      simp
    · subst e
      simp
    · subst e
      simp⟩
  univ := support.univ
  univFinite := support.univFinite

theorem support_le_stuckSupport : support ≤ stuckSupport := by
  constructor
  · intro e he
    exact .inl he
  · intro u hu
    exact hu

/-- A legacy bvar over a regular lambda frame.  Its concrete `letVals`
    entry is `none`, while the ghost context still resolves and translates
    the variable normally. -/
def bvarStuckCtx : KVLCtx :=
  [(none, .vlam (.const natName []))]

def bvarStuckState (prims : Primitives .anon) : TcState .anon :=
  let base := noAccelState prims
  { base with
    ctx := #[supportExpr]
    letVals := #[none] }

theorem bvarStuckCtxRecon (prims : Primitives .anon) :
    CtxRecon worldGood.venv 0 worldGood.nameOf RawProjRel.none
      (bvarStuckState prims) bvarStuckCtx := by
  refine {
    size_eq := rfl
    recon := ?_
    lwf := .empty
    incr := by simp [bvarStuckState, noAccelState, state]
    fresh := by simp [bvarStuckState, noAccelState, state]
    lets := rfl }
  have hrec :
      CtxRecon' worldGood.venv 0 worldGood.nameOf RawProjRel.none
        [(supportExpr, none)] [] bvarStuckCtx :=
    .bvar_lam .nil betaTy_tr ⟨_, betaA_type⟩
  simpa [state, bvarStuckState, noAccelState] using hrec

theorem bvarStuckStateInv (prims : Primitives .anon) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
      stuckSupport 0 bvarStuckCtx (bvarStuckState prims) := by
  have hbase := noAccelStateInv prims
  refine ⟨?_, bvarStuckCtxRecon prims, rfl⟩
  apply KernelStateWF.of_no_cache_entries
  · exact hbase.1.core.of_env_eq rfl
  · exact hbase.1.internSupport.mono support_le_stuckSupport
  · rfl
  · intro entry
    simpa [bvarStuckState, noAccelState, state] using
      loadedEnv_noCacheEntries entry

theorem bvarStuckLookup (prims : Primitives .anon) :
    TcM.lookupLetVal 0 (bvarStuckState prims) =
      .ok none (bvarStuckState prims) := by
  unfold TcM.lookupLetVal
  rfl

theorem bvarStuckSource :
    RecM.WhnfStep.Source RawProjRel.none worldGood stuckSupport 0
      bvarStuckCtx id betaBody := by
  refine ⟨?_, .bvar 0, ?_⟩
  · exact .inr (.inl rfl)
  · simpa [bvarStuckCtx] using betaBody_tr

/-- Adversarial legacy-binder acceptance: the translated variable is
    semantically meaningful but structurally stuck, and the complete step is
    state-pure. -/
theorem bvarStuckAcceptance (prims : Primitives .anon)
    (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep betaBody flags).run betaHarnessMethods
        (bvarStuckState prims) =
          .ok (.done betaBody) (bvarStuckState prims) ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        stuckSupport 0 bvarStuckCtx (bvarStuckState prims) ∧
      RecM.WhnfStep.Meaning RawProjRel.none worldGood stuckSupport 0
        bvarStuckCtx id betaBody (.done betaBody) := by
  unfold betaBody
  rw [KExpr.mkVar_shape]
  exact RecM.whnfCoreWithFlagsStep_varDone_acceptance structuralWhnfTheory
    bvarStuckSource (bvarStuckStateInv prims) (bvarStuckLookup prims)

/-- The fvar-side adversary uses a real regular local declaration, not a
    missing id.  Production must distinguish `.cdecl` from `.ldecl`. -/
def fvarStuckCtx : KVLCtx :=
  [(some (fvarZetaId, []), .vlam (.const natName []))]

def fvarStuckState (prims : Primitives .anon) : TcState .anon :=
  let base := noAccelState prims
  { base with
    env := { base.env with nextFVarId := 1 }
    lctx := base.lctx.push fvarZetaId (.cdecl () () supportExpr) }

theorem fvarStuckFind (prims : Primitives .anon) :
    (fvarStuckState prims).lctx.find? fvarZetaId =
      some (.cdecl () () supportExpr) := by
  simp [fvarStuckState, noAccelState, LocalContext.find?, LocalContext.push,
    fvarZetaId]

theorem fvarStuckCtxRecon (prims : Primitives .anon) :
    CtxRecon worldGood.venv 0 worldGood.nameOf RawProjRel.none
      (fvarStuckState prims) fvarStuckCtx := by
  refine {
    size_eq := rfl
    recon := ?_
    lwf := ?_
    incr := by
      simp [fvarStuckState, noAccelState, state, LocalContext.push]
    fresh := ?_
    lets := rfl }
  · have hrec :
        CtxRecon' worldGood.venv 0 worldGood.nameOf RawProjRel.none
          [] [(fvarZetaId, .cdecl () () supportExpr)] fvarStuckCtx :=
      .fvar .nil (.vlam betaTy_tr ⟨_, betaA_type⟩) (by simp)
    simpa [state, fvarStuckState, noAccelState, LocalContext.push] using hrec
  · apply LocalContext.WF.push .empty
    simp [fvarZetaId]
  · intro p hp
    simp [fvarStuckState, noAccelState, state, LocalContext.push] at hp
    subst p
    simp [fvarStuckState, fvarZetaId]

theorem fvarStuckStateInv (prims : Primitives .anon) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
      stuckSupport 0 fvarStuckCtx (fvarStuckState prims) := by
  have hbase := noAccelStateInv prims
  refine ⟨?_, fvarStuckCtxRecon prims, rfl⟩
  apply KernelStateWF.of_no_cache_entries
  · exact hbase.1.core.of_consts_eq (by rfl) (by
      simpa [fvarStuckState] using hbase.1.core.intern)
  · exact (by
      simpa [fvarStuckState] using
        hbase.1.internSupport.mono support_le_stuckSupport)
  · rfl
  · intro entry
    intro hentry
    apply loadedEnv_noCacheEntries entry
    cases hentry <;> (constructor; assumption)

theorem fvarStuckSource_tr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none
      fvarStuckCtx fvarZetaSource (.bvar 0) := by
  unfold fvarZetaSource
  rw [KExpr.mkFVar_shape]
  exact .fvar rfl

theorem fvarStuckSource :
    RecM.WhnfStep.Source RawProjRel.none worldGood stuckSupport 0
      fvarStuckCtx id fvarZetaSource := by
  exact ⟨.inr (.inr rfl), _, fvarStuckSource_tr⟩

/-- Adversarial regular-fvar acceptance: the `.cdecl` lookup is present and
    translated, yet no zeta reduction occurs. -/
theorem fvarStuckAcceptance (prims : Primitives .anon)
    (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep fvarZetaSource flags).run betaHarnessMethods
        (fvarStuckState prims) =
          .ok (.done fvarZetaSource) (fvarStuckState prims) ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        stuckSupport 0 fvarStuckCtx (fvarStuckState prims) ∧
      RecM.WhnfStep.Meaning RawProjRel.none worldGood stuckSupport 0
        fvarStuckCtx id fvarZetaSource (.done fvarZetaSource) := by
  apply RecM.whnfCoreWithFlagsStep_fvarDone_acceptance structuralWhnfTheory
    fvarStuckSource (fvarStuckStateInv prims)
  intro declName ty val h
  rw [fvarStuckFind prims] at h
  cases h

/-! ### stuck-reduction fallback projection and unchanged-head application fallbacks -/

/-- A well-typed constructor-headed application is not an iota redex.  This
exercises the general application fallback with a non-lambda head and a real
argument spine. -/
def appStuckHead : KExpr .anon := KExpr.mkConst succId #[] ()
def appStuckSource : KExpr .anon := KExpr.mkApp appStuckHead betaArg

def fallbackSupport : RunSupport where
  expr e := stuckSupport e ∨ e = appStuckSource
  exprFinite := stuckSupport.exprFinite.union
    (FiniteSupport.singleton appStuckSource)
  univ := stuckSupport.univ
  univFinite := stuckSupport.univFinite

theorem stuckSupport_le_fallbackSupport : stuckSupport ≤ fallbackSupport := by
  exact ⟨fun _ h => .inl h, fun _ h => h⟩

theorem fallbackStateInv (prims : Primitives .anon) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
      fallbackSupport 0 [] (noAccelState prims) := by
  have hbase := noAccelStateInv prims
  refine ⟨?_, hbase.2.1, hbase.2.2⟩
  apply KernelStateWF.of_no_cache_entries
  · exact hbase.1.core
  · exact hbase.1.internSupport.mono
      (RunSupport.le_trans support_le_stuckSupport
        stuckSupport_le_fallbackSupport)
  · rfl
  · intro entry
    simpa [noAccelState, state] using loadedEnv_noCacheEntries entry

theorem appStuckHead_tr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
      appStuckHead (.const succName []) := by
  rw [appStuckHead, KExpr.mkConst_shape]
  exact .const (ci := succConstant) nameOf_succ
    (by simpa [worldGood, goodEnv, goodName, succName] using natEnv_succ)
    (by intro l hl; simp at hl) rfl

theorem appStuckHead_type :
    worldGood.venv.HasType 0 [] (.const succName [])
      (.forallE (.const natName []) (.const natName [])) := by
  exact Lean4Lean.VEnv.HasType.const (env := worldGood.venv)
    (U := 0) (Γ := []) (ci := succConstant) (ls := [])
    (by simpa [worldGood, goodEnv, goodName, succName] using natEnv_succ)
    (by intro l hl; simp at hl) rfl

theorem appStuckHead_iotaNonLambda : IotaArgNonLambda appStuckHead := by
  unfold appStuckHead
  rw [KExpr.mkConst_shape]
  exact .const

theorem appStuckSource_tr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
      appStuckSource
      (.app (.const succName []) (.const zeroName [])) := by
  rw [appStuckSource, KExpr.mkApp_shape]
  exact .app appStuckHead_type betaArg_type appStuckHead_tr betaArg_tr

/-- The transient non-lambda branch is inhabited by `Nat.succ Nat.zero`.
Production rebuilds the exact application without touching state, and the
result retains reflexive Theory meaning. -/
theorem appStuckIotaTransient (methods : Methods .anon) (s : TcState .anon) :
    (RecM.applyIotaArg appStuckHead betaArg true).run methods s =
        .ok appStuckSource s ∧
      WhnfMeaning RawProjRel.none worldGood 0 []
        appStuckSource appStuckSource := by
  have h := RecM.applyIotaArg_true_nonlam_semantic
    (sourceInfo := (KExpr.mkApp appStuckHead betaArg).info)
    appStuckHead_iotaNonLambda methods s appStuckHead_type betaArg_type
    appStuckHead_tr betaArg_tr
  simpa [← KExpr.mkApp_shape, appStuckSource] using h

theorem appStuckSourceWitness :
    RecM.WhnfStep.Source RawProjRel.none worldGood fallbackSupport 0 []
      id appStuckSource := by
  exact ⟨.inr rfl, _, appStuckSource_tr⟩

theorem appStuckSpine :
    appStuckSource.collectSpine = (appStuckHead, #[betaArg]) := by
  unfold appStuckSource appStuckHead
  rw [KExpr.mkApp_shape, KExpr.mkConst_shape]
  rfl

theorem appStuckHeadWhnf (prims : Primitives .anon) (flags : WhnfFlags) :
    betaHarnessMethods.whnfCoreFlags appStuckHead flags
        (noAccelState prims) =
      .ok appStuckHead (noAccelState prims) := rfl

theorem appStuckHeadSelf : (appStuckHead != appStuckHead) = false := by
  change Bool.not (appStuckHead.info.addr == appStuckHead.info.addr) = false
  rw [beq_self_eq_true]
  rfl

theorem appStuckIota (prims : Primitives .anon) (flags : WhnfFlags) :
    (RecM.tryIotaWithFlags appStuckSource flags).run betaHarnessMethods
        (noAccelState prims) =
      .ok none (noAccelState prims) := by
  unfold RecM.tryIotaWithFlags appStuckSource appStuckHead
  rw [KExpr.mkApp_shape, KExpr.mkConst_shape]
  simp only [KExpr.collectSpine, KExpr.collectSpine.go]
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst succId) _ (noAccelState prims) = _
  unfold EStateM.bind
  rw [tryGetConst_succ_k1e]
  rfl

/-- Non-vacuous application fallback acceptance: the source is translated
and well typed, but the constructor head is unchanged and iota misses. -/
theorem appStuckAcceptance (prims : Primitives .anon)
    (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep appStuckSource flags).run
        betaHarnessMethods (noAccelState prims) =
          .ok (.done appStuckSource) (noAccelState prims) ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        fallbackSupport 0 [] (noAccelState prims) ∧
      RecM.WhnfStep.Meaning RawProjRel.none worldGood fallbackSupport 0 []
        id appStuckSource (.done appStuckSource) := by
  unfold appStuckSource at *
  rw [KExpr.mkApp_shape] at *
  apply RecM.whnfCoreWithFlagsStep_appUnchangedDone_acceptance
    structuralWhnfTheory appStuckSourceWitness (fallbackStateInv prims)
    appStuckSpine .const (appStuckHeadWhnf prims flags)
    appStuckHeadSelf (appStuckIota prims flags)

/-! The projection-miss fixture cannot use `RawProjRel.none`: that would make
its source-translation premise impossible.  This identity interpretation is
nonempty and closed under every structural translation operation. -/
namespace ProjectionFallback

def projectionName : Lean.Name := `Ix.Tc.Verify.projectionFallback

def projectionRel : RawProjRel :=
  fun _ _ _ _ value result => result = value

theorem projectionRel_ok :
    TrProjOK Lean4Lean.VEnv.empty 0 projectionRel := by
  refine {
    weakN := ?_
    instN := ?_
    wf := ?_
    uniq := ?_
    defeqDFC := ?_
    instL := ?_
    monoU := ?_ }
  · intro Γ Γ' n k s i e e' hlift hrel
    subst e'
    rfl
  · intro Γ₀ e₀ A₀ k Γ₁ Γ s i e e' htype hinst hrel
    subst e'
    rfl
  · intro Γ s i e e' hrel hwf
    subst e'
    exact hwf
  · intro Γ₁ Γ₂ s i e₁ e₂ e₁' e₂' hctx h₁ h₂ hdefeq
    subst e₁'
    subst e₂'
    exact hdefeq
  · intro Γ₁ Γ₂ s i e₁ e₂ e' hctx hdefeq hrel
    subst e'
    exact ⟨e₂, rfl⟩
  · intro U U' ls Γ s i e e' hlevels hrel
    subst e'
    rfl
  · intro U U' Γ s i e e' hle hctx hrel
    subst e'
    rfl

def world : VerifyWorld where
  catalog := Catalog.empty
  trusted := fun _ => False
  venv := .empty
  nameOf := fun addr =>
    if addr == AmbientNat.natAddress then some projectionName else none
  venvWF := ⟨[], .empty⟩
  trustedCatalogued := fun h => False.elim h

def value : KExpr .anon := KExpr.mkSort AmbientNat.zeroLevel
def source : KExpr .anon := KExpr.mkPrj AmbientNat.natId 0 value
def support : RunSupport := RunSupport.singleton source
def state : TcState .anon :=
  { TcState.ofEnvAnon ({} : KEnv .anon) with noAccel := true }

theorem trustedCatalog : TrustedCatalogRel projectionRel world := by
  exact TrustedCatalogLog.empty

theorem stateCore : TcStateWF projectionRel state world := by
  refine ⟨trustedCatalog, ?_, ?_⟩
  · exact LoadedAgrees.empty Catalog.empty
  · exact InternTable.WF.empty

theorem stateInv :
    WhnfStateInv .noAccel CacheSemantics.blockErrorsOnly projectionRel world
      support 0 [] state := by
  refine ⟨?_, ?_, rfl, Primitives.ofAnonAddrs_canonical⟩
  · apply KernelStateWF.of_no_cache_entries stateCore
    · constructor
      · intro x hx
        obtain ⟨addr, haddr⟩ := hx
        simp [state, TcState.ofEnvAnon] at haddr
      · intro u hu
        obtain ⟨addr, haddr⟩ := hu
        simp [state, TcState.ofEnvAnon] at haddr
    · rfl
    · intro entry hentry
      cases hentry <;> simp [state, TcState.ofEnvAnon] at *
  · apply CtxRecon.empty <;> rfl

def theory : WhnfTheory projectionRel world 0 where
  literalWF := by
    intro literal hliteral
    cases literal <;>
      simp [Lean4Lean.VEnv.ContainsLits, Lean4Lean.VEnv.contains,
        Lean4Lean.VEnv.empty, world]
        at hliteral
  projections := projectionRel_ok

theorem nameOf_projection :
    world.nameOf AmbientNat.natAddress = some projectionName := by
  simp [world]

theorem value_tr :
    TrKExprS world.venv 0 world.nameOf projectionRel [] value
      (.sort .zero) := by
  unfold value AmbientNat.zeroLevel
  rw [KExpr.mkSort_shape]
  exact .sort trivial

theorem source_tr :
    TrKExprS world.venv 0 world.nameOf projectionRel [] source
      (.sort .zero) := by
  unfold source
  rw [KExpr.mkPrj_shape]
  exact .prj nameOf_projection value_tr rfl

theorem sourceWitness :
    RecM.WhnfStep.Source projectionRel world support 0 [] id source := by
  exact ⟨rfl, _, source_tr⟩

theorem valueWhnf (flags : WhnfFlags) :
    (if flags.cheapProj then
        (RecM.whnfCoreFlagsRec value flags).run
          AmbientNat.betaHarnessMethods state
      else (RecM.whnfRec value).run AmbientNat.betaHarnessMethods state) =
      .ok value state := by
  cases flags.cheapProj <;>
    simp [RecM.whnfCoreFlagsRec, RecM.whnfRec,
      AmbientNat.betaHarnessMethods] <;> rfl

theorem reduceMiss :
    (RecM.tryProjReduce AmbientNat.natId 0 value).run
        AmbientNat.betaHarnessMethods state = .ok none state := by
  rw [RecM.tryProjReduce_eq, RecM.tryProjPrepare_eq]
  unfold value
  rw [KExpr.mkSort_shape]
  rw [ReaderT.run_bind]
  unfold RecM.tryProjReduceTail
  simp only
  rw [ReaderT.run_pure, pure_bind]
  change EStateM.bind
    (ReaderT.run
      (RecM.tryReduceFinValDecidableRec AmbientNat.natId 0
        (.sort AmbientNat.zeroLevel
          (KExpr.mkSort AmbientNat.zeroLevel).info) #[])
      AmbientNat.betaHarnessMethods) _ state = _
  unfold EStateM.bind
  rw [RecM.tryReduceFinValDecidableRec_noAccel rfl]

/-- Non-vacuous projection fallback acceptance: the source translates under
the live projection relation, the value callback succeeds, and the production
helper nevertheless returns `none` without changing state. -/
theorem acceptance (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep source flags).run
        AmbientNat.betaHarnessMethods state = .ok (.done source) state ∧
      WhnfStateInv .noAccel CacheSemantics.blockErrorsOnly projectionRel world
        support 0 [] state ∧
      RecM.WhnfStep.Meaning projectionRel world support 0 [] id source
        (.done source) := by
  unfold source at *
  rw [KExpr.mkPrj_shape] at *
  exact RecM.whnfCoreWithFlagsStep_projectionDone_acceptance theory
    sourceWitness stateInv (valueWhnf flags) reduceMiss

end ProjectionFallback

/-! ### application rebuilding multi-beta and changed-head rebuilding -/

/-- A three-argument redex whose first two arguments feed two lambdas while
the third remains to be rebuilt.  The body selects the outer function
argument, so production must reverse the consumed substitution vector:
`#[Nat.zero, Nat.succ]` maps `var 1` to `Nat.succ`. -/
def multiBetaFunTy : KExpr .anon :=
  KExpr.mkAll () () supportExpr supportExpr
def multiBetaBody : KExpr .anon := KExpr.mkVar 1 ()
def multiBetaInner : KExpr .anon :=
  KExpr.mkLam () () supportExpr multiBetaBody
def multiBetaLam : KExpr .anon :=
  KExpr.mkLam () () multiBetaFunTy multiBetaInner
def multiBetaSource : KExpr .anon :=
  KExpr.mkApp
    (KExpr.mkApp (KExpr.mkApp multiBetaLam appStuckHead) betaArg)
    betaArg

set_option maxHeartbeats 800000 in
theorem multiBetaSpine :
    multiBetaSource.collectSpine =
      (multiBetaLam, #[appStuckHead, betaArg, betaArg]) := by
  unfold multiBetaSource multiBetaLam
  rw [KExpr.mkApp_shape, KExpr.mkApp_shape, KExpr.mkApp_shape]
  rw [KExpr.mkLam_shape]
  simp [KExpr.collectSpine, KExpr.collectSpine.go]

theorem multiBetaConsume :
    RecM.consumeBetaLams multiBetaLam
      #[appStuckHead, betaArg, betaArg] =
        (multiBetaBody, #[appStuckHead, betaArg]) := by
  unfold multiBetaLam multiBetaInner
  rw [KExpr.mkLam_shape, KExpr.mkLam_shape]
  rfl

/-- Exact argument-order witness for the real simultaneous-substitution
walker.  Swapping the array entries would return `betaArg`, not
`appStuckHead`. -/
theorem multiBetaWalker (it : InternTable .anon) :
    simulSubst multiBetaBody #[betaArg, appStuckHead] 0 it =
      (appStuckHead, it) := by
  unfold multiBetaBody simulSubst
  rw [KExpr.mkVar_lbr]
  rw [KExpr.mkVar_shape]
  have hlbr :
      (KExpr.var 1 () (KExpr.mkVar (m := .anon) 1 ()).info).lbr = 2 := by
    rw [← KExpr.mkVar_shape]
    rfl
  unfold runWalk simulSubstCached scratchGet? scratchInsert liftInternW lift
  simp [stateM_bind, stateM_map, stateM_pure, hlbr]

theorem multiNatTr (Δ : KVLCtx) :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none Δ
      supportExpr (.const natName []) := by
  rw [supportExpr_eq_mkConst, KExpr.mkConst_shape]
  exact .const (ci := natConstant) nameOf_nat
    (by simpa [worldGood, goodEnv, goodName, natName] using natEnv_nat)
    (by intro l hl; simp at hl) rfl

theorem multiNatType (Γ : List Lean4Lean.VExpr) :
    worldGood.venv.HasType 0 Γ (.const natName [])
      (.sort (.succ .zero)) := by
  exact Lean4Lean.VEnv.HasType.const (env := worldGood.venv)
    (U := 0) (Γ := Γ) (ci := natConstant) (ls := [])
    (by simpa [worldGood, goodEnv, goodName, natName] using natEnv_nat)
    (by intro l hl; simp at hl) rfl

theorem multiBetaFunTyTr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
      multiBetaFunTy
      (.forallE (.const natName []) (.const natName [])) := by
  unfold multiBetaFunTy
  rw [KExpr.mkAll_shape]
  exact .all ⟨_, multiNatType []⟩
    ⟨_, multiNatType [(.const natName [])]⟩
    (multiNatTr [])
    (multiNatTr [(none, .vlam (.const natName []))])

theorem multiBetaFunType (Γ : List Lean4Lean.VExpr) :
    worldGood.venv.HasType 0 Γ
      (.forallE (.const natName []) (.const natName []))
      (.sort ((Lean4Lean.VLevel.succ .zero).imax
        (Lean4Lean.VLevel.succ .zero))) :=
  Lean4Lean.VEnv.HasType.forallE (multiNatType Γ)
    (multiNatType ((.const natName []) :: Γ))

theorem multiBetaBodyTr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none
      [(none, .vlam (.const natName [])),
        (none, .vlam (.forallE (.const natName []) (.const natName [])))]
      multiBetaBody (.bvar 1) := by
  rw [multiBetaBody, KExpr.mkVar_shape]
  exact .var rfl

theorem multiBetaBodyType :
    worldGood.venv.HasType 0
      [(.const natName []),
        (.forallE (.const natName []) (.const natName []))]
      (.bvar 1) (.forallE (.const natName []) (.const natName [])) := by
  exact Lean4Lean.VEnv.HasType.bvar
    (Lean4Lean.Lookup.succ (Lean4Lean.Lookup.zero))

theorem multiBetaInnerTr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none
      [(none, .vlam (.forallE (.const natName []) (.const natName [])))]
      multiBetaInner
      (.lam (.const natName []) (.bvar 1)) := by
  unfold multiBetaInner
  rw [KExpr.mkLam_shape]
  exact .lam ⟨_, multiNatType
      [(.forallE (.const natName []) (.const natName []))]⟩
    (multiNatTr
      [(none, .vlam (.forallE (.const natName []) (.const natName [])))])
    multiBetaBodyTr

theorem multiBetaInnerType :
    worldGood.venv.HasType 0
      [(.forallE (.const natName []) (.const natName []))]
      (.lam (.const natName []) (.bvar 1))
      (.forallE (.const natName [])
        (.forallE (.const natName []) (.const natName []))) := by
  exact Lean4Lean.VEnv.HasType.lam
    (multiNatType
      [(.forallE (.const natName []) (.const natName []))])
    multiBetaBodyType

theorem multiBetaLamTr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
      multiBetaLam
      (.lam (.forallE (.const natName []) (.const natName []))
        (.lam (.const natName []) (.bvar 1))) := by
  unfold multiBetaLam
  rw [KExpr.mkLam_shape]
  exact .lam ⟨_, multiBetaFunType []⟩ multiBetaFunTyTr multiBetaInnerTr

theorem multiBetaLamType :
    worldGood.venv.HasType 0 []
      (.lam (.forallE (.const natName []) (.const natName []))
        (.lam (.const natName []) (.bvar 1)))
      (.forallE (.forallE (.const natName []) (.const natName []))
        (.forallE (.const natName [])
          (.forallE (.const natName []) (.const natName [])))) := by
  exact Lean4Lean.VEnv.HasType.lam (multiBetaFunType []) multiBetaInnerType

def multiBetaApp1V : Lean4Lean.VExpr :=
  .app
    (.lam (.forallE (.const natName []) (.const natName []))
      (.lam (.const natName []) (.bvar 1)))
    (.const succName [])

def multiBetaApp2V : Lean4Lean.VExpr :=
  .app multiBetaApp1V (.const zeroName [])

def multiBetaSourceV : Lean4Lean.VExpr :=
  .app multiBetaApp2V (.const zeroName [])

theorem multiBetaApp1Type :
    worldGood.venv.HasType 0 [] multiBetaApp1V
      (.forallE (.const natName [])
        (.forallE (.const natName []) (.const natName []))) := by
  unfold multiBetaApp1V
  simpa [Lean4Lean.VExpr.inst] using Lean4Lean.VEnv.HasType.app multiBetaLamType appStuckHead_type

theorem multiBetaApp2Type :
    worldGood.venv.HasType 0 [] multiBetaApp2V
      (.forallE (.const natName []) (.const natName [])) := by
  unfold multiBetaApp2V
  simpa [Lean4Lean.VExpr.inst] using Lean4Lean.VEnv.HasType.app multiBetaApp1Type betaArg_type

theorem multiBetaSourceTr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
      multiBetaSource multiBetaSourceV := by
  unfold multiBetaSource
  rw [KExpr.mkApp_shape, KExpr.mkApp_shape, KExpr.mkApp_shape]
  unfold multiBetaSourceV multiBetaApp2V multiBetaApp1V
  exact .app multiBetaApp2Type betaArg_type
    (.app multiBetaApp1Type betaArg_type
      (.app multiBetaLamType appStuckHead_type
        multiBetaLamTr appStuckHead_tr)
      betaArg_tr)
    betaArg_tr

theorem multiBetaSourceType :
    worldGood.venv.HasType 0 [] multiBetaSourceV
      (.const natName []) := by
  unfold multiBetaSourceV
  simpa [Lean4Lean.VExpr.inst] using Lean4Lean.VEnv.HasType.app multiBetaApp2Type betaArg_type

/-- The one dynamically generated trailing application is a real execution
request, not an unindexed support assumption. -/
def multiBetaRequests : List WalkerRequest :=
  [.internExpr appStuckSource]

def multiBetaRunSupport : RunSupport :=
  RunSupport.singleton appStuckSource

def multiBetaProgram : TcM .anon (KExpr .anon) :=
  TcM.intern appStuckSource

theorem multiBetaExecution (prims : Primitives .anon) :
    ExecutionRequests multiBetaProgram (noAccelState prims)
      multiBetaRequests := by
  unfold multiBetaProgram multiBetaRequests
  exact .internExpr (noAccelState prims) appStuckSource

theorem multiBetaCheckSupport (prims : Primitives .anon) :
    CheckConstSupport (noAccelState prims).env.intern
      multiBetaRequests multiBetaRunSupport := by
  constructor
  · constructor
    · intro x hx
      obtain ⟨a, ha⟩ := hx
      simp [noAccelState, state, loadedEnv, KEnv.insert] at ha
    · intro u hu
      obtain ⟨a, ha⟩ := hu
      simp [noAccelState, state, loadedEnv, KEnv.insert] at ha
  · intro request hmem
    simp [multiBetaRequests] at hmem
    subst request
    constructor
    · intro x hx
      change x = appStuckSource
      exact hx
    · intro u hu
      exact False.elim hu

theorem multiBetaBounds : ResourceBounds multiBetaRequests := by
  constructor
  intro request hmem
  simp [multiBetaRequests] at hmem
  subst request
  unfold appStuckSource appStuckHead
  exact .app .const betaArg_constructed

theorem multiBetaRunAssumptions (prims : Primitives .anon) :
    RunAssumptions (noAccelState prims) multiBetaProgram
      multiBetaRequests multiBetaRunSupport :=
  ⟨multiBetaExecution prims,
    RunSupport.singleton_collisionFree appStuckSource,
    multiBetaCheckSupport prims, multiBetaBounds⟩

theorem multiBetaStateInv (prims : Primitives .anon) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
      multiBetaRunSupport 0 [] (noAccelState prims) := by
  have hbase := noAccelStateInv prims
  refine ⟨?_, hbase.2.1, hbase.2.2⟩
  apply KernelStateWF.of_no_cache_entries
  · exact hbase.1.core
  · constructor
    · intro x hx
      obtain ⟨a, ha⟩ := hx
      simp [noAccelState, state, loadedEnv, KEnv.insert] at ha
    · intro u hu
      obtain ⟨a, ha⟩ := hu
      simp [noAccelState, state, loadedEnv, KEnv.insert] at ha
  · rfl
  · intro entry
    simpa [noAccelState, state] using loadedEnv_noCacheEntries entry

/-- The non-transient branch on the same application performs one real
intern-table update while preserving the complete WHNF invariant and the
same reflexive Theory meaning. -/
theorem appStuckIotaInterned (prims : Primitives .anon)
    (methods : Methods .anon) :
    ∃ s',
      (RecM.applyIotaArg appStuckHead betaArg false).run methods
          (noAccelState prims) = .ok appStuckSource s' ∧
        WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none
          worldGood multiBetaRunSupport 0 [] s' ∧
        InternUpdateFrame (noAccelState prims) s' ∧
        WhnfMeaning RawProjRel.none worldGood 0 []
          appStuckSource appStuckSource := by
  have hcollision : multiBetaRunSupport.CollisionFree := by
    unfold multiBetaRunSupport
    exact RunSupport.singleton_collisionFree appStuckSource
  have hsupport : multiBetaRunSupport (KExpr.mkApp appStuckHead betaArg) := by
    unfold multiBetaRunSupport RunSupport.singleton appStuckSource
    rfl
  have h := RecM.applyIotaArg_false_semantic
    (sourceInfo := (KExpr.mkApp appStuckHead betaArg).info)
    hcollision hsupport (multiBetaStateInv prims) methods
    appStuckHead_type betaArg_type appStuckHead_tr betaArg_tr
  simpa [← KExpr.mkApp_shape, appStuckSource] using h

/-! ### ArgumentExecution iota-argument list execution -/

/-- Finite support for the three-segment executor fixture.  It retains the
loaded state's original support root and adds both the unreduced function and
its one-argument result. -/
def iotaArgsSupport : RunSupport where
  expr e := support e ∨ e = appStuckHead ∨ e = appStuckSource
  exprFinite := ⟨[supportExpr, appStuckHead, appStuckSource], by
    intro e he
    rcases he with he | he | he
    · change e = supportExpr at he
      subst e
      simp
    · subst e
      simp
    · subst e
      simp⟩
  univ := support.univ
  univFinite := support.univFinite

theorem support_le_iotaArgsSupport : support ≤ iotaArgsSupport := by
  exact ⟨fun _ h => .inl h, fun _ h => h⟩

theorem iotaArgsStateInv (prims : Primitives .anon) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
      iotaArgsSupport 0 [] (noAccelState prims) := by
  have hbase := noAccelStateInv prims
  refine ⟨?_, hbase.2.1, hbase.2.2⟩
  apply KernelStateWF.of_no_cache_entries
  · exact hbase.1.core
  · exact hbase.1.internSupport.mono support_le_iotaArgsSupport
  · rfl
  · intro entry
    simpa [noAccelState, state] using loadedEnv_noCacheEntries entry

theorem iotaArgsSupport_head : iotaArgsSupport appStuckHead :=
  .inr (.inl rfl)

theorem iotaArgsSupport_source : iotaArgsSupport appStuckSource :=
  .inr (.inr rfl)

/-- The actual three-call executor is inhabited with the argument placed in
the constructor-field segment.  Empty prefix/trailing segments preserve the
same state; the middle transient non-lambda step rebuilds `Nat.succ Nat.zero`
without interning, and quotient transport recovers reflexive Theory meaning
for the complete application. -/
theorem appStuckIotaTransientThreeSegments (prims : Primitives .anon)
    (methods : Methods .anon) :
    (do
        let result ← RecM.applyIotaArgs appStuckHead #[] true
        let result ← RecM.applyIotaArgs result #[betaArg] true
        RecM.applyIotaArgs result #[] true).run methods
          (noAccelState prims) =
        .ok appStuckSource (noAccelState prims) ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        iotaArgsSupport 0 [] (noAccelState prims) ∧
      InternUpdateFrame (noAccelState prims) (noAccelState prims) ∧
      iotaArgsSupport appStuckSource ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] appStuckSource
        appStuckSource := by
  let hfirst : RecM.ApplyIotaArgsTrace .structuralNoAccel whnfSemantics
      RawProjRel.none worldGood iotaArgsSupport 0 [] methods true
      appStuckHead (.const succName []) (noAccelState prims) []
      appStuckHead (.const succName []) (noAccelState prims) := .nil _ _ _
  have hsecond :=
    RecM.ApplyIotaArgsTrace.transientNonLambdaSingleton
      (support := iotaArgsSupport) (methods := methods)
      appStuckHead_iotaNonLambda (iotaArgsStateInv prims)
      iotaArgsSupport_source appStuckHead_type betaArg_type
      appStuckHead_tr betaArg_tr
  let hthird : RecM.ApplyIotaArgsTrace .structuralNoAccel whnfSemantics
      RawProjRel.none worldGood iotaArgsSupport 0 [] methods true
      appStuckSource
        (.app (.const succName []) (.const zeroName []))
        (noAccelState prims) [] appStuckSource
        (.app (.const succName []) (.const zeroName []))
        (noAccelState prims) := .nil _ _ _
  have h := RecM.ApplyIotaArgsTrace.threeArrayAcceptance
    (first := #[]) (second := #[betaArg]) (third := #[])
    hfirst hsecond hthird structuralWhnfTheory (by trivial)
    (iotaArgsStateInv prims) iotaArgsSupport_head appStuckHead_tr
  simpa [appStuckSource] using h

/-- Concrete lambda produced after the first transient application of the
three-argument multi-beta fixture. -/
def multiIotaIntermediate : KExpr .anon :=
  KExpr.mkLam () () supportExpr appStuckHead

theorem multiIotaFirstResult :
    substNoIntern multiBetaInner appStuckHead 0 = multiIotaIntermediate := by
  unfold multiBetaInner multiBetaBody multiIotaIntermediate appStuckHead
  have hty :
      substNoIntern supportExpr (KExpr.mkConst succId #[] ()) 0 =
        supportExpr := by
    exact KExpr.substNoIntern_of_lbr_le (by simp [supportExpr_lbr])
  have hbody :
      substNoIntern (KExpr.mkVar 1 ()) (KExpr.mkConst succId #[] ()) 1 =
        KExpr.mkConst succId #[] () := by
    rw [KExpr.mkVar_shape, substNoIntern]
    change (if (2 : UInt64) ≤ 1 then _ else _) = _
    rw [if_neg (by decide)]
    simp only [beq_self_eq_true, if_true]
    exact KExpr.liftNoIntern_of_lbr_le (by simp)
  rw [KExpr.mkLam_shape]
  rw [substNoIntern]
  change (if (1 : UInt64) ≤ 0 then _ else _) = _
  rw [if_neg (by decide)]
  rw [show (0 : UInt64) + 1 = 1 from rfl]
  rw [hty, hbody]

theorem multiIotaSecondResult :
    substNoIntern appStuckHead betaArg 0 = appStuckHead := by
  exact KExpr.substNoIntern_of_lbr_le (by simp [appStuckHead])

theorem appStuckHead_constructed : KExpr.Constructed appStuckHead := by
  unfold appStuckHead
  exact .const

theorem multiBetaInner_constructed : KExpr.Constructed multiBetaInner := by
  unfold multiBetaInner multiBetaBody
  exact .lam supportExpr_constructed (.var (by decide))

theorem multiIotaIntermediate_constructed :
    KExpr.Constructed multiIotaIntermediate := by
  unfold multiIotaIntermediate
  exact .lam supportExpr_constructed appStuckHead_constructed

theorem appStuckHead_tr_ctx (Delta : KVLCtx) :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none Delta
      appStuckHead (.const succName []) := by
  rw [appStuckHead, KExpr.mkConst_shape]
  exact .const (ci := succConstant) nameOf_succ
    (by simpa [worldGood, goodEnv, goodName, succName] using natEnv_succ)
    (by intro l hl; simp at hl) rfl

theorem appStuckHead_type_ctx (Gamma : List Lean4Lean.VExpr) :
    worldGood.venv.HasType 0 Gamma (.const succName [])
      (.forallE (.const natName []) (.const natName [])) := by
  exact Lean4Lean.VEnv.HasType.const (env := worldGood.venv)
    (U := 0) (Γ := Gamma) (ci := succConstant) (ls := [])
    (by simpa [worldGood, goodEnv, goodName, succName] using natEnv_succ)
    (by intro l hl; simp at hl) rfl

theorem multiIotaIntermediate_tr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
      multiIotaIntermediate
      (.lam (.const natName []) (.const succName [])) := by
  rw [multiIotaIntermediate, KExpr.mkLam_shape]
  exact .lam ⟨_, multiNatType []⟩ (multiNatTr [])
    (appStuckHead_tr_ctx
      [(none, .vlam (.const natName []))])

/-- Support for the mixed transient executor includes every concrete
intermediate, not merely the final rebuilt application. -/
def multiIotaSupport : RunSupport where
  expr e := support e ∨ e = multiBetaLam ∨ e = multiIotaIntermediate ∨
    e = appStuckHead ∨ e = appStuckSource
  exprFinite :=
    ⟨[supportExpr, multiBetaLam, multiIotaIntermediate, appStuckHead,
      appStuckSource], by
      intro e he
      rcases he with he | he | he | he | he
      · change e = supportExpr at he
        subst e
        simp
      · subst e
        simp
      · subst e
        simp
      · subst e
        simp
      · subst e
        simp⟩
  univ := support.univ
  univFinite := support.univFinite

theorem support_le_multiIotaSupport : support ≤ multiIotaSupport := by
  exact ⟨fun _ h => .inl h, fun _ h => h⟩

theorem multiIotaStateInv (prims : Primitives .anon) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
      multiIotaSupport 0 [] (noAccelState prims) := by
  have hbase := noAccelStateInv prims
  refine ⟨?_, hbase.2.1, hbase.2.2⟩
  apply KernelStateWF.of_no_cache_entries
  · exact hbase.1.core
  · exact hbase.1.internSupport.mono support_le_multiIotaSupport
  · rfl
  · intro entry
    simpa [noAccelState, state] using loadedEnv_noCacheEntries entry

theorem multiIotaSupport_start : multiIotaSupport multiBetaLam :=
  .inr (.inl rfl)

theorem multiIotaSupport_intermediate :
    multiIotaSupport multiIotaIntermediate :=
  .inr (.inr (.inl rfl))

theorem multiIotaSupport_head : multiIotaSupport appStuckHead :=
  .inr (.inr (.inr (.inl rfl)))

theorem multiIotaSupport_result : multiIotaSupport appStuckSource :=
  .inr (.inr (.inr (.inr rfl)))

theorem multiIotaFirstTrace (prims : Primitives .anon)
    (methods : Methods .anon) :
    RecM.ApplyIotaArgsTrace .structuralNoAccel whnfSemantics
      RawProjRel.none worldGood multiIotaSupport 0 [] methods true
      multiBetaLam
        (.lam (.forallE (.const natName []) (.const natName []))
          (.lam (.const natName []) (.bvar 1)))
        (noAccelState prims) [appStuckHead] multiIotaIntermediate
        multiBetaApp1V (noAccelState prims) := by
  have hfirst :=
    RecM.ApplyIotaArgsTrace.transientLambdaSingletonQuot
      (support := multiIotaSupport) (methods := methods)
      (name := ()) (bi := ()) (ty := multiBetaFunTy)
      (body := multiBetaInner) (arg := appStuckHead)
      (info := (KExpr.mkLam () () multiBetaFunTy multiBetaInner).info)
      multiBetaLamType appStuckHead_type
      (RawProjRel.none_ok worldGood.venv 0)
      multiBetaFunTyTr multiBetaInnerTr appStuckHead_tr
      (multiBetaFunType []) multiBetaInnerType appStuckHead_type
      multiBetaInner_constructed appStuckHead_constructed (by decide)
      (multiIotaStateInv prims)
      (by
        rw [multiIotaFirstResult]
        exact multiIotaSupport_intermediate)
  simpa [multiBetaLam, ← KExpr.mkLam_shape, multiBetaApp1V, multiIotaFirstResult] using hfirst

theorem multiIotaSecondTrace (prims : Primitives .anon)
    (methods : Methods .anon) :
    RecM.ApplyIotaArgsTrace .structuralNoAccel whnfSemantics
      RawProjRel.none worldGood multiIotaSupport 0 [] methods true
      multiIotaIntermediate multiBetaApp1V (noAccelState prims) [betaArg]
      appStuckHead multiBetaApp2V (noAccelState prims) := by
  have hsecond :=
    RecM.ApplyIotaArgsTrace.transientLambdaSingletonQuot
      (support := multiIotaSupport) (methods := methods)
      (expectedV := multiBetaApp1V)
      (name := ()) (bi := ()) (ty := supportExpr) (body := appStuckHead)
      (arg := betaArg)
      (info := (KExpr.mkLam () () supportExpr appStuckHead).info)
      (A := .const natName []) (bodyV := .const succName [])
      (argV := .const zeroName [])
      (B := .forallE (.const natName []) (.const natName []))
      multiBetaApp1Type betaArg_type
      (RawProjRel.none_ok worldGood.venv 0)
      (multiNatTr [])
      (appStuckHead_tr_ctx [(none, .vlam (.const natName []))])
      betaArg_tr betaA_type
      (appStuckHead_type_ctx [(.const natName [])]) betaArg_type
      appStuckHead_constructed betaArg_constructed (by decide)
      (multiIotaStateInv prims)
      (by
        rw [multiIotaSecondResult]
        exact multiIotaSupport_head)
  rw [multiIotaIntermediate, KExpr.mkLam_shape]
  simpa [multiBetaApp2V, multiIotaSecondResult] using hsecond

theorem multiIotaThirdTrace (prims : Primitives .anon)
    (methods : Methods .anon) :
    RecM.ApplyIotaArgsTrace .structuralNoAccel whnfSemantics
      RawProjRel.none worldGood multiIotaSupport 0 [] methods true
      appStuckHead multiBetaApp2V (noAccelState prims) [betaArg]
      appStuckSource multiBetaSourceV (noAccelState prims) := by
  simpa [appStuckSource, multiBetaLam, KExpr.mkLam_shape, multiBetaSourceV] using
    (RecM.ApplyIotaArgsTrace.transientNonLambdaSingletonQuot
      (support := multiIotaSupport) (methods := methods)
      (expectedV := multiBetaApp2V)
      appStuckHead_iotaNonLambda (multiIotaStateInv prims)
      multiIotaSupport_result multiBetaApp2Type betaArg_type
      appStuckHead_type betaArg_type appStuckHead_tr betaArg_tr)

/-- A non-vacuous ArgumentExecution trace across all three production segments.  The
first argument beta-reduces the outer lambda to another lambda, the second
beta-reduces that quotient-mismatched intermediate to `Nat.succ`, and the
third rebuilds `Nat.succ Nat.zero`.  Thus the final meaning proof genuinely
uses quotient transport rather than structural equality of intermediates. -/
theorem multiIotaTransientThreeSegments (prims : Primitives .anon)
    (methods : Methods .anon) :
    (do
        let result ← RecM.applyIotaArgs multiBetaLam #[appStuckHead] true
        let result ← RecM.applyIotaArgs result #[betaArg] true
        RecM.applyIotaArgs result #[betaArg] true).run methods
          (noAccelState prims) =
        .ok appStuckSource (noAccelState prims) ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        multiIotaSupport 0 [] (noAccelState prims) ∧
      InternUpdateFrame (noAccelState prims) (noAccelState prims) ∧
      multiIotaSupport appStuckSource ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] multiBetaSource
        appStuckSource := by
  have h := RecM.ApplyIotaArgsTrace.threeArrayAcceptance
    (first := #[appStuckHead]) (second := #[betaArg])
    (third := #[betaArg]) (multiIotaFirstTrace prims methods)
    (multiIotaSecondTrace prims methods) (multiIotaThirdTrace prims methods)
    structuralWhnfTheory (by trivial) (multiIotaStateInv prims)
    multiIotaSupport_start multiBetaLamTr
  simpa [multiBetaSource] using h

/-! ### SelectedRule selected-rule execution witness -/

def multiIotaRule : RecRule .anon :=
  { ctor := (), fields := 1, rhs := multiBetaLam }

def multiIotaInfo : IotaInfo .anon :=
  { k := false, params := 1, motives := 0, minors := 0, indices := 0,
    majorIdx := 1, rules := #[multiIotaRule], lvls := 0 }

def multiIotaSpine : Array (KExpr .anon) :=
  #[appStuckHead, betaArg, betaArg]

def multiIotaCtorArgs : Array (KExpr .anon) := #[betaArg]

theorem multiIotaPrefixSlice :
    RecM.iotaPrefixArgs multiIotaInfo multiIotaSpine = #[appStuckHead] := by
  rfl

theorem multiIotaFieldSlice :
    RecM.iotaFieldArgs multiIotaCtorArgs 1 = #[betaArg] := by
  rfl

theorem multiIotaTrailingSlice :
    RecM.iotaTrailingArgs multiIotaInfo multiIotaSpine = #[betaArg] := by
  rfl

/-- A selected-rule trace whose three indices are the actual production
slices above.  Universe instantiation takes its parameter-free fast path;
the three nonempty argument segments still execute beta, beta, then rebuild. -/
def multiIotaRuleTrace (prims : Primitives .anon) (methods : Methods .anon) :
    RecM.ApplyIotaRuleTrace .structuralNoAccel whnfSemantics
      RawProjRel.none worldGood multiIotaSupport 0 [] methods multiIotaRule
      #[] multiIotaInfo multiIotaSpine multiIotaCtorArgs 1 true
      (.lam (.forallE (.const natName []) (.const natName []))
        (.lam (.const natName []) (.bvar 1)))
      (noAccelState prims) appStuckSource multiBetaSourceV
      (noAccelState prims) where
  rhs := multiBetaLam
  after := noAccelState prims
  middle1 := multiIotaIntermediate
  middle2 := appStuckHead
  middleV1 := multiBetaApp1V
  middleV2 := multiBetaApp2V
  s1 := noAccelState prims
  s2 := noAccelState prims
  instantiate := rfl
  prefixTrace := by
    simpa [multiIotaPrefixSlice] using multiIotaFirstTrace prims methods
  fieldTrace := by
    simpa [multiIotaFieldSlice] using
      multiIotaSecondTrace prims methods
  trailingTrace := by
    simpa [multiIotaTrailingSlice] using
      multiIotaThirdTrace prims methods

/-- ConstructorDispatch wraps the same non-vacuous selected-rule execution in production's
constructor-index dispatch and both of its guards. -/
def multiIotaCtorTrace (prims : Primitives .anon) (methods : Methods .anon) :
    RecM.ApplyIotaCtorTrace .structuralNoAccel whnfSemantics
      RawProjRel.none worldGood multiIotaSupport 0 [] methods multiIotaInfo
      #[] multiIotaSpine multiIotaCtorArgs 0 1 true multiIotaRule
      (.lam (.forallE (.const natName []) (.const natName []))
        (.lam (.const natName []) (.bvar 1)))
      (noAccelState prims) appStuckSource multiBetaSourceV
      (noAccelState prims) where
  selected := rfl
  levelArity := rfl
  fieldBound := by decide
  ruleTrace := multiIotaRuleTrace prims methods

/-- The complete extracted production helper is inhabited on nonempty values
in all three slices, not only the abstract list executor. -/
theorem multiIotaRuleEval (prims : Primitives .anon)
    (methods : Methods .anon) :
    (RecM.applyIotaRule multiIotaRule #[] multiIotaInfo multiIotaSpine
      multiIotaCtorArgs 1 true).run methods (noAccelState prims) =
        .ok appStuckSource (noAccelState prims) :=
  (multiIotaRuleTrace prims methods).eval

theorem multiIotaCtorEval (prims : Primitives .anon)
    (methods : Methods .anon) :
    (RecM.tryApplyIotaCtor multiIotaInfo #[] multiIotaSpine
      multiIotaCtorArgs 0 1 true).run methods (noAccelState prims) =
        .ok (some appStuckSource) (noAccelState prims) :=
  (multiIotaCtorTrace prims methods).eval

theorem multiIotaRuleAcceptance (prims : Primitives .anon)
    (methods : Methods .anon) :
    (RecM.applyIotaRule multiIotaRule #[] multiIotaInfo multiIotaSpine
      multiIotaCtorArgs 1 true).run methods (noAccelState prims) =
        .ok appStuckSource (noAccelState prims) ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        multiIotaSupport 0 [] (noAccelState prims) ∧
      InternUpdateFrame (noAccelState prims) (noAccelState prims) ∧
      multiIotaSupport appStuckSource ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] multiBetaSource
        appStuckSource := by
  have h := (multiIotaRuleTrace prims methods).acceptance_empty rfl
    structuralWhnfTheory (by trivial) (multiIotaStateInv prims)
    (by simpa [multiIotaRule] using multiIotaSupport_start)
    (by
      simpa [multiIotaRule] using
        (multiBetaLamTr.trKExpr worldGood.venvWF.ordered
          structuralWhnfTheory.literalWF
          structuralWhnfTheory.projections.wf (by trivial)))
  obtain ⟨hrun, hfinalI, hframe, hfinalSupport, hfinalTr, hmeaning⟩ := h
  exact ⟨hrun, hfinalI, hframe, hfinalSupport, by
    simpa [multiIotaRuleTrace, multiBetaLam, ← KExpr.mkLam_shape, multiIotaPrefixSlice, multiIotaFieldSlice,
      multiIotaTrailingSlice, multiIotaRule, multiBetaSource] using hmeaning⟩

theorem multiIotaCtorAcceptance (prims : Primitives .anon)
    (methods : Methods .anon) :
    (RecM.tryApplyIotaCtor multiIotaInfo #[] multiIotaSpine
      multiIotaCtorArgs 0 1 true).run methods (noAccelState prims) =
        .ok (some appStuckSource) (noAccelState prims) ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        multiIotaSupport 0 [] (noAccelState prims) ∧
      InternUpdateFrame (noAccelState prims) (noAccelState prims) ∧
      multiIotaSupport appStuckSource ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] multiBetaSource
        appStuckSource := by
  have h := (multiIotaCtorTrace prims methods).acceptance_empty rfl
    structuralWhnfTheory (by trivial) (multiIotaStateInv prims)
    (by simpa [multiIotaRule] using multiIotaSupport_start)
    (by
      simpa [multiIotaRule] using
        (multiBetaLamTr.trKExpr worldGood.venvWF.ordered
          structuralWhnfTheory.literalWF
          structuralWhnfTheory.projections.wf (by trivial)))
  obtain ⟨hrun, hfinalI, hframe, hfinalSupport, hfinalTr, hmeaning⟩ := h
  exact ⟨hrun, hfinalI, hframe, hfinalSupport, by
    simpa [multiIotaCtorTrace, multiIotaRuleTrace, multiBetaLam, ← KExpr.mkLam_shape, multiIotaPrefixSlice, multiIotaFieldSlice,
      multiIotaTrailingSlice, multiIotaRule, multiBetaSource] using hmeaning⟩

theorem multiBetaFinishRequests :
    RecM.FinishAppRequests multiBetaRequests
      (#[appStuckHead, betaArg, betaArg].extract 2 3).toList
      appStuckHead appStuckSource := by
  change RecM.FinishAppRequests multiBetaRequests [betaArg]
    appStuckHead appStuckSource
  apply RecM.FinishAppRequests.cons
  · simp [multiBetaRequests, appStuckSource]
  · simpa [appStuckSource] using
      (RecM.FinishAppRequests.nil (requests := multiBetaRequests)
        appStuckSource)

theorem multiBetaWalkerEval (prims : Primitives .anon) :
    TcM.runIntern (simulSubst multiBetaBody #[betaArg, appStuckHead] 0)
      (noAccelState prims) = .ok appStuckHead (noAccelState prims) := by
  unfold TcM.runIntern
  rw [multiBetaWalker]

/-- Inhabited application rebuilding multi-beta acceptance: the source is translated and typed,
the walker selects the outer function argument, exactly one trailing argument
is rebuilt, and the complete post-state invariant plus intern-only frame are
retained. -/
theorem multiBetaStep (prims : Primitives .anon) (flags : WhnfFlags) :
    ∃ s',
      (RecM.whnfCoreWithFlagsStep multiBetaSource flags).run
          betaHarnessMethods (noAccelState prims) =
        .ok (.next appStuckSource) s' ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        multiBetaRunSupport 0 [] s' ∧
      InternUpdateFrame (noAccelState prims) s' ∧
      TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
        multiBetaSource multiBetaSourceV ∧
      worldGood.venv.HasType 0 [] multiBetaSourceV
        (.const natName []) := by
  obtain ⟨s', hfinish, hI', hframe⟩ :=
    multiBetaFinishRequests.eval
      (multiBetaRunAssumptions prims) (multiBetaStateInv prims)
  refine ⟨s', ?_, hI', hframe, multiBetaSourceTr, multiBetaSourceType⟩
  exact RecM.whnfCoreWithFlagsStep_betaMany multiBetaSpine rfl
    multiBetaConsume rfl (by simpa using multiBetaWalkerEval prims) hfinish

/-- Two physically distinct raw heads that nevertheless translate to the
same trusted `Nat.succ` constant.  The forged info addresses are deliberate:
this fixture attacks control-flow equality, while the generic finite-request
theorems above cover constructed production values. -/
def changedHeadOriginal : KExpr .anon :=
  .const succId #[] (info iotaAddress)

def changedHeadNew : KExpr .anon :=
  .const succId #[] (info goodAddress)

def changedHeadSource : KExpr .anon :=
  KExpr.mkApp changedHeadOriginal betaArg

def changedHeadRebuilt : KExpr .anon :=
  KExpr.mkApp changedHeadNew betaArg

theorem changedHeadPhysical :
    (changedHeadNew != changedHeadOriginal) = true := by
  change Bool.not (goodAddress == iotaAddress) = true
  simp [goodAddress, iotaAddress, address]

theorem changedHeadSpine :
    changedHeadSource.collectSpine = (changedHeadOriginal, #[betaArg]) := by
  unfold changedHeadSource changedHeadOriginal
  rw [KExpr.mkApp_shape]
  rfl

theorem changedHeadOriginalTr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
      changedHeadOriginal (.const succName []) := by
  exact .const (ci := succConstant) nameOf_succ
    (by simpa [worldGood, goodEnv, goodName, succName] using natEnv_succ)
    (by intro l hl; simp at hl) rfl

theorem changedHeadNewTr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
      changedHeadNew (.const succName []) := by
  exact .const (ci := succConstant) nameOf_succ
    (by simpa [worldGood, goodEnv, goodName, succName] using natEnv_succ)
    (by intro l hl; simp at hl) rfl

theorem changedHeadSourceTr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
      changedHeadSource
      (.app (.const succName []) (.const zeroName [])) := by
  unfold changedHeadSource
  rw [KExpr.mkApp_shape]
  exact .app appStuckHead_type betaArg_type changedHeadOriginalTr betaArg_tr

theorem changedHeadRebuiltTr :
    TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
      changedHeadRebuilt
      (.app (.const succName []) (.const zeroName [])) := by
  unfold changedHeadRebuilt
  rw [KExpr.mkApp_shape]
  exact .app appStuckHead_type betaArg_type changedHeadNewTr betaArg_tr

theorem changedHeadMeaning :
    WhnfMeaning RawProjRel.none worldGood 0 [] changedHeadSource
      changedHeadRebuilt := by
  exact ⟨_, _, changedHeadSourceTr, changedHeadRebuiltTr,
    Lean4Lean.VEnv.IsDefEqU.refl
      ⟨_, Lean4Lean.VEnv.HasType.app appStuckHead_type betaArg_type⟩⟩

def changedHeadSupport : RunSupport :=
  RunSupport.singleton changedHeadRebuilt

theorem changedHeadStateInv (prims : Primitives .anon) :
    WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
      changedHeadSupport 0 [] (noAccelState prims) := by
  have hbase := noAccelStateInv prims
  refine ⟨?_, hbase.2.1, hbase.2.2⟩
  apply KernelStateWF.of_no_cache_entries
  · exact hbase.1.core
  · constructor
    · intro x hx
      obtain ⟨a, ha⟩ := hx
      simp [noAccelState, state, loadedEnv, KEnv.insert] at ha
    · intro u hu
      obtain ⟨a, ha⟩ := hu
      simp [noAccelState, state, loadedEnv, KEnv.insert] at ha
  · rfl
  · intro entry
    simpa [noAccelState, state] using loadedEnv_noCacheEntries entry

/-- Low-level exact interning spec for the intentionally raw rebuilt term.
It uses the singleton collision domain directly; unlike normal production
requests it does not claim `KExpr.Constructed` for the forged metadata. -/
theorem changedHeadInternSpec (it : InternTable .anon) (hwf : it.WF)
    (hsup : changedHeadSupport.CoversIntern it) :
    (internExprM changedHeadRebuilt it).1 = changedHeadRebuilt ∧
      (internExprM changedHeadRebuilt it).2.WF ∧
      changedHeadSupport.CoversIntern
        (internExprM changedHeadRebuilt it).2 := by
  unfold internExprM
  have hkcf : KExpr.KeyCollisionFree
      (fun v => it.ExprSupport v ∨ v = changedHeadRebuilt) :=
    KExpr.keyCollisionFree_anon.mpr <|
      (RunSupport.singleton_collisionFree changedHeadRebuilt).expr.mono
        fun x hx => hx.elim (hsup.expr x) (fun h => h)
  have hcanon :
      (it.internExpr changedHeadRebuilt).1 = changedHeadRebuilt := by
    have heq := InternTable.internExpr_eraseMeta hwf hkcf
    rwa [KExpr.eraseMeta_anon, KExpr.eraseMeta_anon] at heq
  refine ⟨hcanon, hwf.internExpr changedHeadRebuilt, ?_⟩
  constructor
  · intro x hx
    rcases InternTable.ExprSupport.of_internExpr hx with hx | rfl
    · exact hsup.expr x hx
    · rfl
  · intro u hu
    exact hsup.univ u (by
      simpa only [InternTable.UnivSupport,
        InternTable.internExpr_univs] using hu)

theorem changedHeadInternEval (prims : Primitives .anon) :
    ∃ s', TcM.intern changedHeadRebuilt (noAccelState prims) =
        .ok changedHeadRebuilt s' ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        changedHeadSupport 0 [] s' ∧
      InternUpdateFrame (noAccelState prims) s' := by
  exact TcM.runIntern_whnf_eval changedHeadInternSpec
    (changedHeadStateInv prims)

/-- Harness that forces the recursive callback across the changed-head
branch.  As with the earlier beta harness, the generic theorem—not this
fixture table—carries the eventual `Methods.WF` obligation. -/
def changedHeadMethods : Methods .anon where
  whnf := fun e => pure e
  whnfCore := fun e => pure e
  whnfMode := fun e _ => pure e
  whnfCoreFlags := fun _ _ => pure changedHeadNew
  infer := fun e => pure e
  isDefEq := fun _ _ => pure false

theorem changedHeadIotaMiss (prims : Primitives .anon)
    {s' : TcState .anon} (hframe : InternUpdateFrame (noAccelState prims) s')
    (flags : WhnfFlags) :
    (RecM.tryIotaWithFlags changedHeadRebuilt flags).run
        changedHeadMethods s' = .ok none s' := by
  unfold RecM.tryIotaWithFlags changedHeadRebuilt changedHeadNew
  rw [KExpr.mkApp_shape]
  simp only [KExpr.collectSpine, KExpr.collectSpine.go]
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst succId) _ s' = _
  unfold EStateM.bind
  have hget : s'.env.get? succId = some succConcrete := by
    rw [hframe]
    simpa [KEnv.get?, noAccelState, state] using loadedEnv_succ_k1e
  have hlookup : TcM.tryGetConst succId s' =
      .ok (some succConcrete) s' := by
    unfold TcM.tryGetConst
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ s' = _
    unfold EStateM.bind
    rw [show (get : TcM .anon (TcState .anon)) s' = .ok s' s' from rfl]
    simp only
    rw [hget]
    rfl
  rw [hlookup]
  rfl

/-- Inhabited changed-head/iota-miss acceptance.  The returned `.done` term
is the rebuilt application; the original and rebuilt sources are physically
different but have the same trusted Theory translation. -/
theorem changedHeadStep (prims : Primitives .anon) (flags : WhnfFlags) :
    ∃ s',
      (RecM.whnfCoreWithFlagsStep changedHeadSource flags).run
          changedHeadMethods (noAccelState prims) =
        .ok (.done changedHeadRebuilt) s' ∧
      WhnfStateInv .structuralNoAccel whnfSemantics RawProjRel.none worldGood
        changedHeadSupport 0 [] s' ∧
      InternUpdateFrame (noAccelState prims) s' ∧
      WhnfMeaning RawProjRel.none worldGood 0 [] changedHeadSource
        changedHeadRebuilt := by
  obtain ⟨s', hintern, hI', hframe⟩ := changedHeadInternEval prims
  have hfinish :
      (RecM.finishAppResult changedHeadNew #[betaArg] 0).run
        changedHeadMethods (noAccelState prims) =
          .ok changedHeadRebuilt s' := by
    apply RecM.finishAppResult_one
    simpa [changedHeadRebuilt] using hintern
  refine ⟨s', ?_, hI', hframe, changedHeadMeaning⟩
  exact RecM.whnfCoreWithFlagsStep_appChangedDone changedHeadSpine
    .const rfl changedHeadPhysical hfinish
    (changedHeadIotaMiss prims hframe flags)

/-! ### NatRecognizer descriptor success witness -/

/-- A deliberately untrusted recursor with the two minors required by the
linear descriptor.  This fixture exercises operational trace completeness;
it is not used as semantic recursor evidence. -/
def linearRecConcrete : KConst .anon :=
  .recr () () false false 0 0 0 0 2 natId 0 natRef
    #[iotaRule, iotaRule] ()

def linearRecPrims (prims : Primitives .anon) : Primitives .anon :=
  { prims with natRec := iotaId }

def linearRecState (prims : Primitives .anon) : TcState .anon :=
  let base := noAccelState (linearRecPrims prims)
  { base with env := base.env.insert iotaId linearRecConcrete }

def linearRecHead : KExpr .anon := KExpr.mkConst iotaId #[] ()

def linearRecMajor : KExpr .anon := .nat 3 iotaAddress (info iotaAddress)

def linearRecSource : KExpr .anon :=
  KExpr.mkApp
    (KExpr.mkApp (KExpr.mkApp linearRecHead iotaResult) iotaResult)
    linearRecMajor

def linearRecParts : NatRecLiteralParts .anon :=
  { spine := #[iotaResult, iotaResult, linearRecMajor]
    major := 3
    baseIdx := 0
    stepIdx := 1
    majorIdx := 2 }

theorem linearRecSpine :
    linearRecSource.collectSpine =
      (linearRecHead, #[iotaResult, iotaResult, linearRecMajor]) := by
  unfold linearRecSource
  rw [KExpr.mkApp_shape]
  unfold KExpr.collectSpine
  rw [KExpr.collectSpine.go, KExpr.mkApp_shape,
    KExpr.collectSpine.go, KExpr.mkApp_shape,
    KExpr.collectSpine.go]
  unfold linearRecHead
  rw [KExpr.mkConst_shape]
  change
    (KExpr.const iotaId #[] (KExpr.mkConst iotaId #[] ()).info,
      (#[linearRecMajor, iotaResult, iotaResult] :
        Array (KExpr .anon)).reverse) = _
  simp

theorem linearRecMajorAt :
    (#[iotaResult, iotaResult, linearRecMajor] : Array (KExpr .anon))[2]? =
      some (.nat 3 iotaAddress (info iotaAddress)) := by
  rfl

theorem linearRecGet (prims : Primitives .anon) :
    TcM.tryGetConst iotaId (linearRecState prims) =
      .ok (some linearRecConcrete) (linearRecState prims) := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _
    (linearRecState prims) = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) (linearRecState prims) =
    .ok (linearRecState prims) (linearRecState prims) from rfl]
  simp only
  have henv : (linearRecState prims).env.get? iotaId =
      some linearRecConcrete := by
    simp [linearRecState, KEnv.get?, KEnv.insert]
  rw [henv]
  rfl

/-- A real successful descriptor execution, certified through NatRecognizer's trace
and then inverted again by trace completeness. -/
theorem linearRecPartsRun (prims : Primitives .anon) :
    (RecM.natRecLiteralParts linearRecSource).run betaHarnessMethods
        (linearRecState prims) =
      .ok (some linearRecParts) (linearRecState prims) := by
  apply RecM.NatRecLiteralPartsSuccessTrace.eval
  refine .intro linearRecSpine ?_ (linearRecGet prims) (by decide)
    linearRecMajorAt
  · simp [linearRecState, linearRecPrims, noAccelState, state]

theorem linearRecPartsTrace (prims : Primitives .anon) :
    RecM.NatRecLiteralPartsSuccessTrace betaHarnessMethods linearRecSource
      (linearRecState prims) linearRecParts (linearRecState prims) :=
  RecM.NatRecLiteralPartsSuccessTrace.complete (linearRecPartsRun prims)

/-! ### NatPatternMatching constructive iota-match witnesses -/

/-- A concrete two-argument recursor prefix mirroring the descriptor fixture's
major position.  The argument values are immaterial to pattern matching; the
count and constant head are not. -/
def linearRecTheoryPrefix : Lean4Lean.VExpr :=
  .app
    (.app (.const ``Nat.rec []) (.const ``Nat []))
    (.const ``Nat [])

theorem linearRecTheoryPrefix_shape :
    HeadConstN ``Nat.rec 2 linearRecTheoryPrefix := by
  unfold linearRecTheoryPrefix
  simpa using HeadConstN.app
    (HeadConstN.app (HeadConstN.const (name := ``Nat.rec) []))

/-- The zero branch constructs Lean4Lean's real dependent capture map. -/
theorem linearRecZeroPatternMatch :
    ∃ (levels : List Lean4Lean.VLevel)
        (captures : (RecursorIotaPattern ``Nat.rec 2 ``Nat.zero 0).Path →
          Lean4Lean.VExpr),
      Lean4Lean.Pattern.Matches
        (RecursorIotaPattern ``Nat.rec 2 ``Nat.zero 0)
        (.app linearRecTheoryPrefix (Lean4Lean.VExpr.natLit 0))
        levels captures :=
  RecursorIotaPattern.matches_natZero linearRecTheoryPrefix_shape

/-- The successor branch constructs a capture map whose constructor argument
is the canonical predecessor numeral. -/
theorem linearRecSuccPatternMatch :
    ∃ (levels : List Lean4Lean.VLevel)
        (captures : (RecursorIotaPattern ``Nat.rec 2 ``Nat.succ 1).Path →
          Lean4Lean.VExpr),
      Lean4Lean.Pattern.Matches
        (RecursorIotaPattern ``Nat.rec 2 ``Nat.succ 1)
        (.app linearRecTheoryPrefix (Lean4Lean.VExpr.natLit 3))
        levels captures := by
  simpa using (RecursorIotaPattern.matches_natSucc
    (predecessor := 2) linearRecTheoryPrefix_shape)

/-! ### NatRuleLayout adversarial layout and suffix witnesses -/

/-- Reporting two minors does not force either corresponding rule slot to
exist.  This declaration passes the descriptor's count check while carrying
an empty rule array. -/
def missingRuleRecursor : KConst .anon :=
  .recr () () false false 0 0 0 0 2 natId 0 natRef #[] ()

theorem missingRuleDescriptor :
    RecM.NatRecLiteralPartsDescriptor iotaId missingRuleRecursor
      linearRecSource linearRecParts := by
  refine ⟨#[], (KExpr.mkConst iotaId #[] ()).info,
    #[iotaResult, iotaResult, linearRecMajor], (), (), false, false,
    0, 0, 0, 0, 2, natId, 0, natRef, #[], (), 3, iotaAddress,
    info iotaAddress, ?_, rfl, by decide, linearRecMajorAt, rfl⟩
  change linearRecSource.collectSpine =
    (linearRecHead, #[iotaResult, iotaResult, linearRecMajor])
  exact linearRecSpine

theorem missingRuleDescriptor_noZeroRule :
    ¬∃ rule, missingRuleRecursor.RecursorRuleAt 0 rule := by
  simp [missingRuleRecursor, KConst.RecursorRuleAt]

/-- Splitting the translated three-argument beta fixture at its middle
argument retains the final argument in a nonempty typed suffix. -/
theorem multiBetaMiddleSplit :
    ∃ (priorArgs laterArgs : List (KExpr .anon))
        (priorV majorV : Lean4Lean.VExpr),
      [appStuckHead, betaArg, betaArg] =
          priorArgs ++ betaArg :: laterArgs ∧
      1 = priorArgs.length ∧
      RecM.TrAppSpine worldGood.venv 0 worldGood.nameOf RawProjRel.none []
        multiBetaLam priorArgs priorV ∧
      TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
        betaArg majorV ∧
      TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
        (KExpr.mkApp (priorArgs.foldl KExpr.mkApp multiBetaLam) betaArg)
        (.app priorV majorV) ∧
      RecM.TrAppSuffix worldGood.venv 0 worldGood.nameOf RawProjRel.none []
        (.app priorV majorV) laterArgs multiBetaSourceV ∧
      laterArgs ≠ [] := by
  have hspine : RecM.TrAppSpine worldGood.venv 0 worldGood.nameOf
      RawProjRel.none [] multiBetaLam
      [appStuckHead, betaArg, betaArg] multiBetaSourceV := by
    simpa using RecM.trAppSpine_of_collectSpine
      multiBetaSourceTr multiBetaSpine
  obtain ⟨priorArgs, laterArgs, priorV, majorV, hargs, hindex, hpriorTr,
    hmajorTr, hthroughTr, hlaterTr⟩ :=
    hspine.splitAt (major := betaArg) (majorIdx := 1) (by rfl)
  have hlater : laterArgs ≠ [] := by
    intro hempty
    have hlength := congrArg List.length hargs
    simp only [List.length_cons, List.length_append] at hlength
    rw [hempty] at hlength
    simp only [List.length_nil] at hlength
    omega
  exact ⟨priorArgs, laterArgs, priorV, majorV, hargs, hindex, hpriorTr,
    hmajorTr, hthroughTr, hlaterTr, hlater⟩

/-- NatReduction's suffix transport is inhabited on a genuinely nonempty suffix.
Replacing the through-middle prefix by its own translation reconstructs the
final application rather than silently returning the prefix. -/
theorem multiBetaMiddleRebase :
    ∃ (priorArgs laterArgs : List (KExpr .anon))
        (resultV : Lean4Lean.VExpr),
      laterArgs ≠ [] ∧
      TrKExprS worldGood.venv 0 worldGood.nameOf RawProjRel.none []
        (laterArgs.foldl KExpr.mkApp
          (KExpr.mkApp (priorArgs.foldl KExpr.mkApp multiBetaLam) betaArg))
        resultV ∧
      worldGood.venv.IsDefEqU 0 [] multiBetaSourceV resultV := by
  obtain ⟨priorArgs, laterArgs, priorV, majorV, hargs, hindex, hpriorTr,
    hmajorTr, hthroughTr, hlaterTr, hlater⟩ := multiBetaMiddleSplit
  obtain ⟨throughType, hthroughType⟩ :=
    hlaterTr.startHasType multiBetaSourceType
  have hthroughEq : worldGood.venv.IsDefEqU 0 []
      (.app priorV majorV) (.app priorV majorV) :=
    ⟨throughType, hthroughType⟩
  obtain ⟨resultV, hresultTr, hresultEq⟩ :=
    hlaterTr.rebase worldGood.venvWF (by trivial) hthroughTr hthroughEq
  exact ⟨priorArgs, laterArgs, resultV, hlater, hresultTr, hresultEq⟩

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
