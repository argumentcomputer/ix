import IxVMRefinement.Assembly.LayerSeams
import IxVMRefinement.RoleVal.CommittedBase
import Ix.IxVM.Consistency.TableValid
import Ix.Cert.AcceptedKeys
import IxC.Kernel.Model.FoldJ

/-! # An inhabitant of the table-validity witness

`TableShape` and `TableWitness` are satisfiable: the committed default table, the empty store
and the environment of the kernel's pinned basis blocks inhabit them on the empty set of
groups (`tableShape_basis`, `tableWitness_basis`).

What this checks: the prelude pin and the literal-support clause hold of the committed
default table; the pinned basis environment has distinct names, consists of pinned constants,
holds every pinned block whole and has a model in every set theory (six basis installs from
the empty environment); the store clauses hold of the empty store.

What it does not check: any clause over a record. The store is empty, so `ReadingOf.stored`,
`KeptIn`, `UsedClosed` and `AgreesCommitted` hold with nothing to say, and the set of groups
is empty, so `bound`, `needsClosed`, `kept` and `preludeKept` do too. `And` and `Bool` are
not in the environment. `Facts` is taken to be `True`: the inhabitant says nothing about the
invariant the typing half continues from.
-/

universe u

namespace IxVM.Refinement.TableInhabit

open Ix.Kernel
open IxVM.Consistency
open Ix.Kernel.Semantics (DeclBasisRun)

/-! ## Freshness and lookup in an environment keyed by roles -/

/-- A role key is fresh in an environment whose names are the keys of other roles. -/
theorem role_fresh {env : Env .anon} (rs : List Role) (r : Role)
    (hn : env.consts.map (·.name) = rs.map Key.role) (hr : r ∉ rs) :
    (env.find? (Key.role r)).isNone = true := by
  have hnone : env.consts.find? (·.name == Key.role r) = none := by
    rw [List.find?_eq_none]
    intro x hx hbeq
    have hk : x.name = Key.role r := eq_of_beq hbeq
    have hmem : x.name ∈ env.consts.map (·.name) := List.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hn, hk] at hmem
    obtain ⟨r', hr', he⟩ := List.mem_map.mp hmem
    have e : r' = r := Key.role.inj he
    rw [e] at hr'
    exact hr hr'
  exact (congrArg Option.isNone hnone).trans rfl

/-- Names that are the keys of distinct roles are distinct. -/
theorem roleNames_nodup {cs : List (ConstantInfo .anon)} (rs : List Role)
    (hn : cs.map (·.name) = rs.map Key.role) (hr : rs.Nodup) : (cs.map (·.name)).Nodup := by
  rw [hn]
  exact hr.map fun _ _ h => by injection h

/-! ## The pinned basis environment -/

def basisEnv1 : Env .anon := ⟨[eqRecA, eqReflA, eqA]⟩

def basisEnv2 : Env .anon := ⟨[natRecA, natSuccA, natZeroA, natA, eqRecA, eqReflA, eqA]⟩

def basisEnv3 : Env .anon :=
  ⟨[punitRecA, punitUnitA, punitA, natRecA, natSuccA, natZeroA, natA, eqRecA, eqReflA, eqA]⟩

def basisEnv4 : Env .anon :=
  ⟨[emptyRecA, emptyA, punitRecA, punitUnitA, punitA, natRecA, natSuccA, natZeroA, natA,
    eqRecA, eqReflA, eqA]⟩

def basisEnv5 : Env .anon :=
  ⟨[falseRecA, falseA, emptyRecA, emptyA, punitRecA, punitUnitA, punitA, natRecA, natSuccA,
    natZeroA, natA, eqRecA, eqReflA, eqA]⟩

/-- **The environment of the kernel's pinned basis blocks**, as six basis installs leave it. -/
def basisEnv : Env .anon :=
  ⟨[quotSoundA, quotIndA, quotLiftA, quotMkA, quotA, falseRecA, falseA, emptyRecA, emptyA,
    punitRecA, punitUnitA, punitA, natRecA, natSuccA, natZeroA, natA, eqRecA, eqReflA, eqA]⟩

/-- The roles keying `basisEnv1`, in its order. -/
def roles1 : List Role := [.eqRec, .eqRefl, .eq]

/-- The roles keying `basisEnv2`, in its order. -/
def roles2 : List Role := [.natRec, .natSucc, .natZero, .nat, .eqRec, .eqRefl, .eq]

/-- The roles keying `basisEnv3`, in its order. -/
def roles3 : List Role :=
  [.punitRec, .punitUnit, .punit, .natRec, .natSucc, .natZero, .nat, .eqRec, .eqRefl, .eq]

/-- The roles keying `basisEnv4`, in its order. -/
def roles4 : List Role :=
  [.emptyRec, .empty, .punitRec, .punitUnit, .punit, .natRec, .natSucc, .natZero, .nat,
   .eqRec, .eqRefl, .eq]

/-- The roles keying `basisEnv5`, in its order. -/
def roles5 : List Role :=
  [.falseRec, .false, .emptyRec, .empty, .punitRec, .punitUnit, .punit, .natRec, .natSucc,
   .natZero, .nat, .eqRec, .eqRefl, .eq]

/-- The roles keying `basisEnv`, in its order. -/
def basisRoleOrder : List Role :=
  [.quotSound, .quotInd, .quotLift, .quotMk, .quot, .falseRec, .false, .emptyRec, .empty,
   .punitRec, .punitUnit, .punit, .natRec, .natSucc, .natZero, .nat, .eqRec, .eqRefl, .eq]

theorem basisRun_eq : DeclBasisRun (Env.empty : Env .anon) .eqK basisEnv1 := by
  have h1 : ((Env.empty : Env .anon).find? (eqA : ConstantInfo .anon).name).isNone = true :=
    role_fresh [] .eq rfl (by decide)
  have h2 : ((⟨[eqA]⟩ : Env .anon).find? (eqReflA : ConstantInfo .anon).name).isNone = true :=
    role_fresh [.eq] .eqRefl rfl (by decide)
  have h3 : ((⟨[eqReflA, eqA]⟩ : Env .anon).find?
      (eqRecA : ConstantInfo .anon).name).isNone = true :=
    role_fresh [.eqRefl, .eq] .eqRec rfl (by decide)
  unfold DeclBasisRun
  refine ⟨(fun h => nomatch h), ?_⟩
  exact And.intro h1 (And.intro h2 (And.intro h3 rfl))

theorem basisRun_nat : DeclBasisRun basisEnv1 .natK basisEnv2 := by
  have h1 : (basisEnv1.find? (natA : ConstantInfo .anon).name).isNone = true :=
    role_fresh roles1 .nat rfl (by decide)
  have h2 : ((⟨natA :: basisEnv1.consts⟩ : Env .anon).find?
      (natZeroA : ConstantInfo .anon).name).isNone = true :=
    role_fresh (.nat :: roles1) .natZero rfl (by decide)
  have h3 : ((⟨natZeroA :: natA :: basisEnv1.consts⟩ : Env .anon).find?
      (natSuccA : ConstantInfo .anon).name).isNone = true :=
    role_fresh (.natZero :: .nat :: roles1) .natSucc rfl (by decide)
  have h4 : ((⟨natSuccA :: natZeroA :: natA :: basisEnv1.consts⟩ : Env .anon).find?
      (natRecA : ConstantInfo .anon).name).isNone = true :=
    role_fresh (.natSucc :: .natZero :: .nat :: roles1) .natRec rfl (by decide)
  unfold DeclBasisRun
  refine ⟨(fun h => nomatch h), ?_⟩
  exact And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 rfl)))

theorem basisRun_punit : DeclBasisRun basisEnv2 .punitK basisEnv3 := by
  have h1 : (basisEnv2.find? (punitA : ConstantInfo .anon).name).isNone = true :=
    role_fresh roles2 .punit rfl (by decide)
  have h2 : ((⟨punitA :: basisEnv2.consts⟩ : Env .anon).find?
      (punitUnitA : ConstantInfo .anon).name).isNone = true :=
    role_fresh (.punit :: roles2) .punitUnit rfl (by decide)
  have h3 : ((⟨punitUnitA :: punitA :: basisEnv2.consts⟩ : Env .anon).find?
      (punitRecA : ConstantInfo .anon).name).isNone = true :=
    role_fresh (.punitUnit :: .punit :: roles2) .punitRec rfl (by decide)
  unfold DeclBasisRun
  refine ⟨(fun h => nomatch h), ?_⟩
  exact And.intro h1 (And.intro h2 (And.intro h3 rfl))

theorem basisRun_empty : DeclBasisRun basisEnv3 .emptyK basisEnv4 := by
  have h1 : (basisEnv3.find? (emptyA : ConstantInfo .anon).name).isNone = true :=
    role_fresh roles3 .empty rfl (by decide)
  have h2 : ((⟨emptyA :: basisEnv3.consts⟩ : Env .anon).find?
      (emptyRecA : ConstantInfo .anon).name).isNone = true :=
    role_fresh (.empty :: roles3) .emptyRec rfl (by decide)
  unfold DeclBasisRun
  refine ⟨(fun h => nomatch h), ?_⟩
  exact And.intro h1 (And.intro h2 rfl)

theorem basisRun_false : DeclBasisRun basisEnv4 .falseK basisEnv5 := by
  have h1 : (basisEnv4.find? (falseA : ConstantInfo .anon).name).isNone = true :=
    role_fresh roles4 .false rfl (by decide)
  have h2 : ((⟨falseA :: basisEnv4.consts⟩ : Env .anon).find?
      (falseRecA : ConstantInfo .anon).name).isNone = true :=
    role_fresh (.false :: roles4) .falseRec rfl (by decide)
  unfold DeclBasisRun
  refine ⟨(fun h => nomatch h), ?_⟩
  exact And.intro h1 (And.intro h2 rfl)

/-- `Eq` is in the environment the quotient package is installed over. -/
theorem basisEnv5_eq : basisEnv5.find? eqName = some eqA :=
  Ix.Cert.AcceptedKeys.find?_name_of_nodup (l := basisEnv5.consts)
    (roleNames_nodup roles5 rfl (by decide)) eqA (by simp [basisEnv5])

theorem basisRun_quot : DeclBasisRun basisEnv5 .quotK basisEnv := by
  have h1 : (basisEnv5.find? (quotA : ConstantInfo .anon).name).isNone = true :=
    role_fresh roles5 .quot rfl (by decide)
  have h2 : ((⟨quotA :: basisEnv5.consts⟩ : Env .anon).find?
      (quotMkA : ConstantInfo .anon).name).isNone = true :=
    role_fresh (.quot :: roles5) .quotMk rfl (by decide)
  have h3 : ((⟨quotMkA :: quotA :: basisEnv5.consts⟩ : Env .anon).find?
      (quotLiftA : ConstantInfo .anon).name).isNone = true :=
    role_fresh (.quotMk :: .quot :: roles5) .quotLift rfl (by decide)
  have h4 : ((⟨quotLiftA :: quotMkA :: quotA :: basisEnv5.consts⟩ : Env .anon).find?
      (quotIndA : ConstantInfo .anon).name).isNone = true :=
    role_fresh (.quotLift :: .quotMk :: .quot :: roles5) .quotInd rfl (by decide)
  have h5 : ((⟨quotIndA :: quotLiftA :: quotMkA :: quotA :: basisEnv5.consts⟩ :
      Env .anon).find? (quotSoundA : ConstantInfo .anon).name).isNone = true :=
    role_fresh (.quotInd :: .quotLift :: .quotMk :: .quot :: roles5) .quotSound rfl (by decide)
  unfold DeclBasisRun
  refine ⟨fun _ => basisEnv5_eq, ?_⟩
  exact And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 (And.intro h5 rfl))))

/-- **The pinned basis environment has a model in every set theory.** -/
theorem basisEnv_model (W : Type u) [Ix.Kernel.SetTheory W] :
    Nonempty (Ix.Kernel.Model W basisEnv) := by
  obtain ⟨m1, -⟩ := Ix.Kernel.Model.basisStepExt
    (Ix.Kernel.Model.EnvModelM.empty W .verified) basisRun_eq
  obtain ⟨m2, -⟩ := Ix.Kernel.Model.basisStepExt m1 basisRun_nat
  obtain ⟨m3, -⟩ := Ix.Kernel.Model.basisStepExt m2 basisRun_punit
  obtain ⟨m4, -⟩ := Ix.Kernel.Model.basisStepExt m3 basisRun_empty
  obtain ⟨m5, -⟩ := Ix.Kernel.Model.basisStepExt m4 basisRun_false
  obtain ⟨m6, -⟩ := Ix.Kernel.Model.basisStepExt m5 basisRun_quot
  exact ⟨Ix.Kernel.Model.Model.ofEnvModelM m6⟩

/-- No pinned basis constant is a model-family constant. -/
theorem basisEnv_claimed : claimedEnv basisEnv = basisEnv := rfl

theorem basisEnv_nodup : (basisEnv.consts.map (·.name)).Nodup :=
  roleNames_nodup basisRoleOrder rfl (by decide)

/-- The pinned basis environment is the six pinned blocks, last installed first. -/
theorem basisEnv_consts :
    basisEnv.consts =
      (BasisKind.quotK.declsA : List (ConstantInfo .anon)).reverse ++
        ((BasisKind.falseK.declsA : List (ConstantInfo .anon)).reverse ++
          ((BasisKind.emptyK.declsA : List (ConstantInfo .anon)).reverse ++
            ((BasisKind.punitK.declsA : List (ConstantInfo .anon)).reverse ++
              ((BasisKind.natK.declsA : List (ConstantInfo .anon)).reverse ++
                (BasisKind.eqK.declsA : List (ConstantInfo .anon)).reverse)))) :=
  rfl

theorem basisEnv_pinned : ∀ ci ∈ basisEnv.consts, PinnedBasis ci := by
  intro ci h
  rw [basisEnv_consts] at h
  simp only [List.mem_append, List.mem_reverse] at h
  unfold PinnedBasis
  rcases h with h | h | h | h | h | h
  · exact ⟨.quotK, h⟩
  · exact ⟨.falseK, h⟩
  · exact ⟨.emptyK, h⟩
  · exact ⟨.punitK, h⟩
  · exact ⟨.natK, h⟩
  · exact ⟨.eqK, h⟩

theorem basisEnv_pins : ∀ (kind : BasisKind),
    ∀ ci ∈ (kind.declsA : List (ConstantInfo .anon)), ci ∈ basisEnv.consts := by
  intro kind ci h
  rw [basisEnv_consts]
  simp only [List.mem_append, List.mem_reverse]
  cases kind with
  | eqK => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  | natK => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  | punitK => exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  | emptyK => exact Or.inr (Or.inr (Or.inl h))
  | falseK => exact Or.inr (Or.inl h)
  | quotK => exact Or.inl h

/-! ## The empty store -/

theorem emptyMap_get? {α : Type} (a : _root_.Address) :
    ({} : Std.HashMap _root_.Address α).get? a = none := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]

theorem emptyStore_consts (a : _root_.Address) : ({} : Ixon.Env).consts.get? a = none :=
  emptyMap_get? a

theorem emptyStore_blobs (a : _root_.Address) : ({} : Ixon.Env).blobs.get? a = none :=
  emptyMap_get? a

theorem emptyStore_record (a : _root_.Address) : recordOf ({} : Ixon.Env) a = none :=
  (congrArg
    (fun (o : Option Ixon.LazyConstant) =>
      o.bind fun lc => (Ixon.deConstantExact lc.rawBytes).toOption)
    (emptyStore_consts a)).trans rfl

/-! ## The inhabitant -/

/-- **The public part of table validity is satisfiable**: the committed default table, the
empty store and the pinned basis environment, on the empty set of groups. -/
theorem tableShape_basis :
    ∃ t : RoleTable, TableShape.{u} t (fun _ => False) ({} : Ixon.Env) basisEnv := by
  obtain ⟨b₀, t₀, hdef, hadm⟩ := IxVM.Refinement.Assembly.defaultAdmits
  have hpin : PreludePinned t₀ := by
    unfold PreludePinned
    exact ⟨b₀, t₀, hdef, hadm, fun _ _ => rfl⟩
  have hlit : IxVM.Refinement.LiteralSupportBound t₀ := by
    rw [IxVM.Refinement.RoleVal.admitBinding_committedDefault hdef hadm]
    exact IxVM.Refinement.RoleVal.committedDefaultRoleTable_literalSupportBound
  have hhashed : EnvSelfHashed ({} : Ixon.Env) := by
    unfold EnvSelfHashed
    constructor
    · intro _ _ h
      rw [emptyStore_consts] at h
      cases h
    · intro _ _ h
      rw [emptyStore_blobs] at h
      cases h
  have hused : UsedClosed ({} : Ixon.Env) := by
    unfold UsedClosed
    constructor
    · intro _ _ h
      rw [emptyStore_record] at h
      cases h
    · intro _ _ _ h
      rw [emptyStore_record] at h
      cases h
  have hcommitted : AgreesCommitted ({} : Ixon.Env) := by
    unfold AgreesCommitted
    intro _ _ _ h
    rw [emptyStore_consts] at h
    cases h
  have hreading : ReadingOf t₀ ({} : Ixon.Env) basisEnv := by
    refine ⟨basisEnv_nodup, ?_, ?_⟩
    · intro ci hci
      rw [basisEnv_claimed] at hci
      exact Or.inr (Or.inl (basisEnv_pinned ci hci))
    · intro _ hr
      obtain ⟨_, _, hc, -⟩ := hr
      rw [emptyStore_record] at hc
      cases hc
  refine ⟨t₀, ?_⟩
  exact {
    needsClosed := fun _ hg => hg.elim
    bound := fun _ hg => hg.elim
    prelude := hpin
    literals := hlit
    hashed := hhashed
    usedClosed := hused
    committed := hcommitted
    zeroFree := ⟨emptyStore_consts _, emptyStore_blobs _⟩
    kept := fun _ _ _ hg => hg.elim
    reading := hreading
    pins := basisEnv_pins
    preludeKept := fun _ _ _ hg => hg.elim
    model := fun W _ => by
      rw [basisEnv_claimed]
      exact basisEnv_model W }

/-- **`TableWitness` is satisfiable** with `Facts` taken to be `True`: every public field is
inhabited jointly. A `Facts` that the typing half can continue from must supply, for the
same store and environment, the invariant its declaration steps preserve and the role shapes
the core's rules read; this inhabitant says nothing about those. -/
theorem tableWitness_basis :
    ∃ t : RoleTable,
      TableWitness.{u} (fun _ _ _ _ => True) t (fun _ => False) ({} : Ixon.Env) basisEnv := by
  obtain ⟨t, h⟩ := tableShape_basis.{u}
  exact ⟨t, ⟨h, trivial⟩⟩

end IxVM.Refinement.TableInhabit
