import IxVMRefinement.Binding.ClauseInvariant
import IxVMRefinement.TwinFamily.Target
import IxVMRefinement.TwinFamily.Reload
import IxVMRefinement.Assembly.PointTable

/-! # The binding fold's family form: the step of a block with its family record

`OverUnitStep` (`Binding/ClauseInvariant.lean`) is the step of one closure unit: it is handed the
used references of one record stored and stores constants at that record's constant addresses.
A block that the circuit routes as modeled is checked together with its family record (a block
of recursors at another address, named by the claim's payload) against advice records that only
the payload names (`KernelModeled::check_family`). Its step is the analogue of the typing half's
`UnitStepFamily` at the binding fold's clause:

* `OverUnitStepFamily L t G R envT E₀ B cb rb crb adv`: from the clause at one registry at every
  record store for `R` and every carried limit within `G`, at an environment that stores what
  the block, its family record and its advice use and the advice's own constant addresses, and
  none of the two records' constant addresses: fresh constants keep the clause with a registry,
  store at each constant address of the block and of the family record a constant that stores
  its reading, install the family record (each recursor with its model companion,
  `FamilyInstalled`), and store nothing else outside derived keys. No name is an operation's.
* `OverUnitStepTwin L t G R envT E₀ A c rb crb`: the step of a second family record `A` of a
  block whose family record `rb` the environment holds installed, at the binding fold's clause
  (the analogue of the typing half's `UnitStepTwin`).

Neither names a limit: the family check of a unit of group `g` runs at the group's validation
limit, one of the carried limits. -/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Typing.TwinFamily (FamilyInstalled TwinMemberLoaded)
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)

/-- **The stored recursors' loaded form, self-mention scoping, and `check_recs` header counts** of
a block `B` (`cb`) and its selected family record `rb` (`crb`) in store `R` and environment `env`:
each recursor member `k` (`rs[k]? = some (.recr rc)`) has a reading in `R` stored in `env` at its
key, loaded with canonical binder annotations (`TwinMemberLoaded`), matching level parameters and
argument counts (`mI`, `rP`), whose stored type mentions no recursor key of `rb`, whose parameter
count matches the block's first inductive, whose motive count is `rs.size`, whose index count
matches the major premise's inductive in `R`, and whose type after stripping `mI + 1` binders at
positional levels leaves a non-`forallE` conclusion. -/
structure StoredFamilyRecs (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (B : _root_.Address) (cb : Ixon.Constant) (rb : _root_.Address) (crb : Ixon.Constant) :
    Prop where
  member : ∀ (ms rs : Array Ixon.MutConst) (k : Nat) (rc : Ixon.Recursor),
    cb.info = .muts ms → crb.info = .muts rs → rs[k]? = some (.recr rc) →
    ∃ (cv : Ix.Kernel.ConstantVal .anon) (mI rP : Nat) (rules₀ : List (Ix.Kernel.RecRule .anon))
      (cv' : Ix.Kernel.ConstantVal .anon) (rules' : List (Ix.Kernel.RecRule .anon)),
      k < UInt64.size ∧
      RecReads t (recordOf R) (fun x => R.blobs.get? x) crb (blockSelf t rb rs)
        (keyOf t (memberAddr rb k (.recr rc))) rc (.recInfo cv mI rP rules₀) ∧
      env.find? (keyOf t (memberAddr rb k (.recr rc))) = some (.recInfo cv' mI rP rules') ∧
      cv'.name = cv.name ∧ cv'.levelParams = cv.levelParams ∧
      StoredAs (.recInfo cv' mI rP rules') (.recInfo cv mI rP rules₀) ∧
      TwinMemberLoaded crb rs ⟨k.toUInt64, rb⟩ rc cv.levelParams cv.type rules₀ cv' rules' ∧
      (∀ (j : Nat) (rc_j : Ixon.Recursor), rs[j]? = some (.recr rc_j) →
        cv'.type.mentionsConst (keyOf t (memberAddr rb j (.recr rc_j))) = false) ∧
      (∀ (ind₀ : Ixon.Inductive), ms[0]? = some (.indc ind₀) →
        rc.params.toNat = ind₀.params.toNat) ∧
      rc.motives.toNat = rs.size ∧
      (∃ (Bm : _root_.Address) (im : Nat) (cbm : Ixon.Constant) (msm : Array Ixon.MutConst)
        (indm : Ixon.Inductive) (D : Core.KExpr) (lvls : List Core.KLevel),
        im < UInt64.size ∧
        recordOf R (memberAddr Bm im (.indc indm)) = some (memberProjection Bm im (.indc indm)) ∧
        recordOf R Bm = some cbm ∧ cbm.info = .muts msm ∧ msm[im]? = some (.indc indm) ∧
        Core.piDomAt mI cv'.type = some D ∧
        D.getAppFn = .const (keyOf t (memberAddr Bm im (.indc indm))) lvls ∧
        rc.indices.toNat = indm.indices.toNat) ∧
      (∃ bs concl, (Core.posOf cv'.levelParams cv'.type).stripPis (mI + 1) = some (bs, concl) ∧
        ∀ d b m, concl ≠ .forallE d b m)

/-- **The stored recursor facts pass to any larger store and environment that keep lookups.** -/
theorem StoredFamilyRecs.mono {t : Ix.Kernel.RoleTable} {R₁ R' : Ixon.Env}
    {env₁ env' : Ix.Kernel.Env .anon} {B rb : _root_.Address} {cb crb : Ixon.Constant}
    (hle : ∀ a c, recordOf R₁ a = some c → recordOf R' a = some c)
    (hblob : ∀ x b, R₁.blobs.get? x = some b → R'.blobs.get? x = some b)
    (hfind : ∀ {k : Ix.Kernel.Key .anon} {ci : Ix.Kernel.ConstantInfo .anon},
      env₁.find? k = some ci → env'.find? k = some ci)
    (h : StoredFamilyRecs t R₁ env₁ B cb rb crb) : StoredFamilyRecs t R' env' B cb rb crb where
  member := fun ms rs k rc hms hrs hk => by
    obtain ⟨cv, mI, rP, rules₀, cv', rules', hku, hRR, hf, hnm, hlp, hSA, hTML, hns, hnp, hmot,
      ⟨Bm, im, cbm, msm, indm, D, lvls, himu, hPm, hBm, hmsm, him, hpi, hfn, hni⟩, hconcl⟩ :=
      h.member ms rs k rc hms hrs hk
    exact ⟨cv, mI, rP, rules₀, cv', rules', hku, ReaderReads.recReads_mono hle hblob hRR,
      hfind hf, hnm, hlp, hSA, hTML, hns, hnp, hmot,
      ⟨Bm, im, cbm, msm, indm, D, lvls, himu, hle _ _ hPm, hle _ _ hBm, hmsm, him, hpi, hfn, hni⟩,
      hconcl⟩

/-- **The stored recursor facts stay valid in any extending environment with distinct names.** -/
theorem StoredFamilyRecs.mono_env {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {env env' : Ix.Kernel.Env .anon} {B rb : _root_.Address} {cb crb : Ixon.Constant}
    (hext : ∀ ci ∈ env.consts, ci ∈ env'.consts) (hnd : (env'.consts.map (·.name)).Nodup)
    (h : StoredFamilyRecs t R env B cb rb crb) : StoredFamilyRecs t R env' B cb rb crb :=
  h.mono (fun _ _ h => h) (fun _ _ h => h) (fun hk => find_of_ext hext hnd hk)

/-- **Universal `recLoaded` projection** matching `FamilyMembersCanon.recLoaded`, over `R`. -/
theorem StoredFamilyRecs.recLoaded {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {R : Ixon.Env} {env : Ix.Kernel.Env .anon} {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {ms rs : Array Ixon.MutConst} (h : StoredFamilyRecs t R env B cb rb crb)
    (hms : cb.info = .muts ms) (hrs : crb.info = .muts rs)
    (p : Ixon.RecursorProj) (rc : Ixon.Recursor) (cv : Ix.Kernel.ConstantVal .anon)
    (mI rP : Nat) (rules₀ : List (Ix.Kernel.RecRule .anon)) (cv' : Ix.Kernel.ConstantVal .anon)
    (mI' rP' : Nat) (rules' : List (Ix.Kernel.RecRule .anon))
    (hp : p.block = rb) (hm : rs[p.idx.toNat]? = some (.recr rc))
    (hRR : RecReads t (recordOf R) (fun x => R.blobs.get? x) crb (blockSelf t rb rs)
      (keyOf t (memberAddr rb p.idx.toNat (.recr rc))) rc (.recInfo cv mI rP rules₀))
    (hf : env.find? (keyOf t (memberAddr rb p.idx.toNat (.recr rc))) =
      some (.recInfo cv' mI' rP' rules')) :
    TwinMemberLoaded crb rs p rc cv.levelParams cv.type rules₀ cv' rules' := by
  obtain ⟨cv₁, mI₁, rP₁, rules₁, cv'₁, rules'₁, -, hRR₁, hf₁, -, -, -, hTML, -⟩ :=
    h.member ms rs p.idx.toNat rc hms hrs hm
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have eci := RecReads.same hroles hRR₁ hRR
  injection eci with hcv _ _ hrl
  have ef := Option.some.inj (hf₁.symm.trans hf)
  injection ef with hcv' _ _ hrl'
  have hp' : (⟨p.idx.toNat.toUInt64, rb⟩ : Ixon.RecursorProj) = p := by
    cases p with
    | mk idx blk =>
      dsimp only at hp ⊢
      subst hp
      have hidx : idx.toNat.toUInt64 = idx := UInt64.ofNat_toNat
      rw [hidx]
  rw [hp', hcv, hrl, hcv', hrl'] at hTML
  exact hTML

/-- **Universal `recNoSelf` projection**: no stored recursor type mentions any recursor key of
the family record. -/
theorem StoredFamilyRecs.recNoSelf {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {ms rs : Array Ixon.MutConst} (h : StoredFamilyRecs t R env B cb rb crb)
    (hms : cb.info = .muts ms) (hrs : crb.info = .muts rs)
    {k j : Nat} {rc_k rc_j : Ixon.Recursor} {cv' : Ix.Kernel.ConstantVal .anon}
    {mI' rP' : Nat} {rules' : List (Ix.Kernel.RecRule .anon)}
    (hk : rs[k]? = some (.recr rc_k)) (hj : rs[j]? = some (.recr rc_j))
    (hf : env.find? (keyOf t (memberAddr rb k (.recr rc_k))) =
      some (.recInfo cv' mI' rP' rules')) :
    cv'.type.mentionsConst (keyOf t (memberAddr rb j (.recr rc_j))) = false := by
  obtain ⟨_, _, _, _, cv'₁, _, -, -, hf₁, -, -, -, -, hns, -⟩ := h.member ms rs k rc_k hms hrs hk
  have ef := Option.some.inj (hf₁.symm.trans hf)
  injection ef with hcv' _ _ _
  rw [← hcv']
  exact hns j rc_j hj

/-- **The step of a block with its family record, over the fold's clause** (module docstring).
`adv` is the advice of the block's family check. -/
def OverUnitStepFamily (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env) (envT : Ix.Kernel.Env .anon)
    (E₀ : Ixon.Env) (B : _root_.Address) (cb : Ixon.Constant) (rb : _root_.Address)
    (crb : Ixon.Constant) (adv : _root_.Address → Prop) : Prop :=
  ∀ (env : Ix.Kernel.Env .anon) (Reg : NativeFam .anon → Prop),
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    (∀ E, RecordsFor R E → ∀ lim, Carried lim → LimWithin G t lim →
      FoldClauseWith.{u} L t E lim env Reg) →
    (∀ x, UsedRef E₀ B x ∨ UsedRef E₀ rb x →
      (env.find? (keyOf t x)).isSome = true ∨ FamAddr B cb rb crb x ∨ ¬ NeedOk E₀ x) →
    (∀ a, adv a → ∀ ca, recordOf E₀ a = some ca → ∀ x, ConstAddrOf a ca x →
      (env.find? (keyOf t x)).isSome = true) →
    (∀ a, adv a → ∀ x, UsedRef E₀ a x →
      (env.find? (keyOf t x)).isSome = true ∨ FamAddr B cb rb crb x ∨ ¬ NeedOk E₀ x) →
    (∀ x, FamAddr B cb rb crb x → env.find? (keyOf t x) = none) →
    ∃ (new : List (Ix.Kernel.ConstantInfo .anon)) (Reg' : NativeFam .anon → Prop),
      (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, env.find? ci.name = none) ∧
      (∀ E, RecordsFor R E → ∀ lim, Carried lim → LimWithin G t lim →
        FoldClauseWith.{u} L t E lim ⟨new ++ env.consts⟩ Reg') ∧
      (∀ ci ∈ new, ci.name ∉ RoleOps.opNames) ∧
      (∀ x, FamAddr B cb rb crb x →
        ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀) ∧
      FamilyInstalled t ⟨new ++ env.consts⟩ rb crb ∧
      StoredFamilyRecs t R ⟨new ++ env.consts⟩ B cb rb crb ∧
      ∀ ci ∈ new, (∃ x, FamAddr B cb rb crb x ∧ ci.name = keyOf t x) ∨ ∃ k s, ci.name = .aux k s

/-- **The step of a second family record of a block, over the fold's clause** (module
docstring): `OverUnitStep` of the record at `A`, handed in addition the family record `rb` of its
block installed and storing its readings in `E₀`. -/
def OverUnitStepTwin (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env) (envT : Ix.Kernel.Env .anon)
    (E₀ : Ixon.Env) (A : _root_.Address) (c : Ixon.Constant) (rb : _root_.Address)
    (crb : Ixon.Constant) : Prop :=
  ∀ (env : Ix.Kernel.Env .anon) (Reg : NativeFam .anon → Prop),
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    (∀ E, RecordsFor R E → ∀ lim, Carried lim → LimWithin G t lim →
      FoldClauseWith.{u} L t E lim env Reg) →
    (∀ x, UsedRef E₀ A x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk E₀ x) →
    FamilyInstalled t env rb crb →
    (∀ x, ConstAddrOf rb crb x →
      ∃ ci ci₀, env.find? (keyOf t x) = some ci ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀) →
    (∀ x, ConstAddrOf A c x → env.find? (keyOf t x) = none) →
    ∃ (new : List (Ix.Kernel.ConstantInfo .anon)) (Reg' : NativeFam .anon → Prop),
      (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, env.find? ci.name = none) ∧
      (∀ E, RecordsFor R E → ∀ lim, Carried lim → LimWithin G t lim →
        FoldClauseWith.{u} L t E lim ⟨new ++ env.consts⟩ Reg') ∧
      (∀ ci ∈ new, ci.name ∉ RoleOps.opNames) ∧
      (∀ x, ConstAddrOf A c x →
        ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀) ∧
      ∀ ci ∈ new, (∃ x, ConstAddrOf A c x ∧ ci.name = keyOf t x) ∨ ∃ k s, ci.name = .aux k s

/-- **A family installed by a step stays installed in every later environment** with distinct
names: what the family step's conclusion gives the rest of the fold. -/
theorem familyInstalled_mono {t : Ix.Kernel.RoleTable} {env env' : Ix.Kernel.Env .anon}
    {rb : _root_.Address} {crb : Ixon.Constant}
    (hext : ∀ ci ∈ env.consts, ci ∈ env'.consts) (hnd : (env'.consts.map (·.name)).Nodup)
    (h : FamilyInstalled t env rb crb) : FamilyInstalled t env' rb crb := by
  intro x hx
  obtain ⟨⟨cv, mI, rP, rules, hf⟩, hm⟩ := h x hx
  exact ⟨⟨cv, mI, rP, rules, find_of_ext hext hnd hf⟩,
    Ix.Kernel.Model.HasModel.mono (fun hk => find_of_ext hext hnd hk) hm⟩

end IxVM.Refinement.Binding
