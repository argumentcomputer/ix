import IxVMRefinement.Assembly.PointClauses
import IxVMRefinement.Assembly.PointGateLoads
import IxVMRefinement.Assembly.PointTable

/-! # The per-record step of a block on the constructors-only route

`unitStep_pointBlock`: the skeleton's `UnitStep` for a block the circuit routes to its modeled
branch (two or more inductive types, or one with a nested occurrence), whose recursors the
circuit refuses. The unit installs the block's types and constructors only, with the one-point
model (`Decl.Point.pointBlock_install`), and keeps the carried clause
`((LateRegistry ∧ HashKeyed) ∧ AuxRootSynced) ∧ LvClauses` (`PointX`), the registry with no new
entry.

The step at an environment `env` the fold hands it: the table facts (the block's keys are input
keys, `key_id_of_fresh`; the `PUnit` pin is stored, `punitPin_of_shape`); the block arm's
evidence (`PointEvidence`: the one-point interface `PointBlock` at `env` with the formers and
constructors the block's readings); the install as the store reads it (`PointInstall`, built
here); the load facts at the new constants (`PointLoadsFrom`); the prefix invariant there
(`PointBlock.prefixInv`) and the carried clause there (`PointBlock.lateRegistry`, `.hashKeyed`,
`.auxRootSynced`, `.lvClauses`).

Named inputs beyond those `unitStep_nativeBlock` takes:

* `hgate : PointShape E B ms`: two or more inductives, or the one-type facts `NestedGate`;
* `hunb`: no role `TableShape` leaves unstored (`StoredRole`) is bound at a constant address of
  the block;
* `hev : PointEvidence`: the refinement of the block's arm (the formers' and constructors'
  checks into `PointBlock`, with their readings);
* `hloads : PointLoadsFrom`: the load facts that reach the new constants of an install.
-/

namespace IxVM.Refinement.Typing

open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)
open IxVM.Refinement.Decl.Point

universe u

/-- **The carried clause** (the conjunction `NativeBlockX` names on the native route). -/
abbrev PointX (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon) : Prop :=
  ((LateRegistry.{u} t E env ∧ HashKeyed t env) ∧ Decl.AuxRootSynced env) ∧ LvClauses env

/-- **The refinement of the block's arm, as the step reads it**: at every environment that
satisfies the prefix invariant at the limit of the members' checks, stores what the block uses
and none of its constant addresses, keys them as input keys and stores the `PUnit` pin, the
one-point interface holds with formers and constructors that are the block's readings over the
step's store, every constant address of the block has a reading over the run's store among the
block's declared constants, and the members' counts are below `2 ^ 56` (each member's check
loaded its record). Producer: the refinement of the modeled branch of `check_const`'s `Induct`
arm (the formers: `pointFormer_of_member`; the constructors at the stage of the formers: open). -/
def PointEvidence (t : Ix.Kernel.RoleTable) (E₀ E : Ixon.Env) (B : _root_.Address)
    (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (n : Nat) : Prop :=
  ∀ env : Ix.Kernel.Env .anon, Decl.PrefixInv.{u} E t (some n) env →
    Decl.UsedRefsStored t env cb →
    (∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none) →
    (∀ x, ConstAddrOf B cb x → keyOf t x = .id x) → PUnitPin env →
    ∃ (formers : List FormerRec) (ctors : List CtorRec) (blk : List (ConstantInfo .anon)),
      PointBlock env blk formers ctors ∧ PointReads t E B cb ms formers ctors ∧
      (∀ x, ConstAddrOf B cb x → ∃ ci₀ ∈ blk, ci₀.name = keyOf t x ∧ Reads t E₀ x ci₀) ∧
      ∀ i ind, ms[i]? = some (.indc ind) →
        ind.params.toNat < 2 ^ 56 ∧ ind.indices.toNat < 2 ^ 56 ∧ ind.ctors.size < 2 ^ 56

/-- **The load facts that reach the new constants of a constructors-only install**, at every
prefix whose invariant holds. Producer: the reload fields of `PointInstall`
(`PointNewLoads.lean`) with the never-asked fields (`PointGateLoads.lean`). -/
def PointLoadsFrom (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (B : _root_.Address)
    (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (n : Nat) : Prop :=
  ∀ (env : Ix.Kernel.Env .anon) (new : List (ConstantInfo .anon)),
    PointInstall ⟨E, env, t, some n⟩ new B cb ms → Decl.PrefixInv.{u} E t (some n) env →
    Decl.AuxRootSynced env →
    (∀ k ind, ms[k]? = some (.indc ind) → env.find? (Core.keyOf t (Core.iprjAddr B k)) = none) →
    PointShape E B ms →
    NewLoads (appCtx ⟨E, env, t, some n⟩ new).stored new

section

variable {env : Ix.Kernel.Env .anon} {block : List (ConstantInfo .anon)} {formers : List FormerRec}
  {ctors : List CtorRec}

/-- A former the formers list holds is found at its key after the install. -/
theorem PointBlock.find_pointFormer (hb : PointBlock env block formers ctors)
    {t : Ix.Kernel.RoleTable} {B : _root_.Address} {i : Nat} {ind : Ixon.Inductive}
    {ty₀ ty' : Ix.Kernel.Expr .anon} {caps : IndCaps .anon}
    (hf : pointFormer t B i ind ty₀ caps ty' ∈ formers) :
    (⟨newConsts formers ctors ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
      (Core.keyOf t (Core.iprjAddr B i)) =
      some (.indInfo ⟨Core.keyOf t (Core.iprjAddr B i), List.range ind.lvls.toNat, ty'⟩ {}) := by
  have h := hb.find_former hf
  rw [installed_eq] at h
  exact h

/-- A constructor the constructors list holds is found at its key after the install. -/
theorem PointBlock.find_pointCtor (hb : PointBlock env block formers ctors)
    {t : Ix.Kernel.RoleTable} {B : _root_.Address} {i j : Nat} {ct : Ixon.Constructor}
    {cty₀ cty' : Ix.Kernel.Expr .anon} (hc : pointCtor t B i j ct cty₀ cty' ∈ ctors) :
    (⟨newConsts formers ctors ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
      (Core.keyOf t (Core.cprjAddr B i j)) =
      some (.ctorInfo ⟨Core.keyOf t (Core.cprjAddr B i j), List.range ct.lvls.toNat, cty'⟩
        ct.params.toNat ct.fields.toNat) := by
  have h := hb.find_ctor hc
  rw [installed_eq] at h
  exact h

/-- **The names of the new constants**: a former's is its member's projection key, a
constructor's its slot's. -/
theorem PointReads.newName {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {B : _root_.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} (hb : PointBlock env block formers ctors)
    (hR : PointReads t E B cb ms formers ctors) :
    ∀ ci ∈ newConsts formers ctors,
      (∃ i ind, ms[i]? = some (.indc ind) ∧ ci.name = Core.keyOf t (Core.iprjAddr B i)) ∨
      ∃ i ind j, ms[i]? = some (.indc ind) ∧ j < ind.ctors.size ∧
        ci.name = Core.keyOf t (Core.cprjAddr B i j) := by
  intro ci hci
  rcases hb.new_cases hci with ⟨f, hf, rfl⟩ | ⟨c, hc, rfl⟩
  · obtain ⟨i, ind, ty₀, ty', caps, hm, rfl, -⟩ := hR.formerOf f hf
    exact Or.inl ⟨i, ind, hm, rfl⟩
  · obtain ⟨i, ind, j, ct, cty₀, cty', hm, hct, rfl, -⟩ := hR.ctorOf c hc
    exact Or.inr ⟨i, ind, j, hm, (List.getElem?_eq_some_iff.mp hct).1, rfl⟩

end

/-- **The record of member `i` names the block at its projection address.** -/
theorem memberProjection_info (B : _root_.Address) (i : Nat) (ind : Ixon.Inductive) :
    (memberProjection B i (.indc ind)).info = .iPrj ⟨i.toUInt64, B⟩ := rfl

/-- **`UnitStep` for a block on the constructors-only route** (module docstring). The unit is the
block's record at `B`; its members are checked at the limit `n`. -/
theorem unitStep_pointBlock {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {R E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {B : _root_.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hshape : TableShape.{u} t (fun _ => True) R envT)
    (hrec : ModeledBlockRecord E₀ B cb ms) (hlim : lim = some n)
    (hgate : PointShape E B ms)
    (hunb : ∀ x, ConstAddrOf B cb x → ∀ r, ¬ StoredRole r → t.addressOf? r ≠ some x)
    (hP : HashedBlockProjectionsHeld E)
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hev : PointEvidence.{u} t E₀ E B cb ms n) (hloads : PointLoadsFrom.{u} t E B cb ms n) :
    UnitStep.{u} (PointX.{u} t E) t envT E₀ E lim B cb := by
  subst hlim
  intro env hext hnd hinv hXe href hfresh
  obtain ⟨⟨⟨hreg, hkeys⟩, haux⟩, hlv⟩ := hXe
  have htwf : t.wf = true := hinv.tableWf
  have hstored : Decl.UsedRefsStored t env cb :=
    usedRefsStored_of_cover (hcover env ⟨hext, href, hfresh⟩) hinert
  have hid : ∀ x, ConstAddrOf B cb x → keyOf t x = .id x := fun x hx =>
    key_id_of_fresh htwf hshape hext hnd (hfresh x hx) (hunb x hx)
  have hpin : PUnitPin env := punitPin_of_shape hshape hext hnd
  obtain ⟨formers, ctors, blk, hb, hR, hreads, hbounds⟩ := hev env hinv hstored hfresh hid hpin
  have hblockE : recordOf E B = some cb := hst.held hrec.record
  have hrecAt : Ix.Cert.recordAt E B = some cb := recordAt_of_recordOf hst.decoded hblockE
  have hmod : ModeledAt E B := PointShape.modeledAt hinv hrecAt hrec.muts hgate
  have heq : installed env formers ctors = ⟨newConsts formers ctors ++ env.consts⟩ :=
    installed_eq env formers ctors
  have hextN : Ix.Kernel.EnvExt env ⟨newConsts formers ctors ++ env.consts⟩ := by
    have h := hb.envExt
    rw [heq] at h
    exact h
  -- the install, as the store reads it
  have hI : PointInstall ⟨E, env, t, some n⟩ (newConsts formers ctors) B cb ms :=
    { check := ht
      decoded := hst.decoded
      held := hP
      block := hblockE
      muts := hrec.muts
      inds := hrec.inds
      formerRec := fun i ind hm => hst.held (hrec.former i ind hm)
      ctorRec := fun i ind hm j hj => hst.held (hrec.ctors i ind hm j hj)
      bounds := hbounds
      used := fun i hi x hx => by
        obtain ⟨ci, hci⟩ := hstored i hi x hx
        exact ⟨ci, hextN.find hci⟩
      former := fun i ind hm => by
        obtain ⟨ty₀, ty', caps, hf, hread, hlbb, hdef, hcanon⟩ := hR.formerAt i ind hm
        exact ⟨ty₀, ty', hread, hlbb, hdef, hcanon, hb.find_pointFormer hf⟩
      ctor := fun i ind hm j hj => by
        obtain ⟨ct, cty₀, cty', hct, hc, hcidx, hread, hlbb, hdef, hcanon⟩ :=
          hR.ctorAt i ind j hm hj
        exact ⟨ct, cty₀, cty', hct, hcidx, hread, hlbb, hdef, hcanon, hb.find_pointCtor hc⟩
      newName := hR.newName hb
      newFind := fun ci hci => by
        have h := hb.find_new hci
        rw [heq] at h
        exact h }
  -- the prefix invariant after the install
  have hinv₂ : Decl.PrefixInv.{u} E t (some n) (installed env formers ctors) :=
    hb.prefixInv hinv (hloads env _ hI hinv haux
      (fun k ind hk => hfresh (Core.iprjAddr B k)
        (Or.inr ⟨ms, k, .indc ind, hrec.muts, hk, Or.inl rfl⟩)) hgate)
  rw [heq] at hinv₂
  -- the carried clause after the install
  have hreg₂ : LateRegistry.{u} t E (installed env formers ctors) := by
    refine hb.lateRegistry hreg (fun P cm ip hP' hcm hinfo => ?_)
    obtain ⟨f, hf, hname⟩ := hP'
    obtain ⟨i, ind, ty₀, ty', caps, hm, rfl, -⟩ := hR.formerOf f hf
    have hPx : P = Core.iprjAddr B i :=
      Core.keyOf_inj htwf (a₁ := P) (a₂ := Core.iprjAddr B i) hname.symm
    subst hPx
    have hrecP : Ix.Cert.recordAt E (Core.iprjAddr B i) = some (memberProjection B i (.indc ind)) :=
      recordAt_of_recordOf hst.decoded (hst.held (hrec.former i ind hm))
    rw [hrecP] at hcm
    obtain rfl := Option.some.inj hcm
    rw [memberProjection_info] at hinfo
    injection hinfo with hip
    rw [← hip]
    exact hmod
  have hkeys₂ : HashKeyed t (installed env formers ctors) := by
    refine hb.hashKeyed htwf hkeys (fun x hx => ?_)
    rcases hR.newName hb x hx with ⟨i, ind, hm, hname⟩ | ⟨i, ind, j, hm, hj, hname⟩
    · exact ⟨_, hname, address_size_of_record hS (hrec.former i ind hm)⟩
    · exact ⟨_, hname, address_size_of_record hS (hrec.ctors i ind hm j hj)⟩
  have haux₂ := hb.auxRootSynced haux
  have hlv₂ := hb.lvClauses hlv
  rw [heq] at hreg₂ hkeys₂ haux₂ hlv₂
  refine ⟨newConsts formers ctors, hb.freshChain.nodup, hb.freshChain.fresh, hinv₂,
    ⟨⟨⟨hreg₂, hkeys₂⟩, haux₂⟩, hlv₂⟩, ?_, ?_⟩
  · -- every constant address holds a new constant storing a reading of it
    intro x hx
    obtain ⟨ci₀, hci₀, hname₀, hread₀⟩ := hreads x hx
    obtain ⟨ci, hfind, hsto⟩ := hb.stored ci₀ hci₀
    have hnm : ci.name = keyOf t x := (Ix.Kernel.Semantics.Env.find?_name hfind).trans hname₀
    have hmem : ci ∈ newConsts formers ctors := by
      rcases hb.find_cases hfind with h | ⟨f, hf, rfl⟩ | ⟨c, hc, rfl⟩
      · rw [hname₀, hfresh x hx] at h
        cases h
      · exact hb.mem_new_former hf
      · exact hb.mem_new_ctor hc
    exact ⟨ci, hmem, ci₀, hnm, hread₀, hsto⟩
  · intro ci hci
    left
    rcases hR.newName hb ci hci with ⟨i, ind, hm, hname⟩ | ⟨i, ind, j, hm, hj, hname⟩
    · exact ⟨Core.iprjAddr B i, Or.inr ⟨ms, i, .indc ind, hrec.muts, hm, Or.inl rfl⟩, hname⟩
    · exact ⟨Core.cprjAddr B i j,
        Or.inr ⟨ms, i, .indc ind, hrec.muts, hm, Or.inr ⟨ind, j, rfl, hj, rfl⟩⟩, hname⟩

end IxVM.Refinement.Typing
