import IxVMRefinement.Assembly.PointUseSites
import IxVMRefinement.Assembly.StoreArClauses
import IxVMRefinement.Assembly.NativeBlockRegister
import IxVMRefinement.Decl.EtaOpen

/-! # The carried clauses and the prefix invariant after a constructors-only install

At a block on the constructors-only route the install is `Decl.Point.installed env formers
ctors`: the prefix with the block's types (at the empty capability record) and constructors in
front, nothing else. This file carries the fold's clauses across it:

* `PointBlock.envModelN`, `PointBlock.lateRegistry`: the registry of native families is kept with
  no new entry. The model step is the one-point chain (`Decl.Point.pointRun_chain`), which extends
  every model it is given, so every registered family's data cross it (`EnvModelN.step`); no new
  family is one the circuit treats as native, which is the dispatch's answer at the block in every
  good run (`ModeledAt`);
* `PointBlock.hashKeyed`: the new names are keys of addresses of 32 bytes;
* `storeArR_pointRun`, `PointBlock.thmLevels`, `PointBlock.lvClauses`: the level clauses (no
  theorem is stored; every stored type is arity-correct and resolves, from its front door);
* `PointBlock.prefixInv`: the prefix invariant at the installed environment, from the prefix's
  and the load facts that reach the new constants (`NewLoads`).
-/

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)
open Ix.Kernel.Semantics (NativeFam)
open Ix.Kernel.Model (EnvModelN StoreArR ArRes ConstArR)
open IxVM.Refinement.Decl.Point

universe u

section

variable {env : Ix.Kernel.Env .anon} {block : List (ConstantInfo .anon)} {formers : List FormerRec}
  {ctors : List CtorRec}

/-! ## The registry -/

/-- **The install extends every model it is given**, so it keeps every registry. -/
theorem _root_.IxVM.Refinement.Decl.Point.PointBlock.envModelN (hb : PointBlock env block formers ctors) (V : Type u)
    [Ix.Kernel.SetTheory V] {R : NativeFam .anon → Prop}
    (h : EnvModelN V .verified env R) : EnvModelN V .verified (installed env formers ctors) R :=
  EnvModelN.step V h fun mp hT hE => by
    have hch : Chain (formers.map (·.cv.name)) mp mp :=
      { twin := Twin.refl env
        acval := rfl
        shadowed := fun T hT cvT caps hf => by
          obtain ⟨f, hf', rfl⟩ := List.mem_map.mp hT
          rw [hb.freshF f hf'] at hf
          exact nomatch hf
        closedT := hE
        closedD := hE
        pin := hb.pin }
    obtain ⟨mp₂, hext, hE₂⟩ := pointRun_chain _ _ mp mp hch hb.run
    exact ⟨hE₂, mp₂, hext⟩

/-- **The install keeps the registry of native families, with no new entry**, where no former's
record names a block the circuit treats as native. -/
theorem _root_.IxVM.Refinement.Decl.Point.PointBlock.lateRegistry {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    (hb : PointBlock env block formers ctors) (hreg : LateRegistry.{u} t E env)
    (hnat : ∀ (P : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj),
      (∃ f ∈ formers, f.cv.name = keyOf t P) → Ix.Cert.recordAt E P = some cm →
      cm.info = .iPrj ip → ¬ NativeAt E ip.block) :
    LateRegistry.{u} t E (installed env formers ctors) := by
  obtain ⟨Reg, hR⟩ := hreg
  refine ⟨Reg, hR.step (fun V _ h => hb.envModelN V h) hb.envExt ?_⟩
  intro P cm ip cv caps hf hold hcm hinfo hnat'
  exfalso
  rcases hb.find_cases hf with h | ⟨f, hf', hx⟩ | ⟨c, hc, hx⟩
  · rw [hold] at h
    cases h
  · have hname : cv.name = keyOf t P := Ix.Kernel.Semantics.Env.find?_name hf
    have hcv : cv.name = f.cv.name := by
      unfold FormerRec.stored at hx
      injection hx with hx1 _
      rw [hx1]
    exact hnat P cm ip ⟨f, hf', hcv.symm.trans hname⟩ hcm hinfo hnat'
  · unfold CtorRec.stored at hx
    cases hx

/-! ## Keys -/

/-- **The new names are keys of 32-byte addresses**, so the store clause is kept. -/
theorem _root_.IxVM.Refinement.Decl.Point.PointBlock.hashKeyed {t : Ix.Kernel.RoleTable} (htwf : t.wf = true)
    (hb : PointBlock env block formers ctors) (h : HashKeyed t env)
    (hsz : ∀ x ∈ newConsts formers ctors,
      ∃ a : _root_.Address, x.name = Core.keyOf t a ∧ a.hash.size = 32) :
    HashKeyed t (installed env formers ctors) := by
  rw [installed_eq]
  exact HashKeyed.append htwf h (fun ci hci => Or.inl (hsz ci hci))

/-! ## The level clauses -/

/-- **A run of members keeps `StoreArR`**: each member is fresh, is no definition, and has a type
that is arity-correct and resolves where it is checked (its front door). -/
theorem storeArR_pointRun {F : List (Ix.Kernel.Key .anon)} :
    ∀ (members : List (ConstantInfo .anon)) {env env₂ : Ix.Kernel.Env .anon},
      PointRun F env members env₂ → StoreArR env → StoreArR env₂
  | [], env, env₂, hrun, h => by
    have he : env₂ = env := hrun
    rw [he]
    exact h
  | ci :: rest, env, env₂, hrun, h => by
    obtain ⟨ciA, hm, hrest⟩ := hrun
    obtain ⟨type', hcv, -, hkind⟩ := hm.kind
    have hfresh : env.find? ci.toConstantVal.name = none := Option.isNone_iff_eq_none.mp hcv.1
    have hname : ciA.name = ci.toConstantVal.name := by
      rcases hkind with rfl | ⟨nP, nF, rfl⟩ <;> rfl
    have hfreshA : env.find? ciA.name = none := by
      rw [hname]
      exact hfresh
    have har : ArRes ⟨ciA :: env.consts⟩ type' :=
      (Ix.Kernel.Model.arRes_of_cvRun hcv).mono (Ix.Kernel.Model.find?_cons_fresh_ext hfreshA)
    have hc : ConstArR ⟨ciA :: env.consts⟩ ciA := by
      rcases hkind with rfl | ⟨nP, nF, rfl⟩
      · exact ConstArR.of_ind har
      · exact ConstArR.of_ctor har
    have h' : StoreArR ⟨ciA :: env.consts⟩ :=
      Ix.Kernel.Model.storeArR_cons h hfreshA hc (fun ⟨cv, v, hh, he⟩ => by
        rcases hkind with rfl | ⟨nP, nF, rfl⟩ <;> exact nomatch he)
    exact storeArR_pointRun rest hrest h'

/-- **The install stores no theorem.** -/
theorem _root_.IxVM.Refinement.Decl.Point.PointBlock.newSat_notThm (hb : PointBlock env block formers ctors) :
    Ix.Kernel.Model.NewSat env (installed env formers ctors) Ix.Kernel.Model.NotThm := by
  intro n x hf
  rcases hb.find_cases hf with h | ⟨f, -, rfl⟩ | ⟨c, -, rfl⟩
  · exact Or.inl h
  · exact Or.inr (fun _ _ hh => nomatch hh)
  · exact Or.inr (fun _ _ hh => nomatch hh)

/-- **The install keeps the level clauses.** -/
theorem _root_.IxVM.Refinement.Decl.Point.PointBlock.lvClauses (hb : PointBlock env block formers ctors) (h : LvClauses env) :
    LvClauses (installed env formers ctors) :=
  ⟨Ix.Kernel.Model.ThmLevels.step_noThm h.1 hb.newSat_notThm,
    storeArR_pointRun _ hb.run h.2⟩

/-! ## The prefix invariant -/

/-- A new name is no unresolved key: it is an input key. -/
theorem _root_.IxVM.Refinement.Decl.Point.PointBlock.new_resolved (hb : PointBlock env block formers ctors) :
    ∀ cn ∈ newConsts formers ctors, cn.name ≠ Core.unresolvedKey := by
  intro cn hcn
  obtain ⟨a, ha⟩ := hb.new_id hcn
  rw [ha]
  unfold Core.unresolvedKey
  exact fun e => nomatch e

/-- **The prefix invariant at the installed environment**, from the prefix's, at any store and
limit, given the load facts that reach the new constants. -/
theorem _root_.IxVM.Refinement.Decl.Point.PointBlock.prefixInv {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    (hb : PointBlock env block formers ctors) (hinv : Decl.PrefixInv.{u} E t lim env)
    (hnew : NewLoads (appCtx ⟨E, env, t, lim⟩ (newConsts formers ctors)).stored
      (newConsts formers ctors)) :
    Decl.PrefixInv.{u} E t lim (installed env formers ctors) := by
  have hstore : Decl.FoldStoreInv (installed env formers ctors) :=
    foldStoreInv_run _ hb.run hinv.store
  have hext : Ix.Kernel.EnvExt env (appCtx ⟨E, env, t, lim⟩ (newConsts formers ctors)).env := by
    have h := hb.envExt
    rw [installed_eq] at h
    exact h
  have hloads := storedLoads_append (c := ⟨E, env, t, lim⟩) hinv.loads hext hb.new_resolved
    hinv.etaStable hnew
  have hinst : installed env formers ctors =
      (appCtx ⟨E, env, t, lim⟩ (newConsts formers ctors)).env := installed_eq env formers ctors
  exact
    { decl := fun V _ => (pointBlock_install.{u} hb 0).2.2.1 V (hinv.decl V)
      store := hstore
      unresolved := by
        cases hf : (installed env formers ctors).find? Core.unresolvedKey with
        | none => rfl
        | some x =>
          exfalso
          rcases hb.find_cases hf with h | ⟨f, hf', rfl⟩ | ⟨c, hc, rfl⟩
          · rw [hinv.unresolved] at h
            cases h
          · have hn := Ix.Kernel.Semantics.Env.find?_name hf
            exact hb.new_resolved _ (hb.mem_new_former hf') hn
          · have hn := Ix.Kernel.Semantics.Env.find?_name hf
            exact hb.new_resolved _ (hb.mem_new_ctor hc) hn
      tableWf := hinv.tableWf
      companions := hb.coreCompanions hinv.store.store E t lim hinv.companions
      loads := by
        rw [hinst]
        exact hloads
      etaStable := hstore.etaStable }

end

end IxVM.Refinement.Typing
