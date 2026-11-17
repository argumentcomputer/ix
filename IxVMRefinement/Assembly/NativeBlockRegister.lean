import IxVMRefinement.Assembly.LateRegistry
import IxVMRefinement.Assembly.NativeBlockInv
import IxVMRefinement.Assembly.NativeBlockStage

/-! # Registering a native family at its install, and the store clause beside the registry

* `NativeNoRecFacts.newInd`: the only inductive type the no-recursor install stores new is the
  family's stored former;
* `LateRegistryWith.nativeNoRec`, `LateRegistry.nativeNoRec`: the install registers its family
  (`LateRegistryWith.register` met: the model step is `NativeNoRecFacts.register`, the new-key
  fact is `newInd` with the family's stored former, the family is read off the store, `hat`);
* `NativeNoRecFacts.ctorFields`, `.levelParams_of_former`: two fields of `hat` from the install
  (the constructors' field counts; the family's level parameters are the declared former's);
* `KeepsValuesKeyed`: the rule for the extra clause along a value step that also hands the fact
  that the stored key is the key of a 32-byte address; `KeepsValuesJ` gives it
  (`KeepsValuesJ.keyed`), and so does the store clause `HashKeyed`
  (`keepsValuesKeyed_hashKeyed`), which `KeepsValuesJ` alone cannot carry: a value step hands
  no fact about the address behind its key. `address_size_of_record` produces the premise for a
  step at a record address of a run store.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps Key)
open Ix.Kernel.Semantics (NativeFam DeclRunJ IndRoutesJ)
open Ix.Kernel.Model (rulesJ)

/-! ## The new family -/

/-- **The only inductive type the no-recursor install stores new is the family's stored
former.** -/
theorem NativeNoRecFacts.newInd {env env₂ : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} {nP : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    {fam : NativeFam .anon} (h : NativeNoRecFacts env env₂ blk nP p₀ fam) :
    ∃ new : List (ConstantInfo .anon), env₂ = ⟨new ++ env.consts⟩ ∧
      ∀ ci ∈ new, ∀ cv caps, ci = .indInfo cv caps → cv = fam.cvS := by
  obtain ⟨-, -, isRec, cvS, cvTa, caps, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts, hfam,
    -, -, -, -, -, -, -, -, -, hTbl⟩ := h
  subst hfam
  have hc : (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩).consts =
      ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [.indInfo cvS caps]) ++ env.consts := by
    rw [Decl.consts_consSumCtors_eq]
    simp
  have hmem : ∀ ci ∈ (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [.indInfo cvS caps], ∀ cv caps', ci = .indInfo cv caps' → cv = cvS := by
    intro ci hci cv caps' he
    rcases List.mem_append.mp hci with hct | hind
    · obtain ⟨c, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hct)
      cases he
    · rw [List.mem_singleton.mp hind] at he
      injection he with h1 _
      exact h1.symm
  rcases checkNativeTable_shape hTbl with heq | ⟨tbl, heq, -⟩
  · refine ⟨_, ?_, hmem⟩
    rw [heq]
    exact congrArg Ix.Kernel.Env.mk hc
  · refine ⟨.projInfo tbl :: ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [.indInfo cvS caps]), ?_, ?_⟩
    · rw [heq, hc]
      rfl
    · intro ci hci cv caps' he
      rcases List.mem_cons.mp hci with rfl | hold
      · cases he
      · exact hmem ci hold cv caps' he

/-! ## Registration -/

/-- **A native block's install registers its family**, where the install extends the prefix
and the family is read off the store at the new environment (`LateFamAt`). -/
theorem LateRegistryWith.nativeNoRec {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon} {Reg : NativeFam .anon → Prop}
    {blk : List (ConstantInfo .anon)} {nP : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    {fam : NativeFam .anon} (h : LateRegistryWith.{u} t E env Reg)
    (hfacts : NativeNoRecFacts env env₂ blk nP p₀ fam) (hext : Ix.Kernel.EnvExt env env₂)
    (hat : LateFamAt t E env₂ fam) :
    LateRegistryWith.{u} t E env₂ (fun f => Reg f ∨ f = fam) := by
  refine h.register (fun V _ hm => hfacts.register V hm) hext hat ?_
  intro P cm ip cv caps hf hold _ _ _ _
  obtain ⟨new, henv, hind⟩ := hfacts.newInd
  have hf' := hf
  rw [henv] at hf'
  rcases find?_append_cases new hf' with hm | ho
  · have hcv := hind _ hm cv caps rfl
    have hname : cv.name = keyOf t P := Core.WhnfAux.name_of_find hf
    have hname₂ : fam.cvS.name = fam.p.cvT.name := Core.WhnfAux.name_of_find hat.stored.former
    rw [hcv] at hname
    exact hname.symm.trans hname₂
  · rw [hold] at ho
    cases ho

/-- **A native block's install keeps the registry clause**, registering its family. -/
theorem LateRegistry.nativeNoRec {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)} {nP : Nat}
    {p₀ : Ix.Kernel.NativeParts .anon} {fam : NativeFam .anon} (h : LateRegistry.{u} t E env)
    (hfacts : NativeNoRecFacts env env₂ blk nP p₀ fam) (hext : Ix.Kernel.EnvExt env env₂)
    (hat : LateFamAt t E env₂ fam) : LateRegistry.{u} t E env₂ := by
  obtain ⟨Reg, hR⟩ := h
  exact ⟨_, hR.nativeNoRec hfacts hext hat⟩

/-- **The install extends the prefix** (IxC: the former and the constructors are fresh, the
table is the new structure's). -/
theorem NativeNoRecFacts.envExt {env env₂ : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} {nP : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    {fam : NativeFam .anon} (h : NativeNoRecFacts env env₂ blk nP p₀ fam) :
    Ix.Kernel.EnvExt env env₂ :=
  Ix.Kernel.Semantics.declNativeNoRecRunJ_envExt h.runJ

/-- **A native block's install keeps the registry clause**, given that its family is read off
the store at the new environment. -/
theorem LateRegistry.nativeNoRec' {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)} {nP : Nat}
    {p₀ : Ix.Kernel.NativeParts .anon} {fam : NativeFam .anon} (h : LateRegistry.{u} t E env)
    (hfacts : NativeNoRecFacts env env₂ blk nP p₀ fam) (hat : LateFamAt t E env₂ fam) :
    LateRegistry.{u} t E env₂ :=
  h.nativeNoRec hfacts hfacts.envExt hat

/-! ## Fields of `LateFamAt` the install gives -/

/-- The family's record has the recognised block's former. -/
theorem NativeNoRecFacts.cvT_eq {env env₂ : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} {nP : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    {fam : NativeFam .anon} (h : NativeNoRecFacts env env₂ blk nP p₀ fam) :
    fam.p.cvT = p₀.cvT := by
  obtain ⟨-, -, isRec, cvS, cvTa, caps, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts, hfam,
    hInd, hp, -⟩ := h
  subst hfam
  obtain ⟨cvTa₀, s, bs, cvS', -, -, -, -, hp₁, -⟩ := hInd
  subst hp hp₁
  simp [Ix.Kernel.NativeParts.withKinds]

/-- **`LateFamAt.ctorFields` from the install**: each stored constructor has its declared
constructor's field count (the constructors' stage, `SumCtorsRunJ`). -/
theorem NativeNoRecFacts.ctorFields {env env₂ : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} {nP : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    {fam : NativeFam .anon} (h : NativeNoRecFacts env env₂ blk nP p₀ fam) :
    ∀ (j : Nat) (c cA : ConstantVal .anon × Nat), fam.p.ctors[j]? = some c →
      fam.ctorsA[j]? = some cA → cA.2 = c.2 := by
  obtain ⟨-, -, isRec, cvS, cvTa, caps, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts, hfam,
    -, -, hCtors, -⟩ := h
  subst hfam
  obtain ⟨-, -, hall⟩ := hCtors
  intro j c cA hc hcA
  exact (hall j c cA hc hcA).1

/-- **The family's level parameters are the declared former's** (for `LateFamAt.record`'s level
parameters, at a former read with `List.range` of the member's level count). -/
theorem NativeNoRecFacts.levelParams_of_former {env env₂ : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} {nP : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    {fam : NativeFam .anon} (h : NativeNoRecFacts env env₂ blk nP p₀ fam)
    {cv : ConstantVal .anon} {caps : IndCaps .anon} {cs : List (ConstantInfo .anon)}
    (hblk : blk = .indInfo cv caps :: cs) : fam.p.cvT.levelParams = cv.levelParams := by
  obtain ⟨caps₀, hshape, -⟩ := Decl.nativePartsNoRec?_inv h.recognised
  rw [hblk] at hshape
  injection hshape with h1 _
  injection h1 with hcv _
  rw [h.cvT_eq, hcv]

/-! ## The invariant after the install, from its load contract and η stability -/

/-- **The prefix invariant after a native block's install**, given its two clauses that read the
new family (the load contract at the new environment and η stability) and that every key stored
new resolves. Every other clause is the declaration layer's step, the table, or kept by
constants that are no recursor. -/
theorem PrefixInv.nativeNoRec {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env env₂ : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)} {nP : Nat}
    {p₀ : Ix.Kernel.NativeParts .anon} {fam : NativeFam .anon}
    (h : Decl.PrefixInv.{u} E t lim env) (hfacts : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (hpin : Ix.Kernel.basisPinHit blk = none) (hna : Decl.DeclNonAux (.indDecl blk nP))
    (hres : ∀ (k : Core.KKey) (ci : ConstantInfo .anon), env₂.find? k = some ci →
      env.find? k = none → k ≠ Core.unresolvedKey)
    (hloads : Core.ScopedLoadFacts (Core.Ctx.stored ⟨E, env₂, t, lim⟩))
    (heta : Decl.EtaStable env₂) :
    Decl.PrefixInv.{u} E t lim env₂ := by
  have hext : Ix.Kernel.EnvExt env env₂ := hfacts.envExt
  have hunres : env₂.find? Core.unresolvedKey = none := by
    cases hf : env₂.find? Core.unresolvedKey with
    | none => rfl
    | some ci => exact absurd rfl (hres _ ci hf h.unresolved)
  have hnaKeys : ∀ ci ∈ blk, Decl.NonAuxKey ci.name := fun ci hci =>
    (hna.1 ci (by simpa [IxVM.Consistency.installs, hpin] using hci)).1
  have hdecl := hfacts.fullDeclInv hpin hna
  have hstore := hfacts.foldStoreInv hpin hnaKeys h.store
  obtain ⟨new, rfl, hkind⟩ := hfacts.shape
  have hnorec : ∀ ci ∈ new, ∀ cv mI rP rls, ci ≠ .recInfo cv mI rP rls := by
    intro ci hci cv mI rP rls he
    rcases hkind ci hci with ⟨cv', caps, h'⟩ | ⟨cv', nP', nF, h'⟩ | ⟨tbl, h'⟩ <;>
      (rw [h'] at he; cases he)
  exact
    { decl := fun V _ => hdecl V (h.decl V)
      store := hstore
      unresolved := hunres
      tableWf := h.tableWf
      companions := CoreCompanions.append_noRec (c := ⟨E, env, t, lim⟩) h.companions
        h.store.store hext hnorec
      loads := hloads
      etaStable := heta }

/-! ## The store clause beside the registry -/

/-- **The extra clause is kept by storing a value constant at the key of a 32-byte address**,
along its declaration step: `KeepsValuesJ` with the premise that the stored key is the key of an
address of 32 bytes. -/
def KeepsValuesKeyed (t : Ix.Kernel.RoleTable) (X : Ix.Kernel.Env .anon → Prop) : Prop :=
  ∀ (env : Ix.Kernel.Env .anon) (ci : ConstantInfo .anon) (d : Ix.Kernel.Declaration .anon),
    X env → env.find? ci.name = none → IsValueConst ci →
    (∀ T : Key .anon, ci.name ≠ Ix.Kernel.projTableName T) →
    DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d ⟨ci :: env.consts⟩ →
    (∃ x : _root_.Address, ci.name = keyOf t x ∧ x.hash.size = 32) → X ⟨ci :: env.consts⟩

theorem KeepsValuesJ.keyed {X : Ix.Kernel.Env .anon → Prop} (h : KeepsValuesJ X)
    (t : Ix.Kernel.RoleTable) : KeepsValuesKeyed t X :=
  fun env ci d hX hf hv hnt hd _ => h env ci d hX hf hv hnt hd

theorem KeepsValuesKeyed.and {t : Ix.Kernel.RoleTable} {X Y : Ix.Kernel.Env .anon → Prop}
    (hX : KeepsValuesKeyed t X) (hY : KeepsValuesKeyed t Y) :
    KeepsValuesKeyed t (fun env => X env ∧ Y env) :=
  fun env ci d h hf hv hnt hd hk =>
    ⟨hX env ci d h.1 hf hv hnt hd hk, hY env ci d h.2 hf hv hnt hd hk⟩

/-- **The store clause is kept by a value constant at the key of a 32-byte address.** -/
theorem keepsValuesKeyed_hashKeyed {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) :
    KeepsValuesKeyed t (HashKeyed t) := by
  intro env ci d hX _ _ _ _ hkey
  exact HashKeyed.append (new := [ci]) htwf hX
    (fun c hc => by rw [List.mem_singleton.mp hc]; exact Or.inl hkey)

/-- **The registry and the store clause together** are kept by such a value step. -/
theorem keepsValuesKeyed_late {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) (E : Ixon.Env) :
    KeepsValuesKeyed t (fun env => LateRegistry.{u} t E env ∧ HashKeyed t env) :=
  ((keepsValuesJ_lateRegistry t E).keyed t).and (keepsValuesKeyed_hashKeyed htwf)

/-- **The premise's producer at a value step**: an address the run's store holds a record at
has 32 bytes (it is the hash of the record's bytes). -/
theorem address_size_of_record {calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
    {E₀ : Ixon.Env} {A : _root_.Address} {c : Ixon.Constant}
    (hS : LoadedReads.RunStore calls E₀) (hc : recordOf E₀ A = some c) : A.hash.size = 32 := by
  obtain ⟨lc, hget, -⟩ := LoadedReads.recordOf_inv hc
  obtain ⟨-, ha⟩ := hS.loaded.1 A lc hget
  rw [← ha]
  exact (Blake3.Pure.hash _).property

end IxVM.Refinement.Typing
