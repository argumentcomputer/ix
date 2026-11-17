import IxVMRefinement.Decl.PrefixInv
import IxVMRefinement.Decl.NativeFront
import IxVMRefinement.Assembly.NativeBlockFacts

/-! # Pieces of the invariant at the environment after a native block's install

The install of a native block without its recursor adds, in front of the prefix, the former, the
constructors and (at a structure-like block) a projection table, and no recursor. These lemmas
give the clauses of `Decl.PrefixInv` that read only that shape:

* `find?_append_cases`: a lookup in the longer environment finds a new constant or the prefix's;
* `CoreCompanions.append_noRec`: the companions are kept by constants that are no recursor (the
  role fields are monotone; the recursor fields read the prefix's recursors, whose rules name
  constructors the prefix stores);
* `unresolved_append`: the unresolved key stays unstored.
-/

namespace IxVM.Refinement.Typing

open IxVM.Refinement.Core (Ctx KKey unresolvedKey)
open Ix.Kernel (ConstantInfo)

/-- **A lookup in an environment with constants in front finds one of them or the prefix's.** -/
theorem find?_append_cases {env : Ix.Kernel.Env .anon} {k : KKey} :
    ∀ (new : List (ConstantInfo .anon)) {x : ConstantInfo .anon},
      (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k = some x →
        x ∈ new ∨ env.find? k = some x
  | [], _, h => Or.inr h
  | c :: rest, x, h => by
    have h' : (⟨c :: (rest ++ env.consts)⟩ : Ix.Kernel.Env .anon).find? k = some x := h
    rw [Ix.Kernel.Env.find?_cons] at h'
    split at h'
    · have e : c = x := Option.some.inj h'
      subst e
      exact Or.inl List.mem_cons_self
    · rcases find?_append_cases rest h' with hm | ho
      · exact Or.inl (List.mem_cons_of_mem _ hm)
      · exact Or.inr ho

/-- **The companions are kept by constants that are no recursor**, at fresh keys that extend the
prefix (`EnvExt`): the role fields are monotone along the extension; a recursor the longer
environment stores is the prefix's, and so is the constructor its rule names (the prefix stores
it, `StoreInv.recRules_fire`). -/
theorem CoreCompanions.append_noRec {c : Ctx} (h : Decl.CoreCompanions c)
    (hstore : Ix.Kernel.Open.StoreInv c.env) {new : List (ConstantInfo .anon)}
    (hext : Ix.Kernel.EnvExt c.env ⟨new ++ c.env.consts⟩)
    (hnorec : ∀ ci ∈ new, ∀ cv mI rP rls, ci ≠ .recInfo cv mI rP rls) :
    Decl.CoreCompanions ⟨c.E, ⟨new ++ c.env.consts⟩, c.t, c.lim⟩ := by
  have oldRec : ∀ {k : KKey} {cv : Ix.Kernel.ConstantVal .anon} {mI rP : Nat}
      {rls : List (Ix.Kernel.RecRule .anon)},
      (⟨new ++ c.env.consts⟩ : Ix.Kernel.Env .anon).find? k = some (.recInfo cv mI rP rls) →
        c.env.find? k = some (.recInfo cv mI rP rls) := by
    intro k cv mI rP rls hf
    rcases find?_append_cases new hf with hm | ho
    · exact absurd rfl (hnorec _ hm cv mI rP rls)
    · exact ho
  have oldRuleCtor : ∀ {k : KKey} {cv : Ix.Kernel.ConstantVal .anon} {mI rP : Nat}
      {rls : List (Ix.Kernel.RecRule .anon)} {rl : Ix.Kernel.RecRule .anon}
      {cvj : Ix.Kernel.ConstantVal .anon} {nP nF : Nat},
      c.env.find? k = some (.recInfo cv mI rP rls) → rl ∈ rls →
      (⟨new ++ c.env.consts⟩ : Ix.Kernel.Env .anon).find? rl.ctor =
        some (.ctorInfo cvj nP nF) →
      c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) := by
    intro k cv mI rP rls rl cvj nP nF hk hrl hc
    obtain ⟨-, cvj', nF', hc'⟩ := hstore.recRules_fire hk hrl
    exact hc'.trans ((hext.find hc').symm.trans hc)
  exact
    { natLit := fun h1 h2 h3 => hext.natLitSupported_mono (h.natLit h1 h2 h3)
      strLit := fun h1 => hext.strLitSupported_mono (h.strLit h1)
      natOps := fun r hr hm => hext.natOpStored_mono (h.natOps r hr hm)
      natAdd := fun h1 => hext.opt_mono (p := Ix.Kernel.Rules.natAddTyOk) (h.natAdd h1) rfl
      eqStored := fun h1 =>
        let ⟨ci', hci'⟩ := h.eqStored h1
        ⟨ci', hext.find hci'⟩
      quotBasis := fun h1 ci' hm => hext.find (h.quotBasis h1 ci' hm)
      recMajorRecord := fun k cv mI rP rls p us hf hne hdom =>
        h.recMajorRecord k cv mI rP rls p us (oldRec hf) hne hdom
      recRulesNodupAndProj := fun k cv mI rP rls hf =>
        h.recRulesNodupAndProj k cv mI rP rls (oldRec hf)
      recPlain := fun k cv mI rP rls rl cvj nP nF hf hrl hfire hc =>
        h.recPlain k cv mI rP rls rl cvj nP nF (oldRec hf) hrl hfire
          (oldRuleCtor (oldRec hf) hrl hc)
      ruleCtorHead := fun k cv mI rP rls rl cvj nP nF T us hf hrl hc hdom =>
        h.ruleCtorHead k cv mI rP rls rl cvj nP nF T us (oldRec hf) hrl
          (oldRuleCtor (oldRec hf) hrl hc) hdom }

/-- **The unresolved key stays unstored** where no new constant has it. -/
theorem unresolved_append {env : Ix.Kernel.Env .anon} (h : env.find? unresolvedKey = none)
    {new : List (ConstantInfo .anon)} (hne : ∀ ci ∈ new, ci.name ≠ unresolvedKey) :
    (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? unresolvedKey = none := by
  rw [Ix.Kernel.EnvExt.find?_append_of_fresh hne]
  exact h

/-! ## The shape of the environment after the install -/

/-- **A native table step adds at most the projection table**, keyed by the family. -/
theorem checkNativeTable_shape {p : Ix.Kernel.NativeParts .anon}
    {ctorsA : List (Ix.Kernel.ConstantVal .anon × Nat)} {sortss : List (List Ix.Kernel.Level)}
    {X env₂ : Ix.Kernel.Env .anon}
    (h : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss X = .ok env₂) :
    env₂ = X ∨ ∃ tbl : Ix.Kernel.ProjTable .anon,
      env₂ = ⟨.projInfo tbl :: X.consts⟩ ∧ tbl.structName = p.cvT.name := by
  unfold Ix.Kernel.checkNativeTable at h
  split at h
  · split at h
    · obtain ⟨bodies, -, -, -, -, rfl⟩ := Ix.Kernel.checkStructProjTable_inv h
      exact Or.inr ⟨_, rfl, rfl⟩
    · injection h with hX
      exact Or.inl hX.symm
  · injection h with hX
    exact Or.inl hX.symm

/-- **The constants the no-recursor install adds**: the former, the constructors and, at a
structure-like block, the projection table of the family; no recursor. -/
theorem NativeNoRecFacts.shape {env env₂ : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} {nP : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    {fam : Ix.Kernel.Semantics.NativeFam .anon} (h : NativeNoRecFacts env env₂ blk nP p₀ fam) :
    ∃ new : List (ConstantInfo .anon), env₂ = ⟨new ++ env.consts⟩ ∧
      ∀ ci ∈ new, (∃ cv caps, ci = .indInfo cv caps) ∨ (∃ cv nP' nF, ci = .ctorInfo cv nP' nF) ∨
        ∃ tbl : Ix.Kernel.ProjTable .anon, ci = .projInfo tbl := by
  obtain ⟨-, -, isRec, cvS, cvTa, caps, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts, -,
    -, -, -, -, -, -, -, -, -, hTbl⟩ := h
  have hc : (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩).consts =
      ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [.indInfo cvS caps]) ++ env.consts := by
    rw [Decl.consts_consSumCtors_eq]
    simp
  have hmem : ∀ ci ∈ (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [.indInfo cvS caps],
      (∃ cv caps, ci = .indInfo cv caps) ∨ (∃ cv nP' nF, ci = .ctorInfo cv nP' nF) ∨
        ∃ tbl : Ix.Kernel.ProjTable .anon, ci = .projInfo tbl := by
    intro ci hci
    rcases List.mem_append.mp hci with hct | hind
    · obtain ⟨c, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hct)
      exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
    · rw [List.mem_singleton.mp hind]
      exact Or.inl ⟨_, _, rfl⟩
  rcases checkNativeTable_shape hTbl with heq | ⟨tbl, heq, -⟩
  · refine ⟨_, ?_, hmem⟩
    rw [heq]
    exact congrArg Ix.Kernel.Env.mk hc
  · refine ⟨.projInfo tbl :: ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [.indInfo cvS caps]), ?_, ?_⟩
    · rw [heq, hc]
      rfl
    · intro ci hci
      rcases List.mem_cons.mp hci with rfl | hold
      · exact Or.inr (Or.inr ⟨tbl, rfl⟩)
      · exact hmem ci hold

/-! ## The η type for open parameter spines (a hypothesis of the block step) -/

/-- **The η type for open parameter spines**: a constructor stored with the type
`∀ params fields, T params` (distinct level parameters) has, at every depth and every argument
spine, an inferred type that reduces to the family at the spine's parameters.
`Decl.etaType_of_closed` is this at closed parameters and under the whole environment's
`EtaShape`. The block step takes it for a structure-like block only (the fields `eta`, `etaIota`
of the load contract and `EtaStable` at the new environment, at the new family). -/
def EtaTypeOpen : Prop :=
  ∀ (env : Ix.Kernel.Env .anon) (T kc : KKey) (cvc : Ix.Kernel.ConstantVal .anon)
    (nP nF : Nat) (cbs : List (Core.KExpr × Ix.Kernel.BinderMeta)),
    env.find? kc = some (.ctorInfo cvc nP nF) → cvc.levelParams.Nodup →
    cvc.type.stripPis (nP + nF) =
      some (cbs, Ix.Kernel.Expr.mkAppN (.const T (cvc.levelParams.map .param))
        (Ix.Kernel.structPsAt nF nP)) →
    ∀ (d : Nat) (us : List Core.KLevel) (args : List Core.KExpr) (ty : Core.KExpr),
      args.length = nP + nF →
      Ix.Kernel.Rules.Infer env .io d (Ix.Kernel.Expr.mkAppN (.const kc us) args) ty →
      Ix.Kernel.Rules.Red env d ty (Ix.Kernel.Expr.mkAppN (.const T us) (args.take nP))

end IxVM.Refinement.Typing
