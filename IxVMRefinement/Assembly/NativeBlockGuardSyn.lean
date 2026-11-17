import IxVMRefinement.Assembly.NativeBlockGuardOff
import IxC.Kernel.Model.SortSyn
import IxC.Kernel.Verify.Inductives.StructPartsInv

/-! # The new table's guard clause where the field domains are in the class `C`

`BlockGuard` (`NativeBlockTableOf.lean`) relates two computations of a field's guard level at a
`Prop` structure: the table's, `structProjGuards` of the field sorts IxC's constructor stage read
(`FieldSortsJ`), and the circuit's `proj_guard`, which recomputes each field's sort by
`k_ensure_sort` at every use. Both are sorts of the same opened field domain. IxC's inference has
no conversion rule and a sort or a `∀` reduces only to itself, so where the domain is in the
syntactic class `SortSyn` (`IxC/Kernel/Model/SortSyn.lean`) the two sorts are the class's level
(`SortSyn.sort_eq`), whatever the two environments, as long as both keep the prefix's lookups.

* `CtorFieldsSortSyn env cty nP nF`: the constructor type's field domains, opened as IxC's
  constructor stage opens them, are in the class at the prefix `env`;
* `ProjGuardFields`, `ProjGuardWalkAt`: what the circuit's `proj_guard` computes, in IxC's terms:
  the guard level is the fold of `structProjGuards`' shape over represented levels, each the
  sort of a derivation of the opened domain at an environment `envS`, and the circuit joins
  every earlier field a later binder uses (a functional spec of `proj_guard`, produced in
  `NativeBlockGuardWalk.lean`);
* `NativeInstallOut.guard_sorts`: at a one-constructor, index-free install, the new table, its
  guards and the field sorts' derivations;
* `eval_guardFold_eq_zero`: a guard fold is zero at an assignment exactly where its start and
  every joined level are;
* `blockGuard_of_install_syn`: **`BlockGuard` from the circuit's spec and the class**.
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)
open Ix.Kernel.Semantics (FieldSortsJ)
open Ix.Kernel.Rules (SortSyn Infer Red)

set_option linter.unusedVariables false

/-! ## The class at a constructor, and the circuit's guard in IxC's terms -/

/-- **The constructor type's field domains are in the class `C`** at `env`: opening its `nP`
parameters at depths `0, …` and then its `nF` fields (IxC's constructor stage,
`SumCtorRunJ`), each field domain is `SortSyn` at its depth. -/
def CtorFieldsSortSyn (env : Ix.Kernel.Env .anon) (cty : Ix.Kernel.Expr .anon) (nP nF : Nat) :
    Prop :=
  ∀ (fvsP : List (Ix.Kernel.Expr .anon)) (crest : Ix.Kernel.Expr .anon)
    (xFvs : List (Ix.Kernel.Expr .anon)) (body : Ix.Kernel.Expr .anon),
    Ix.Kernel.openPisAtFvars nP cty 0 = some (fvsP, crest) →
    Ix.Kernel.openPisAtFvars nF crest nP = some (xFvs, body) →
    ∀ (j : Nat) (x : Ix.Kernel.Expr .anon), j < nF → xFvs[j]? = some x →
      ∃ v, SortSyn env (nP + j) x.fvarTypeD v

/-- **What the circuit's guard of field `f'` is, in IxC's terms**: the fold, in
`structProjGuards`' shape, of represented levels `lus` under flags `flags`, where each level
`j ≤ f'` is semantically the sort of a full-grade derivation of the opened field domain at
`envS`, and every earlier field that a later binder uses (`structUsedLater`) is flagged. -/
def ProjGuardFields (envS : Ix.Kernel.Env .anon) (cvC : ConstantVal .anon) (nP nF f' : Nat)
    (g : Core.KLevel) : Prop :=
  ∃ (lus : List Core.KLevel) (flags : List Bool),
    g = (List.range f').foldl
      (fun acc j => if flags.getD j false then Ix.Kernel.Level.max acc (lus.getD j .zero) else acc)
      (lus.getD f' .zero) ∧
    (∀ (fvsP : List (Ix.Kernel.Expr .anon)) (crest : Ix.Kernel.Expr .anon)
        (xFvs : List (Ix.Kernel.Expr .anon)) (body : Ix.Kernel.Expr .anon),
      Ix.Kernel.openPisAtFvars nP cvC.type 0 = some (fvsP, crest) →
      Ix.Kernel.openPisAtFvars nF crest nP = some (xFvs, body) →
      ∀ j, j ≤ f' → ∃ (x T : Ix.Kernel.Expr .anon) (u : Ix.Kernel.Level), xFvs[j]? = some x ∧
        Infer envS .full (nP + j) x.fvarTypeD T ∧ Red envS (nP + j) T (.sort u) ∧
        Core.LvEq u (lus.getD j .zero)) ∧
    (∀ j, j < f' → Ix.Kernel.structUsedLater cvC.type nP j = true → flags.getD j false = true)

/-- **The circuit's guard runs at the new structure's constructor `cA`**, in IxC's terms: every
`proj_guard` run of a field of member `0` of the block at `B`, good at the environment after
the install, computes a level of `ProjGuardFields` shape. -/
def ProjGuardWalkAt (E : Ixon.Env) (env : Ix.Kernel.Env .anon) (t : Ix.Kernel.RoleTable)
    (n : Nat) (new : List (ConstantInfo .anon)) (B : _root_.Address) (envS : Ix.Kernel.Env .anon)
    (cA : ConstantVal .anon × Nat) (nP : Nat) : Prop :=
  ∀ (i f : F) (rc bp' rg : SourceValue F) (hg hg' : Heap F) (csg : List (Call F))
    (g : Core.KLevel) (b : Bytes.Address),
    ZMod.val i = 0 → ZMod.val f < cA.2 →
    ObsFn Core.W "KernelInfer::proj_guard" [rc, bp', .field i, .field f] hg rg hg' csg →
    Core.Good (appCtx ⟨E, env, t, some n⟩ new) csg → Core.RCRep t (some n) hg rc →
    Bytes.RepAddressRef Core.addrTy hg b bp' → Core.ixAddr b = B →
    IxVM.Refinement.KernelLevels.RepKLevel hg' g rg →
    ProjGuardFields envS cA.1 nP cA.2 (ZMod.val f) g

/-! ## Folds of guard levels -/

/-- **A guard fold is zero at an assignment exactly where its start and every joined level
are.** -/
theorem eval_guardFold_eq_zero (ψ : Ix.Kernel.LevelParam → Nat) (P : Nat → Bool)
    (L : Nat → Ix.Kernel.Level) (init : Ix.Kernel.Level) :
    ∀ k : Nat, Ix.Kernel.Level.eval ψ ((List.range k).foldl
        (fun acc j => if P j then Ix.Kernel.Level.max acc (L j) else acc) init) = 0 ↔
      Ix.Kernel.Level.eval ψ init = 0 ∧
        ∀ j, j < k → P j = true → Ix.Kernel.Level.eval ψ (L j) = 0
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih := eval_guardFold_eq_zero ψ P L init k
    by_cases hk : P k = true
    · rw [if_pos hk]
      simp only [Ix.Kernel.Level.eval]
      rw [Nat.max_eq_zero_iff, ih]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, fun j hj hp => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h2 j hj hp
        · exact h3
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun j hj hp => h2 j (Nat.lt_succ_of_lt hj) hp⟩, h2 k (Nat.lt_succ_self k) hk⟩
    · rw [if_neg hk, ih]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun j hj hp => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h2 j hj hp
        · exact absurd hp hk
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun j hj hp => h2 j (Nat.lt_succ_of_lt hj) hp⟩

/-! ## The install's table and field sorts -/

/-- **The new table at a one-constructor, index-free install, with the field sorts IxC's
constructor stage read**: the constructor list is one constructor `cA`; the environment after
the install stores a table at the family's table name, whose guards are `structProjGuards` of
`cA`'s type at sorts `sorts` and whose level parameters are the family's; and `sorts` are the
fields' sorts (`FieldSortsJ`) of `cA`'s opened field domains at the constructor stage's
environment (the former stored over the prefix). -/
theorem NativeInstallOut.guard_sorts {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)} {p₀ p : Ix.Kernel.NativeParts .anon}
    {new : List (ConstantInfo .anon)} {ty' : Ix.Kernel.Expr .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps)
    (hsize : ind.ctors.size = 1) (hidx : ind.indices.toNat = 0) :
    ∃ (cA : ConstantVal .anon × Nat) (sorts : List Ix.Kernel.Level)
      (tbl : Ix.Kernel.ProjTable .anon) (caps' : IndCaps .anon)
      (fvsP : List (Ix.Kernel.Expr .anon)) (crest : Ix.Kernel.Expr .anon)
      (xFvs idxArgs : List (Ix.Kernel.Expr .anon)) (body : Ix.Kernel.Expr .anon),
      ctorsA = [cA] ∧
      (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
        (Ix.Kernel.projTableName (Core.keyOf t (Core.iprjAddr B 0))) = some (.projInfo tbl) ∧
      tbl.guards = Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts ∧
      tbl.levelParams = List.range ind.lvls.toNat ∧
      Ix.Kernel.openPisAtFvars p.nP cA.1.type 0 = some (fvsP, crest) ∧
      Ix.Kernel.openPisAtFvars cA.2 crest p.nP = some (xFvs, body) ∧
      FieldSortsJ Ix.Kernel.Model.rulesJ
        ⟨.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ caps' ::
          env.consts⟩ p.isProp p.large p.resSort p.nP xFvs idxArgs cA.2 sorts := by
  have hpT : p.cvT.name = Core.keyOf t (Core.iprjAddr B 0) := by rw [hO.cvT]; exact hO.cvT₀.1
  have hpL : p.cvT.levelParams = List.range ind.lvls.toNat := by rw [hO.cvT]; exact hO.cvT₀.2
  have hpI : p.nIdx = 0 := hO.nIdx.trans hidx
  have hlen : ctorsA.length = 1 := hO.lenA.trans hsize
  obtain ⟨cA, rfl⟩ : ∃ cA, ctorsA = [cA] := by
    match ctorsA, hlen with
    | [cA], _ => exact ⟨cA, rfl⟩
  obtain ⟨-, -, isRec, cvS', cvTa, caps', p₁, q, ctorsB, sortss, kinds, tfvs, trest, isorts, hfam,
    -, -, hCtors, -, -, -, -, -, -, hTbl⟩ := hO.facts
  injection hfam with h1 h2 h3 h4
  subst h1 h2 h3 h4
  obtain ⟨hlA, hlS, hall⟩ := hCtors
  obtain ⟨c, hc⟩ : ∃ c, p.ctors[0]? = some c := by
    have h0 : 0 < p.ctors.length := by
      rw [← hlA]
      exact Nat.zero_lt_one
    exact ⟨p.ctors[0], List.getElem?_eq_getElem h0⟩
  obtain ⟨hc2, sorts, hsorts, hrun⟩ := hall 0 c cA hc rfl
  obtain ⟨sorts₀, rfl⟩ : ∃ s, sortss = [s] := by
    have hl : sortss.length = 1 := hlS.trans (hlA.symm.trans rfl)
    match sortss, hl with
    | [s], _ => exact ⟨s, rfl⟩
  have hss : sorts₀ = sorts := by simpa using hsorts
  subst hss
  obtain ⟨-, -, fvsP, crest, tfvs', trest', xFvs, idxArgs, hop1, -, -, hop2, -, -, -, hFS⟩ := hrun
  obtain ⟨tbl, -, -, hfind, -, -, -, -, hlps, -, -, -, hguards, -⟩ :=
    IxVM.Refinement.Decl.checkNativeTable_struct_inv hpI hTbl
  have hfind' : (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
      (Ix.Kernel.projTableName (Core.keyOf t (Core.iprjAddr B 0))) = some (.projInfo tbl) := by
    rw [← hpT]
    exact hfind
  rw [← hc2] at hop2 hFS
  exact ⟨cA, _, tbl, caps', fvsP, crest, xFvs, idxArgs, _, rfl, hfind', hguards,
    hlps.trans hpL, hop1, hop2, hFS⟩

/-! ## The producer -/

/-- **`BlockGuard` where the structure's field domains are in the class**: at a
one-constructor, index-free install, from the circuit's guard spec at an environment `envS` that
keeps the prefix's lookups (`hwalk`) and the class at the prefix (`hsyn`). The table's guard and
the circuit's are folds of one shape; the circuit joins every level the table joins; each joined
level is the sort of the same opened domain at two environments that keep the prefix's lookups,
which the class fixes (`SortSyn.sort_eq`). -/
theorem blockGuard_of_install_syn {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)} {p₀ p : Ix.Kernel.NativeParts .anon}
    {new : List (ConstantInfo .anon)} {ty' : Ix.Kernel.Expr .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps)
    (hsize : ind.ctors.size = 1) (hidx : ind.indices.toNat = 0)
    (hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    {envS : Ix.Kernel.Env .anon}
    (hS : ∀ (k : Core.KKey) (ci : ConstantInfo .anon), env.find? k = some ci →
      envS.find? k = some ci)
    (hwalk : ∀ cA ∈ ctorsA, ProjGuardWalkAt E env t n new B envS cA p.nP)
    (hsyn : ∀ cA ∈ ctorsA, CtorFieldsSortSyn env cA.1.type p.nP cA.2) :
    BlockGuard ⟨E, env, t, some n⟩ new B := by
  obtain ⟨cA, sorts, tbl₀, caps', fvsP, crest, xFvs, idxArgs, body, hcA, hfind₀, hguards, hlps,
    hop1, hop2, hFS⟩ := hO.guard_sorts hsize hidx
  subst hcA
  have hwalk' := hwalk cA (List.mem_singleton_self _)
  have hsyn' := hsyn cA (List.mem_singleton_self _) fvsP crest xFvs body hop1 hop2
  -- the constructor stage's environment keeps the prefix's lookups
  have hF : ∀ (k : Core.KKey) (ci : ConstantInfo .anon), env.find? k = some ci →
      (⟨.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ caps' ::
        env.consts⟩ : Ix.Kernel.Env .anon).find? k = some ci := by
    intro k ci hf
    rw [Ix.Kernel.Env.find?_cons]
    have hne : ¬ (ConstantInfo.indInfo
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ caps').name = k := by
      intro h
      have hk : k = Core.keyOf t (Core.iprjAddr B 0) := h.symm
      rw [hk, hfreshT] at hf
      cases hf
    rw [if_neg hne]
    exact hf
  unfold BlockGuard
  intro i hi j cvC nP nF tbl hC hTb hz f rc bp' rg hg hg' csg g us b hf hus ev good hrc hb hbB
    hgr hzero φ
  have hκ : (appCtx ⟨E, env, t, some n⟩ new).stored.κ (Core.iprjAddr B 0) =
      Core.keyOf t (Core.iprjAddr B 0) :=
    appCtx_key_of_find (c := ⟨E, env, t, some n⟩) (new := new) hO.formerFind
  rw [hκ] at hTb
  have htbl : tbl = tbl₀ := by
    have h := hTb.symm.trans hfind₀
    injection h with h
    injection h with h
    exact h
  rw [htbl] at hus ⊢
  show Ix.Kernel.Level.eval φ
    (Ix.Kernel.Level.subst tbl₀.levelParams us (tbl₀.guards.getD (ZMod.val f) .zero)) = 0
  rw [hguards]
  by_cases hfl : ZMod.val f < cA.2
  · rw [Ix.Kernel.structProjGuards_getD _ _ _ _ hfl]
    obtain ⟨lus, flags, hgeq, hder, hflag⟩ :=
      hwalk' i f rc bp' rg hg hg' csg g b hi hfl ev good hrc hb hbB hgr
    have hder' := hder fvsP crest xFvs body hop1 hop2
    -- each joined level of the table is semantically the circuit's
    have hkey : ∀ j, j ≤ ZMod.val f → ∀ ψ : Ix.Kernel.LevelParam → Nat,
        Ix.Kernel.Level.eval ψ (sorts.getD j .zero) =
          Ix.Kernel.Level.eval ψ (lus.getD j .zero) := by
      intro j hj ψ
      have hjF : j < cA.2 := Nat.lt_of_le_of_lt hj hfl
      obtain ⟨x, T, u, hx, hI, hR, hu⟩ := hder' j hj
      obtain ⟨fv, ty, u', hfv, hsj, hI', hR', -, -⟩ := hFS.2 j hjF
      have hxe : fv = x := Option.some.inj (hfv.symm.trans hx)
      subst hxe
      obtain ⟨v, hv⟩ := hsyn' j fv hjF hfv
      have e1 : u = v := (hv.mono hS).sort_eq hI hR
      have e2 : u' = v := (hv.mono hF).sort_eq hI' hR'
      have hsg : sorts.getD j .zero = u' := by
        rw [List.getD_eq_getElem?_getD, hsj]
        rfl
      rw [hsg, e2, ← e1]
      exact hu ψ
    have hlpsR : List.range us.length = tbl₀.levelParams := by
      rw [hlps]
      rw [hlps] at hus
      rw [hus, List.length_range]
    have hg0 := hzero φ
    rw [hlpsR, Ix.Kernel.Level.eval_subst, hgeq] at hg0
    obtain ⟨hinit, hdeps⟩ :=
      (eval_guardFold_eq_zero (Ix.Kernel.Level.substFn φ tbl₀.levelParams us)
        (fun j => flags.getD j false) (fun j => lus.getD j .zero) (lus.getD (ZMod.val f) .zero)
        (ZMod.val f)).mp hg0
    rw [Ix.Kernel.Level.eval_subst]
    refine (eval_guardFold_eq_zero (Ix.Kernel.Level.substFn φ tbl₀.levelParams us)
      (fun j => Ix.Kernel.structUsedLater cA.1.type p.nP j) (fun j => sorts.getD j .zero)
      (sorts.getD (ZMod.val f) .zero) (ZMod.val f)).mpr ⟨?_, ?_⟩
    · rw [hkey (ZMod.val f) (Nat.le_refl _)]
      exact hinit
    · intro j hj hused
      rw [hkey j (Nat.le_of_lt hj)]
      exact hdeps j hj (hflag j hj hused)
  · have hlenG : (Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts).length ≤ ZMod.val f := by
      simp only [Ix.Kernel.structProjGuards, List.length_map, List.length_range]
      omega
    have hz0 : (Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts).getD (ZMod.val f) .zero =
        .zero := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hlenG]
      rfl
    rw [hz0]
    rfl

end IxVM.Refinement.Typing
