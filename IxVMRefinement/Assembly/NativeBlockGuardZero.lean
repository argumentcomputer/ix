import IxVMRefinement.Assembly.NativeBlockGuardSyn
import IxC.Kernel.Model.SortZero

/-! # The new table's guard clause where the field domains are in the zero-ness class

`blockGuard_of_install_syn` with the class `SortSyn` widened to `SortZ`
(`IxC/Kernel/Model/SortZero.lean`): only the zero-ness of each joined level matters to the guard,
and the sort of `∀ x : A, B` has the zero-ness of `B`'s, so a field domain's binder domains are
unconstrained (a field `∀ {a b : M}, …` over a variable `M : outParam (Type u)` is in the class).

* `CtorFieldsSortZ`, `CtorFieldsSortSyn.sortZ`: the class at a constructor; it contains the
  narrower one;
* `blockGuard_of_install_z`: **`BlockGuard` from the circuit's spec and the zero-ness class**.
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)
open Ix.Kernel.Semantics (FieldSortsJ)
open Ix.Kernel.Rules (SortSyn SortZ Infer Red)

set_option linter.unusedVariables false

/-- **The constructor type's field domains are in the zero-ness class** at `env` (opened as
IxC's constructor stage opens them). -/
def CtorFieldsSortZ (env : Ix.Kernel.Env .anon) (cty : Ix.Kernel.Expr .anon) (nP nF : Nat) :
    Prop :=
  ∀ (fvsP : List (Ix.Kernel.Expr .anon)) (crest : Ix.Kernel.Expr .anon)
    (xFvs : List (Ix.Kernel.Expr .anon)) (body : Ix.Kernel.Expr .anon),
    Ix.Kernel.openPisAtFvars nP cty 0 = some (fvsP, crest) →
    Ix.Kernel.openPisAtFvars nF crest nP = some (xFvs, body) →
    ∀ (j : Nat) (x : Ix.Kernel.Expr .anon), j < nF → xFvs[j]? = some x →
      ∃ v, SortZ env (nP + j) x.fvarTypeD v

/-- The zero-ness class at a constructor contains the narrower class. -/
theorem CtorFieldsSortSyn.sortZ {env : Ix.Kernel.Env .anon} {cty : Ix.Kernel.Expr .anon}
    {nP nF : Nat} (h : CtorFieldsSortSyn env cty nP nF) : CtorFieldsSortZ env cty nP nF := by
  intro fvsP crest xFvs body h1 h2 j x hj hx
  obtain ⟨v, hv⟩ := h fvsP crest xFvs body h1 h2 j x hj hx
  obtain ⟨w, hw, -⟩ := hv.sortZ
  exact ⟨w, hw⟩

/-- **`BlockGuard` where the structure's field domains are in the zero-ness class**: at a
one-constructor, index-free install, from the circuit's guard spec at an environment `envS` that
keeps the prefix's lookups (`hwalk`) and the class at the prefix (`hsyn`). The table's guard and
the circuit's are folds of one shape; the circuit joins every level the table joins; each joined
level is the sort of the same opened domain at two environments that keep the prefix's lookups,
which the class fixes in zero-ness (`SortZ.zero_iff`). -/
theorem blockGuard_of_install_z {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat}
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
    (hsyn : ∀ cA ∈ ctorsA, CtorFieldsSortZ env cA.1.type p.nP cA.2) :
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
    rw [ite_eq_right hne]
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
        Ix.Kernel.Level.eval ψ (sorts.getD j .zero) = 0 ↔
          Ix.Kernel.Level.eval ψ (lus.getD j .zero) = 0 := by
      intro j hj ψ
      have hjF : j < cA.2 := Nat.lt_of_le_of_lt hj hfl
      obtain ⟨x, T, u, hx, hI, hR, hu⟩ := hder' j hj
      obtain ⟨fv, ty, u', hfv, hsj, hI', hR', -, -⟩ := hFS.2 j hjF
      have hxe : fv = x := Option.some.inj (hfv.symm.trans hx)
      subst hxe
      obtain ⟨v, hv⟩ := hsyn' j fv hjF hfv
      have e1 := (hv.mono hS).zero_iff hI hR ψ
      have e2 := (hv.mono hF).zero_iff hI' hR' ψ
      have hsg : sorts.getD j .zero = u' := by
        rw [List.getD_eq_getElem?_getD, hsj]
        rfl
      rw [hsg, ← hu ψ]
      exact e2.trans e1.symm
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
    · exact (hkey (ZMod.val f) (Nat.le_refl _) _).mpr hinit
    · intro j hj hused
      exact (hkey j (Nat.le_of_lt hj) _).mpr (hdeps j hj (hflag j hj hused))
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
