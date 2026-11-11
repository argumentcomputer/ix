import Ix.IxVM.Consistency.Statement
import IxC.Kernel.Model.Restrict
import IxC.Kernel.Semantics.EnvFacts

/-!
# The claimed sub-environment's model (for obligation L7)

`ConsistentRead`'s model conjunct is over `claimedEnv env`: the installed
environment without the model families' constants. The fold gives a model of the
installed environment; `claimedModel` restricts it (`Ix.Kernel.Model.restrict`).

The sub-environment agrees with the environment on every key whose entry is not
a model-family constant (`KeptKey`): `claimedEnv_find?`. Every input and role key
is such a key, and so is every projection table's (`keptKey_of_not_aux`, and a
table is not a model-family constant). With distinct names, the two agree on
projection tables too (`claimedEnv_findProj?`). What L7 discharges: distinct
names (from `InstallStep`), and that every claimed constant's type and every
claimed definition's value mention only kept keys (`RefsIn (KeptKey env)`; reader
output references input and role keys, a projection table's type is a closed
sort). The model's laws are then the claimed constants' own: none of them reads
a model-family constant.
-/

namespace IxVM.Consistency

open Ix.Kernel

universe u

/-- **A key whose entry in `env`, if any, is not a model-family constant.** -/
def KeptKey (env : Env .anon) (n : Key .anon) : Prop :=
  ∀ ci, env.find? n = some ci → isModelAux ci = false

/-- An input or role key is kept. -/
theorem keptKey_of_not_aux {env : Env .anon} {n : Key .anon}
    (h : ∀ b d, n ≠ .aux b d) : KeptKey env n := by
  intro ci hf
  have hn := Ix.Kernel.Semantics.Env.find?_name hf
  unfold isModelAux
  rw [hn]
  cases n <;> first | rfl | exact absurd rfl (h _ _)

/-- A projection table is not a model-family constant. -/
theorem isModelAux_projInfo (tbl : Ix.Kernel.ProjTable .anon) :
    isModelAux (.projInfo tbl : ConstantInfo .anon) = false := by
  unfold isModelAux
  cases (ConstantInfo.projInfo tbl).name <;> rfl

/-- Filtering keeps a lookup whose first hit passes the filter. -/
theorem find?_filter_kept (p q : ConstantInfo .anon → Bool) :
    ∀ l : List (ConstantInfo .anon), (∀ ci, l.find? q = some ci → p ci = true) →
      (l.filter p).find? q = l.find? q
  | [], _ => rfl
  | c :: l, h => by
    by_cases hq : q c = true
    · have hp : p c = true := h c (by simp [List.find?, hq])
      simp [List.filter, hp, List.find?, hq]
    · have h' : ∀ ci, l.find? q = some ci → p ci = true := fun ci hci =>
        h ci (by simp [List.find?, hq, hci])
      have ih := find?_filter_kept p q l h'
      cases hp : p c <;> simp [List.filter, hp, List.find?, hq, ih]

/-- **The sub-environment agrees with the environment at a kept key.** -/
theorem claimedEnv_find? {env : Env .anon} {n : Key .anon} (hK : KeptKey env n) :
    (claimedEnv env).find? n = env.find? n := by
  unfold claimedEnv Ix.Kernel.Env.find?
  exact find?_filter_kept _ _ env.consts (fun ci hci => by
    have := hK ci hci
    simp [this])

/-- Distinct names identify constants. -/
theorem eq_of_name_eq {l : List (ConstantInfo .anon)} (hnd : (l.map (·.name)).Nodup) :
    ∀ {x y : ConstantInfo .anon}, x ∈ l → y ∈ l → x.name = y.name → x = y := by
  induction l with
  | nil => intro x y hx; exact absurd hx List.not_mem_nil
  | cons c l ih =>
    intro x y hx hy hxy
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd (List.mem_map.mpr ⟨y, hy', hxy.symm⟩) hnd.1
    · exact absurd (List.mem_map.mpr ⟨x, hx', hxy⟩) hnd.1
    · exact ih hnd.2 hx' hy' hxy

/-- **With distinct names, the sub-environment has the environment's projection
tables** (a table is not a model-family constant). -/
theorem claimedEnv_findProj? {env : Env .anon} (hnd : (env.consts.map (·.name)).Nodup)
    (T : Key .anon) (i : Nat) : (claimedEnv env).findProj? T i = env.findProj? T i := by
  unfold Ix.Kernel.Env.findProj?
  cases he : env.find? (projTableName T) with
  | none =>
    have hc : (claimedEnv env).find? (projTableName T) = none := by
      rw [claimedEnv_find? (fun ci h => by rw [he] at h; exact nomatch h), he]
    rw [hc]
  | some ci =>
    by_cases hp : ∃ tbl, ci = .projInfo tbl
    · obtain ⟨tbl, rfl⟩ := hp
      have hc : (claimedEnv env).find? (projTableName T) = some (.projInfo tbl) := by
        rw [claimedEnv_find? (fun ci' h => by rw [he] at h; cases h; exact isModelAux_projInfo tbl), he]
      rw [hc]
    · have hone : ∀ x, (claimedEnv env).find? (projTableName T) = some x → x = ci :=
        fun x hc => eq_of_name_eq hnd
          (List.mem_filter.mp (Ix.Kernel.Semantics.Env.find?_mem hc)).1
          (Ix.Kernel.Semantics.Env.find?_mem he)
          ((Ix.Kernel.Semantics.Env.find?_name hc).trans
            (Ix.Kernel.Semantics.Env.find?_name he).symm)
      cases hc : (claimedEnv env).find? (projTableName T) with
      | none => cases ci <;> first | rfl | exact absurd ⟨_, rfl⟩ hp
      | some x => obtain rfl := hone x hc; rfl

/-- **The claimed sub-environment's model** (for L7): a model of the installed
environment, with distinct names, whose claimed constants' types and claimed
definitions' values mention only kept keys, restricts to `claimedEnv env`. -/
def claimedModel {V : Type u} [SetTheory V] {env : Env .anon} (M : Model V env)
    (hnd : (env.consts.map (·.name)).Nodup)
    (htype : ∀ c ∈ (claimedEnv env).consts, c.toConstantVal.type.RefsIn (KeptKey env))
    (hvalue : ∀ cv value hint, ConstantInfo.defnInfo cv value hint ∈ (claimedEnv env).consts →
      value.RefsIn (KeptKey env)) :
    Model V (claimedEnv env) :=
  M.restrict (K := KeptKey env) (fun _ hK => claimedEnv_find? hK) (claimedEnv_findProj? hnd)
    ⟨keptKey_of_not_aux (fun _ _ h => nomatch h), keptKey_of_not_aux (fun _ _ h => nomatch h),
      keptKey_of_not_aux (fun _ _ h => nomatch h), keptKey_of_not_aux (fun _ _ h => nomatch h),
      keptKey_of_not_aux (fun _ _ h => nomatch h), keptKey_of_not_aux (fun _ _ h => nomatch h),
      keptKey_of_not_aux (fun _ _ h => nomatch h)⟩
    (fun _ hc => (List.mem_filter.mp hc).1) htype hvalue
    (keptKey_of_not_aux (fun _ _ h => nomatch h)) (keptKey_of_not_aux (fun _ _ h => nomatch h))

/-- The model conjunct's form. -/
theorem nonempty_claimedModel {env : Env .anon}
    (hM : ∀ (V : Type u) [SetTheory V], Nonempty (Model V env))
    (hnd : (env.consts.map (·.name)).Nodup)
    (htype : ∀ c ∈ (claimedEnv env).consts, c.toConstantVal.type.RefsIn (KeptKey env))
    (hvalue : ∀ cv value hint, ConstantInfo.defnInfo cv value hint ∈ (claimedEnv env).consts →
      value.RefsIn (KeptKey env)) :
    ∀ (V : Type u) [SetTheory V], Nonempty (Model V (claimedEnv env)) :=
  fun V _ => let ⟨M⟩ := hM V; ⟨claimedModel M hnd htype hvalue⟩

end IxVM.Consistency
