import Ix.IxVM.Consistency.Statement
import IxC.Kernel.Model.Restrict
import IxC.Kernel.Model.Open.Tables
import IxC.Kernel.Semantics.EnvFacts
import IxC.Kernel.Verify.Rename.Installs

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
sort), and that a kept structure's projection table names a kept constructor (the
kernel builds a table from one block: the structure's own constructor). The model's
laws are then the claimed constants' own: none of them reads a model-family constant.

The kernel's rules are sound over a model of an environment whose stored terms are
closed (`Ix.Kernel.Open.StoredClosed`) and whose stored telescopes have the binders the
laws read (`Ix.Kernel.Open.StoredArities`), whose projection tables are their structures'
(`Ix.Kernel.Open.StoredTables`), and whose η rules' constructors carry their families' level
parameters (`Ix.Kernel.Open.StoredEtaRules`). The fold's invariant gives all four for the
installed environment, and the claimed sub-environment keeps them:
`storedClosed_of_envModelOk`, `storedArities_of_envModelOk`, `storedEnv_of_envModelOk`.
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

/-- With distinct names, a claimed constant's own key is kept. -/
theorem keptKey_of_claimed {env : Env .anon} (hnd : (env.consts.map (·.name)).Nodup)
    {c : ConstantInfo .anon} (hc : c ∈ (claimedEnv env).consts) : KeptKey env c.name := by
  intro ci hci
  have hc' := List.mem_filter.mp hc
  obtain rfl := eq_of_name_eq hnd (Ix.Kernel.Semantics.Env.find?_mem hci) hc'.1
    (Ix.Kernel.Semantics.Env.find?_name hci)
  simpa using hc'.2

/-! ## What `Installs` gives -/

/-- One install step grows the environment by fresh constants. -/
theorem InstallStep.grows {env env₂ : Env .anon} {d : Declaration .anon}
    (h : InstallStep env d env₂) : Grows (fun _ => True) env env₂ := by
  obtain ⟨new, rfl, hnd, hfresh, -, -⟩ := h
  exact ⟨new, rfl, fun c hc => ⟨trivial, hfresh c hc⟩, hnd⟩

/-- **The installed environment's names are distinct.** -/
theorem Installs.nodup {ds : List (Declaration .anon)} {env : Env .anon} (h : Installs ds env) :
    (env.consts.map (·.name)).Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | snoc _ hstep ih => exact hstep.grows.nodup ih

/-- A lookup in front of a list finds a constant of distinct-named new constants. -/
theorem find?_front {new rest : List (ConstantInfo .anon)} (hnd : (new.map (·.name)).Nodup)
    {c : ConstantInfo .anon} (hc : c ∈ new) :
    (⟨new ++ rest⟩ : Env .anon).find? c.name = some c := by
  unfold Env.find?
  rw [List.find?_append]
  obtain ⟨c', hc'⟩ : ∃ c', new.find? (·.name == c.name) = some c' :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨c, hc, by simp⟩)
  have hname : c'.name = c.name := by simpa using List.find?_some hc'
  obtain rfl := eq_of_name_eq hnd (List.mem_of_find?_eq_some hc') hc hname
  rw [hc']
  rfl

/-- **Every constant a declaration installs is stored as declared** in the
environment the declarations install. -/
theorem Installs.stored {ds : List (Declaration .anon)} {env : Env .anon} (h : Installs ds env) :
    ∀ {d : Declaration .anon}, d ∈ ds → ∀ {ci₀ : ConstantInfo .anon}, ci₀ ∈ installs d →
      ∃ ci, env.find? ci₀.name = some ci ∧ StoredAs ci ci₀ := by
  induction h with
  | nil => intro d hd; exact absurd hd List.not_mem_nil
  | snoc _ hstep ih =>
    intro d hd ci₀ hci₀
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨ci, hf, hs⟩ := ih hd hci₀
      exact ⟨ci, hstep.grows.persist hf, hs⟩
    · obtain rfl := List.mem_singleton.mp hd
      obtain ⟨new, rfl, hnd, -, hall, -⟩ := hstep
      obtain ⟨ci, hci, hs⟩ := hall ci₀ hci₀
      exact ⟨ci, by rw [← hs.name_eq]; exact find?_front hnd hci, hs⟩

/-- **A declared constant at an input or role key is claimed**: the claimed
sub-environment stores it as declared. -/
theorem Installs.claimed {ds : List (Declaration .anon)} {env : Env .anon} (h : Installs ds env)
    {d : Declaration .anon} (hd : d ∈ ds) {ci₀ : ConstantInfo .anon} (hci₀ : ci₀ ∈ installs d)
    (hk : ∀ b t, ci₀.name ≠ .aux b t) :
    ∃ ci, (claimedEnv env).find? ci₀.name = some ci ∧ StoredAs ci ci₀ := by
  obtain ⟨ci, hf, hs⟩ := h.stored hd hci₀
  exact ⟨ci, by rw [claimedEnv_find? (keptKey_of_not_aux hk)]; exact hf, hs⟩

/-- **The claimed sub-environment's model** (for L7): a model of the installed
environment, with distinct names, whose claimed constants' types, claimed
definitions' values and claimed recursor rules' right-hand sides mention only kept
keys, and whose kept structures' projection tables name kept constructors, restricts to
`claimedEnv env`. -/
def claimedModel {V : Type u} [SetTheory V] {env : Env .anon} (M : Model V env)
    (hnd : (env.consts.map (·.name)).Nodup)
    (htype : ∀ c ∈ (claimedEnv env).consts, c.toConstantVal.type.RefsIn (KeptKey env))
    (hvalue : ∀ cv value hint, ConstantInfo.defnInfo cv value hint ∈ (claimedEnv env).consts →
      value.RefsIn (KeptKey env))
    (hrhs : ∀ cv mI rP rules, ConstantInfo.recInfo cv mI rP rules ∈ (claimedEnv env).consts →
      ∀ rl ∈ rules, rl.rhs.RefsIn (KeptKey env))
    (hctor : ∀ T i entry, (claimedEnv env).findProj? T i = some entry → KeptKey env T →
      KeptKey env entry.ctor) :
    Model V (claimedEnv env) :=
  M.restrict (K := KeptKey env) (fun _ hK => claimedEnv_find? hK) (claimedEnv_findProj? hnd)
    ⟨keptKey_of_not_aux (fun _ _ h => nomatch h), keptKey_of_not_aux (fun _ _ h => nomatch h),
      keptKey_of_not_aux (fun _ _ h => nomatch h), keptKey_of_not_aux (fun _ _ h => nomatch h),
      keptKey_of_not_aux (fun _ _ h => nomatch h), keptKey_of_not_aux (fun _ _ h => nomatch h),
      keptKey_of_not_aux (fun _ _ h => nomatch h)⟩
    (fun _ hc => (List.mem_filter.mp hc).1) (fun _ hc => keptKey_of_claimed hnd hc) htype hvalue
    hrhs (keptKey_of_not_aux (fun _ _ h => nomatch h)) (keptKey_of_not_aux (fun _ _ h => nomatch h))
    ⟨keptKey_of_not_aux (fun _ _ h => nomatch h), keptKey_of_not_aux (fun _ _ h => nomatch h)⟩
    hctor

/-- **The claimed sub-environment's stored terms are closed** when the installed
environment's are: its constants are among the environment's. -/
theorem storedClosed_claimedEnv {env : Env .anon} (h : Ix.Kernel.Open.StoredClosed env) :
    Ix.Kernel.Open.StoredClosed (claimedEnv env) :=
  h.of_sub fun _ hc => (List.mem_filter.mp hc).1

/-- **The fold's invariant closes the claimed sub-environment's stored terms**: the
invariant holds the environment's well-formedness (`EnvWF`), which includes closure. -/
theorem storedClosed_of_envModelOk {V : Type u} [SetTheory V] {μ : CheckMode}
    {env : Env .anon} (h : Ix.Kernel.Model.EnvModelOk V μ env) :
    Ix.Kernel.Open.StoredClosed (claimedEnv env) := by
  obtain ⟨⟨m⟩, -⟩ := h
  exact storedClosed_claimedEnv (Ix.Kernel.Open.EnvWF.storedClosed m.base2.wf)

/-- With distinct names, a constant the claimed sub-environment finds is the
environment's at that key. -/
theorem claimedEnv_find?_some {env : Env .anon} (hnd : (env.consts.map (·.name)).Nodup)
    {n : Key .anon} {ci : ConstantInfo .anon} (h : (claimedEnv env).find? n = some ci) :
    env.find? n = some ci := by
  have hK : KeptKey env n := by
    have hk := keptKey_of_claimed hnd (List.mem_of_find?_eq_some h)
    rwa [Ix.Kernel.Semantics.Env.find?_name h] at hk
  rw [← claimedEnv_find? hK]
  exact h

/-- **The fold's invariant gives the claimed sub-environment's stored telescopes their
binders** (`Ix.Kernel.Open.StoredArities`): the invariant holds them of the installed
environment, and with distinct names the sub-environment's lookups are its. -/
theorem storedArities_of_envModelOk {V : Type u} [SetTheory V] {μ : CheckMode}
    {env : Env .anon} (h : Ix.Kernel.Model.EnvModelOk V μ env)
    (hnd : (env.consts.map (·.name)).Nodup) :
    Ix.Kernel.Open.StoredArities (claimedEnv env) := by
  obtain ⟨⟨m⟩, -⟩ := h
  exact (Ix.Kernel.Open.EnvModel.storedArities m.base2).of_find
    fun _ _ hf => claimedEnv_find?_some hnd hf

/-- **The fold's invariant gives the claimed sub-environment every stored-environment fact
the rules read** (`Ix.Kernel.Open.StoredEnv`): the invariant holds them of the installed
environment, and with distinct names the sub-environment's constants, lookups and
projection tables are its. -/
theorem storedEnv_of_envModelOk {V : Type u} [SetTheory V] {μ : CheckMode}
    {env : Env .anon} (h : Ix.Kernel.Model.EnvModelOk V μ env)
    (hnd : (env.consts.map (·.name)).Nodup) :
    Ix.Kernel.Open.StoredEnv (claimedEnv env) := by
  obtain ⟨⟨m⟩, -⟩ := h
  exact (Ix.Kernel.Open.EnvModelM.storedEnv m).of_find (fun _ hc => (List.mem_filter.mp hc).1)
    (fun _ _ hf => claimedEnv_find?_some hnd hf) (claimedEnv_findProj? hnd)

/-- The model conjunct's form. -/
theorem nonempty_claimedModel {env : Env .anon}
    (hM : ∀ (V : Type u) [SetTheory V], Nonempty (Model V env))
    (hnd : (env.consts.map (·.name)).Nodup)
    (htype : ∀ c ∈ (claimedEnv env).consts, c.toConstantVal.type.RefsIn (KeptKey env))
    (hvalue : ∀ cv value hint, ConstantInfo.defnInfo cv value hint ∈ (claimedEnv env).consts →
      value.RefsIn (KeptKey env))
    (hrhs : ∀ cv mI rP rules, ConstantInfo.recInfo cv mI rP rules ∈ (claimedEnv env).consts →
      ∀ rl ∈ rules, rl.rhs.RefsIn (KeptKey env))
    (hctor : ∀ T i entry, (claimedEnv env).findProj? T i = some entry → KeptKey env T →
      KeptKey env entry.ctor) :
    ∀ (V : Type u) [SetTheory V], Nonempty (Model V (claimedEnv env)) :=
  fun V _ => let ⟨M⟩ := hM V; ⟨claimedModel M hnd htype hvalue hrhs hctor⟩

end IxVM.Consistency
