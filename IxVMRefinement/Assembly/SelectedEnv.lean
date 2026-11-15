import IxVMRefinement.Assembly.SupportedTerms
import Ix.IxVM.Consistency.Restrict

/-! # Selecting and arranging the final modeled environment

Selection depends only on constant names. Keeping projection-table keys preserves every
projection lookup. Once selected terms have their actual support, the model restricts, and
distinct-name lookup agreement makes its final list order immaterial.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel

universe u

noncomputable def selectEnv (env : Env .anon) (K : Key .anon → Prop) : Env .anon :=
  ⟨env.consts.filter fun ci => @decide (K ci.name) (Classical.propDecidable _)⟩

theorem mem_selectEnv {env : Env .anon} {K : Key .anon → Prop}
    {ci : ConstantInfo .anon} :
    ci ∈ (selectEnv env K).consts ↔ ci ∈ env.consts ∧ K ci.name := by
  simp only [selectEnv, List.mem_filter, @decide_eq_true_eq _ (Classical.propDecidable _)]

theorem selectEnv_find {env : Env .anon} {K : Key .anon → Prop}
    {n : Key .anon} (hn : K n) : (selectEnv env K).find? n = env.find? n := by
  unfold selectEnv Env.find?
  apply IxVM.Consistency.find?_filter_kept
  intro ci hci
  have hname : ci.name = n := by simpa using List.find?_some hci
  apply decide_eq_true
  rw [hname]
  exact hn

theorem selectEnv_findProj {env : Env .anon} {K : Key .anon → Prop}
    (htables : ∀ T, K (projTableName T)) (T : Key .anon) (i : Nat) :
    (selectEnv env K).findProj? T i = env.findProj? T i := by
  unfold Env.findProj?
  rw [selectEnv_find (htables T)]

theorem selectEnv_nodup {env : Env .anon} {K : Key .anon → Prop}
    (hnd : (env.consts.map (·.name)).Nodup) :
    ((selectEnv env K).consts.map (·.name)).Nodup := by
  have hsub : (selectEnv env K).consts.Sublist env.consts := List.filter_sublist
  exact (hsub.map (·.name)).nodup hnd

/-- The selected model uses support proved for the constants actually selected. It places no
support requirement on constants omitted from the final environment. -/
def selectEnv_model {W : Type u} [SetTheory W] {env : Env .anon} {K : Key .anon → Prop}
    (M : Model W env) (htables : ∀ T, K (projTableName T))
    (hnat : K natZeroName ∧ K natSuccName)
    (hsupported : ∀ ci ∈ env.consts, K ci.name → SupportedConstant K ci)
    (hfalse : K falseName) (heq : K eqName) (hbool : K boolTrueName ∧ K boolFalseName)
    (hctor : ∀ T i entry, env.findProj? T i = some entry → K T → K entry.ctor)
    (hbody : ∀ T i entry, env.findProj? T i = some entry → K T → entry.body.Supports K) :
    Model W (selectEnv env K) := by
  have hs : ∀ ci ∈ (selectEnv env K).consts, SupportedConstant K ci := by
    intro ci hci
    obtain ⟨hmem, hkey⟩ := mem_selectEnv.mp hci
    exact hsupported ci hmem hkey
  apply M.restrict_supported
    (fun _ hk => selectEnv_find hk) (selectEnv_findProj htables) hnat
    (fun _ hc => (mem_selectEnv.mp hc).1)
    (fun _ hc => (mem_selectEnv.mp hc).2)
    (fun ci hc => (hs ci hc).2.1)
    (fun cv value hint hc => (hs (.defnInfo cv value hint) hc).2.2)
    (fun cv mI rP rules hc => (hs (.recInfo cv mI rP rules) hc).2.2)
    hfalse heq hbool
  · intro T i entry hentry hT
    rw [selectEnv_findProj htables] at hentry
    exact hctor T i entry hentry hT
  · intro T i entry hentry hT
    rw [selectEnv_findProj htables] at hentry
    exact hbody T i entry hentry hT

/-- Membership and distinct names determine every lookup, independently of list order. -/
theorem find_eq_of_same_members {env env' : Env .anon}
    (hnd : (env.consts.map (·.name)).Nodup)
    (hmem : ∀ ci, ci ∈ env'.consts ↔ ci ∈ env.consts) (n : Key .anon) :
    env'.find? n = env.find? n := by
  cases hsource : env.find? n with
  | none =>
    cases htarget : env'.find? n with
    | none => rfl
    | some ci =>
      have hci : ci ∈ env.consts := (hmem ci).mp (Semantics.Env.find?_mem htarget)
      have hfalse := List.find?_eq_none.mp hsource ci hci
      exact (hfalse (by simpa using beq_iff_eq.mpr (Semantics.Env.find?_name htarget))).elim
  | some ci =>
    cases htarget : env'.find? n with
    | none =>
      have hci : ci ∈ env'.consts := (hmem ci).mpr (Semantics.Env.find?_mem hsource)
      have hfalse := List.find?_eq_none.mp htarget ci hci
      exact (hfalse (by simpa using beq_iff_eq.mpr (Semantics.Env.find?_name hsource))).elim
    | some ci' =>
      have heq := IxVM.Consistency.eq_of_name_eq hnd
        ((hmem ci').mp (Semantics.Env.find?_mem htarget))
        (Semantics.Env.find?_mem hsource)
        ((Semantics.Env.find?_name htarget).trans (Semantics.Env.find?_name hsource).symm)
      exact congrArg some heq

private theorem refsIn_true {md : Mode} (e : Expr md) : e.RefsIn (fun _ => True) := by
  induction e <;> simp_all [Expr.RefsIn]

/-- A model is independent of the storage order when membership and lookups are unchanged. -/
def model_of_same_members {W : Type u} [SetTheory W] {env env' : Env .anon}
    (M : Model W env) (hnd : (env.consts.map (·.name)).Nodup)
    (hmem : ∀ ci, ci ∈ env'.consts ↔ ci ∈ env.consts) : Model W env' := by
  have hfind := find_eq_of_same_members hnd hmem
  have hproj : ∀ T i, env'.findProj? T i = env.findProj? T i := by
    intro T i
    unfold Env.findProj?
    rw [hfind]
  exact M.restrict (K := fun _ => True) (fun n _ => hfind n) hproj
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    (fun ci hc => (hmem ci).mp hc) (fun _ _ => trivial)
    (fun ci _ => refsIn_true ci.toConstantVal.type)
    (fun _ value _ _ => refsIn_true value)
    (fun _ _ _ _ _ rl _ => refsIn_true rl.rhs)
    trivial trivial ⟨trivial, trivial⟩ (fun _ _ _ _ _ => trivial)
    (fun _ _ entry _ _ => refsIn_true entry.body)

end IxVM.Refinement.Assembly
