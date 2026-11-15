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
  classical
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
noncomputable def selectEnv_model {W : Type u} [SetTheory W] {env : Env .anon} {K : Key .anon → Prop}
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

private theorem selected_findProj_info {env : Env .anon} {T : Key .anon}
    {i : Nat} {entry : ProjEntry .anon} (h : env.findProj? T i = some entry) :
    ∃ tbl : ProjTable .anon,
      env.find? (projTableName T) = some (.projInfo tbl) ∧
      i < tbl.numFields ∧ entry = tbl.entry i := by
  unfold Env.findProj? at h
  cases hfind : env.find? (projTableName T) with
  | none => rw [hfind] at h; cases h
  | some ci =>
    rw [hfind] at h
    cases ci with
    | projInfo tbl =>
      dsimp only at h
      split at h
      · rename_i hi
        injection h with hentry
        exact ⟨tbl, rfl, hi, hentry.symm⟩
      · cases h
    | _ => cases h

/-- Projection bodies inherit support from the selected constructor's actual stored type.
The equality to generated field bodies comes from the checking fold's `TableBodies` invariant. -/
theorem projection_body_supported {env : Env .anon} {K : Key .anon → Prop}
    (htables : Model.TableBodies env)
    (htypes : ∀ ci ∈ env.consts, K ci.name → ci.toConstantVal.type.Supports K)
    (hctor : ∀ T i entry, env.findProj? T i = some entry → K T → K entry.ctor)
    {T : Key .anon} {i : Nat} {entry : ProjEntry .anon}
    (hentry : env.findProj? T i = some entry) (hT : K T) : entry.body.Supports K := by
  have hKctor := hctor T i entry hentry hT
  obtain ⟨tbl, hfind, hi, rfl⟩ := selected_findProj_info hentry
  change K tbl.ctor at hKctor
  obtain ⟨cvC, hfind_ctor, hbodies, _⟩ := htables (projTableName T) tbl hfind
  have hcty : cvC.type.Supports K := htypes (.ctorInfo cvC tbl.numParams tbl.numFields)
    (Semantics.Env.find?_mem hfind_ctor) (by
      rw [Semantics.Env.find?_name hfind_ctor]
      exact hKctor)
  obtain ⟨hsize, hall⟩ :=
    supports_structProjBodies tbl.structName tbl.numParams tbl.numFields hcty hbodies
  have hi' : i < tbl.bodies.size := by omega
  change (tbl.bodies.getD i default).Supports K
  unfold Array.getD
  simp only [hi', ↓reduceDIte]
  exact hall tbl.bodies[i] (Array.mem_toList_iff.mpr (Array.getElem_mem hi'))

/-- Restrict using the full checking environment's table invariant; projection-body support
is derived from selected constructor support, rather than supplied independently. -/
noncomputable def selectEnv_model_of_tableBodies
    {W : Type u} [SetTheory W] {env : Env .anon} {K : Key .anon → Prop}
    (M : Model W env) (hkeepTables : ∀ T, K (projTableName T))
    (hnat : K natZeroName ∧ K natSuccName)
    (hsupported : ∀ ci ∈ env.consts, K ci.name → SupportedConstant K ci)
    (hfalse : K falseName) (heq : K eqName) (hbool : K boolTrueName ∧ K boolFalseName)
    (htables : Model.TableBodies env)
    (hctor : ∀ T i entry, env.findProj? T i = some entry → K T → K entry.ctor) :
    Model W (selectEnv env K) :=
  selectEnv_model M hkeepTables hnat hsupported hfalse heq hbool hctor
    (fun _ _ _ he hT => projection_body_supported htables
      (fun ci hc hk => (hsupported ci hc hk).2.1) hctor he hT)

/-- Preserving the actual stored projection tables suffices; absent table keys and keys
holding another kind of constant need not be selected. -/
theorem selectEnv_findProj_stored {env : Env .anon} {K : Key .anon → Prop}
    (hnd : (env.consts.map (·.name)).Nodup)
    (htables : ∀ n tbl, env.find? n = some (.projInfo tbl) → K n)
    (T : Key .anon) (i : Nat) : (selectEnv env K).findProj? T i = env.findProj? T i := by
  unfold Env.findProj?
  cases hsource : env.find? (projTableName T) with
  | none =>
    have hnone : (selectEnv env K).find? (projTableName T) = none := by
      apply List.find?_eq_none.mpr
      intro ci hci hname
      exact List.find?_eq_none.mp hsource ci (mem_selectEnv.mp hci).1 hname
    rw [hnone]
  | some ci =>
    by_cases hp : ∃ tbl, ci = .projInfo tbl
    · obtain ⟨tbl, rfl⟩ := hp
      rw [selectEnv_find (htables _ tbl hsource), hsource]
    · have hone : ∀ x, (selectEnv env K).find? (projTableName T) = some x → x = ci := by
        intro x hx
        exact IxVM.Consistency.eq_of_name_eq hnd
          (mem_selectEnv.mp (Semantics.Env.find?_mem hx)).1
          (Semantics.Env.find?_mem hsource)
          ((Semantics.Env.find?_name hx).trans (Semantics.Env.find?_name hsource).symm)
      cases htarget : (selectEnv env K).find? (projTableName T) with
      | none => cases ci <;> first | rfl | exact absurd ⟨_, rfl⟩ hp
      | some x => obtain rfl := hone x htarget; rfl

/-- Select a model while retaining exactly the stored projection-table keys. -/
noncomputable def selectEnv_model_stored_tables {W : Type u} [SetTheory W] {env : Env .anon} {K : Key .anon → Prop}
    (M : Model W env) (hnd : (env.consts.map (·.name)).Nodup)
    (htables : ∀ n tbl, env.find? n = some (.projInfo tbl) → K n)
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
    (fun _ hk => selectEnv_find hk) (selectEnv_findProj_stored hnd htables) hnat
    (fun _ hc => (mem_selectEnv.mp hc).1)
    (fun _ hc => (mem_selectEnv.mp hc).2)
    (fun ci hc => (hs ci hc).2.1)
    (fun cv value hint hc => (hs (.defnInfo cv value hint) hc).2.2)
    (fun cv mI rP rules hc => (hs (.recInfo cv mI rP rules) hc).2.2)
    hfalse heq hbool
  · intro T i entry hentry hT
    rw [selectEnv_findProj_stored hnd htables] at hentry
    exact hctor T i entry hentry hT
  · intro T i entry hentry hT
    rw [selectEnv_findProj_stored hnd htables] at hentry
    exact hbody T i entry hentry hT

end IxVM.Refinement.Assembly
