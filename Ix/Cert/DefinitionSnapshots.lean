import Ix.Cert.AdmittedTargetFronts

/-! The actual definition front determines its installation counter and
executable prefix. A restricted FEnv retains the FULL final `.env`; only
its bounded lookup agrees with the reconstructed logical prefix. -/
namespace Ix.Cert.DefinitionSnapshots
open Ix.Kernel Ix.Cert.ReferenceFronts
universe w
variable {md : Mode}

private theorem idxSpec_skip (key : Key md) (new old : List (Ix.Kernel.ConstantInfo md))
    (fresh : ∀ c ∈ new, c.name ≠ key) : idxSpec (new ++ old) key = idxSpec old key := by
  induction new with
  | nil => rfl
  | cons c new ih =>
    have no := beq_eq_false_iff_ne.mpr (fresh c List.mem_cons_self)
    simp only [List.cons_append, idxSpec, no, Bool.false_eq_true, ite_false]
    exact ih fun d member => fresh d (List.mem_cons_of_mem _ member)

/-- No guessed offset: the actual suffix preserves the creating definition
and every older constant, while all newer names are fresh relative to it. -/
theorem counter_prefix {ev : Evidences md} {ds : List (Declaration md)} {envA before : Env md}
    {i F : Nat} {cv : Ix.Kernel.ConstantVal md} {raw expected checked : Ix.Kernel.Expr md}
    {hint : ReducibilityHint}
    (front : DefinitionFrontAt ev ds envA i cv raw hint F before expected checked) :
    (mkFEnv envA).idx[cv.name]? = some (before.consts.length,
      .defnInfo ⟨cv.name, cv.levelParams, expected⟩ checked hint) ∧
    envA.prefixTo before.consts.length = before := by
  let stored : Ix.Kernel.ConstantInfo md := .defnInfo ⟨cv.name, cv.levelParams, expected⟩ checked hint
  let after : Env md := ⟨stored :: before.consts⟩
  obtain ⟨_, _, _, _, suffixRun, _, _, _⟩ := front
  have growth := foldlM_checkDecl_post .verified (fueledOps .verified F) ev
    (ds.drop (i + 1)) after envA suffixRun
  obtain ⟨new, extent, fresh⟩ := growth
  have atHead : after.find? cv.name = some stored := by
    simp [after, stored, Env.find?, Ix.Kernel.ConstantInfo.name, Ix.Kernel.ConstantInfo.toConstantVal]
  have other : ∀ c ∈ new, c.name ≠ cv.name := by
    intro c member same
    have absent := (fresh c member).2
    rw [same, atHead] at absent
    cases absent
  constructor
  · rw [mkFEnv_idx, extent, idxSpec_skip cv.name new after.consts other]
    simp [after, stored, idxSpec, Ix.Kernel.ConstantInfo.name, Ix.Kernel.ConstantInfo.toConstantVal]
  · exact Env.prefixTo_of_extends (env := before) (env' := envA) (new := new ++ [stored])
      (by simpa [after, List.append_assoc] using extent)

private theorem checked_names {ev : Evidences md} {ds : Array (Declaration md)} {envA : Env md}
    (run : Cached.checkDecls .verified ev ds = .ok envA) : NodupNames envA := by
  obtain ⟨fc, finalEnv⟩ := Cached.checkDecls_fullyChecked .verified run
  obtain ⟨n, s, trace⟩ := fc.1.run
  have chain := (Cached.installRun_trace .verified trace (Cached.PushChain.refl Env.empty)).1
  rw [← finalEnv]
  exact chain.2.2 List.nodup_nil

/-- Actual cached acceptance supplies uniqueness internally. The logical
prefix and the lookup view agree with this SAME index/front; the view's env
field remains final. This also covers full-install native Nat definitions. -/
theorem checked_context (V : Type w) [SetTheory V]
    {ev : Evidences md} {ds : Array (Declaration md)} {envA : Env md}
    {i : Nat} {cv : Ix.Kernel.ConstantVal md} {raw : Ix.Kernel.Expr md} {hint : ReducibilityHint}
    (run : Cached.checkDecls .verified ev ds = .ok envA)
    (atDecl : ds.toList[i]? = some (.defnDecl cv raw hint)) :
    ∃ F before expected checked,
      DefinitionFrontAt ev ds.toList envA i cv raw hint F before expected checked ∧
      (mkFEnv envA).idx[cv.name]? = some (before.consts.length,
        .defnInfo ⟨cv.name, cv.levelParams, expected⟩ checked hint) ∧
      envA.prefixTo before.consts.length = before ∧
      ((mkFEnv envA).restrictTo before.consts.length).env = envA ∧
      (∀ n, ((mkFEnv envA).restrictTo before.consts.length).find? n = before.find? n) ∧
      ((mkFEnv envA).restrictTo before.consts.length).find? cv.name = none := by
  obtain ⟨F, before, expected, checked, front⟩ := reference_definition_front_at
    (Cached.checkDecls_refines_ref V rfl run) atDecl
  obtain ⟨counter, logical⟩ := counter_prefix front
  refine ⟨F, before, expected, checked, front, counter, logical, rfl, ?_, ?_⟩
  · intro n
    rw [mkFEnv_find?_visibleBelow envA _ n (checked_names run), logical]
  · simp [FEnv.find?, FEnv.restrictTo, counter]

end Ix.Cert.DefinitionSnapshots
