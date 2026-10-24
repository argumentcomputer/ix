import Ix.Cert.DefinitionSnapshots

/-! Actual theorem fronts keep the checked proof separate from raw theorem
storage. Prefixes and counters come from the creating step's actual suffix;
no theorem value semantics or candidate checking is supplied here. -/
namespace Ix.Cert.TheoremSnapshots
open Ix.Kernel Ix.Kernel.Semantics
universe w
variable {md : Mode}

/-- The same actual reference run supplies the theorem's propositionhood and
annotated proof. Only the raw post-reader body is stored under thmInfo. -/
def TheoremFrontAt (ev : Evidences md) (ds : List (Declaration md)) (envA : Env md)
    (i : Nat) (cv : Ix.Kernel.ConstantVal md) (raw : Ix.Kernel.Expr md)
    (F : Nat) (before : Env md) (expected checkedProof : Ix.Kernel.Expr md) : Prop :=
  let step := checkDecl .verified (fueledOps .verified F) ev
  let after : Env md := ⟨.thmInfo ⟨cv.name, cv.levelParams, expected⟩ raw :: before.consts⟩
  ds[i]? = some (.thmDecl cv raw) ∧
  checkDeclsPure .verified (fueledOps .verified F) ev ds = .ok envA ∧
  (ds.take i).foldlM step Env.empty = .ok before ∧
  step before (.thmDecl cv raw) = .ok after ∧
  (ds.drop (i + 1)).foldlM step after = .ok envA ∧
  ConstantValRun .verified F before cv expected ∧
  (∃ stype u, inferTypeCore .verified before F 0 expected = .ok stype ∧
    ensureSortCore .verified before F 0 stype = .ok u ∧ Level.isEquiv u .zero = some true) ∧
  ValueFrontRun .verified F before cv raw expected checkedProof ∧
  envA.find? cv.name = some (.thmInfo ⟨cv.name, cv.levelParams, expected⟩ raw)

theorem reference_theorem_front_at
    {ev : Evidences md} {ds : List (Declaration md)} {envA : Env md}
    {i : Nat} {cv : Ix.Kernel.ConstantVal md} {raw : Ix.Kernel.Expr md}
    (accepted : Cached.AcceptsRef .verified ev ds envA)
    (atDecl : ds[i]? = some (.thmDecl cv raw)) :
    ∃ F before expected checkedProof,
      TheoremFrontAt ev ds envA i cv raw F before expected checkedProof := by
  obtain ⟨F, whole⟩ := accepted
  obtain ⟨bound, atValue⟩ := List.getElem?_eq_some_iff.mp atDecl
  have split : ds = ds.take i ++ .thmDecl cv raw :: ds.drop (i + 1) := by
    have eq := List.take_append_drop i ds
    rw [List.drop_eq_getElem_cons bound, atValue] at eq
    exact eq.symm
  have run := whole
  unfold checkDeclsPure at run
  rw [split] at run
  obtain ⟨before, prefixRun, rest⟩ := foldlM_append_ok run
  rw [List.foldlM_cons] at rest
  cases stepRun : checkDecl .verified (fueledOps .verified F) ev before (.thmDecl cv raw) with
  | error err => rw [stepRun] at rest; exact nomatch rest
  | ok after =>
    rw [stepRun] at rest
    change (ds.drop (i + 1)).foldlM (checkDecl .verified (fueledOps .verified F) ev) after = .ok envA at rest
    obtain ⟨expected, checkedProof, header, prop, value, installed⟩ := declThmRun_of stepRun
    have immediate : after.find? cv.name = some (.thmInfo ⟨cv.name, cv.levelParams, expected⟩ raw) := by
      rw [installed]
      simp only [Env.find?_cons, Ix.Kernel.ConstantInfo.name, Ix.Kernel.ConstantInfo.toConstantVal, ↓reduceIte]
    have growth := foldlM_checkDecl_post .verified (fueledOps .verified F) ev
      (ds.drop (i + 1)) after envA rest
    refine ⟨F, before, expected, checkedProof, atDecl, whole, prefixRun, ?_, ?_, header, prop, value,
      growth.persist immediate⟩
    · exact installed ▸ stepRun
    · exact installed ▸ rest

private theorem idxSpec_skip (key : Key md) (new old : List (Ix.Kernel.ConstantInfo md))
    (fresh : ∀ c ∈ new, c.name ≠ key) : idxSpec (new ++ old) key = idxSpec old key := by
  induction new with
  | nil => rfl
  | cons c new ih =>
    have no := beq_eq_false_iff_ne.mpr (fresh c List.mem_cons_self)
    simp only [List.cons_append, idxSpec, no, Bool.false_eq_true, ite_false]
    exact ih fun d member => fresh d (List.mem_cons_of_mem _ member)

/-- The raw theorem's actual installation position, without an offset or
uniqueness premise. The annotation witness does not enter the stored value. -/
theorem counter_prefix {ev : Evidences md} {ds : List (Declaration md)} {envA before : Env md}
    {i F : Nat} {cv : Ix.Kernel.ConstantVal md} {raw expected checkedProof : Ix.Kernel.Expr md}
    (front : TheoremFrontAt ev ds envA i cv raw F before expected checkedProof) :
    (mkFEnv envA).idx[cv.name]? = some (before.consts.length,
      .thmInfo ⟨cv.name, cv.levelParams, expected⟩ raw) ∧ envA.prefixTo before.consts.length = before := by
  let stored : Ix.Kernel.ConstantInfo md := .thmInfo ⟨cv.name, cv.levelParams, expected⟩ raw
  let after : Env md := ⟨stored :: before.consts⟩
  obtain ⟨_, _, _, _, suffixRun, _, _, _, _⟩ := front
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

/-- The actual accepted theorem supplies its logical prefix and bounded
lookup view. The physical env remains final; the current key stays hidden. -/
theorem checked_context (V : Type w) [SetTheory V]
    {ev : Evidences md} {ds : Array (Declaration md)} {envA : Env md}
    {i : Nat} {cv : Ix.Kernel.ConstantVal md} {raw : Ix.Kernel.Expr md}
    (run : Cached.checkDecls .verified ev ds = .ok envA)
    (atDecl : ds.toList[i]? = some (.thmDecl cv raw)) :
    ∃ F before expected checkedProof,
      TheoremFrontAt ev ds.toList envA i cv raw F before expected checkedProof ∧
      (mkFEnv envA).idx[cv.name]? = some (before.consts.length,
        .thmInfo ⟨cv.name, cv.levelParams, expected⟩ raw) ∧
      envA.prefixTo before.consts.length = before ∧
      ((mkFEnv envA).restrictTo before.consts.length).env = envA ∧
      (∀ n, ((mkFEnv envA).restrictTo before.consts.length).find? n = before.find? n) ∧
      ((mkFEnv envA).restrictTo before.consts.length).find? cv.name = none := by
  obtain ⟨F, before, expected, checkedProof, front⟩ := reference_theorem_front_at
    (Cached.checkDecls_refines_ref V rfl run) atDecl
  obtain ⟨counter, logical⟩ := counter_prefix front
  refine ⟨F, before, expected, checkedProof, front, counter, logical, rfl, ?_, ?_⟩
  · intro n
    rw [mkFEnv_find?_visibleBelow envA _ n (checked_names run), logical]
  · simp [FEnv.find?, FEnv.restrictTo, counter]

end Ix.Cert.TheoremSnapshots
