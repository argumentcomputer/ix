import Ix.Cert.AdmittedTargetFronts
import Ix.CompileCert.Loop

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

open Ix.Kernel.Admission (Binding Limits Records Error)
open Ix.Kernel.Reader (Prelude preludeFor)

/-- One actual prepared/check run, indexed once after acceptance. -/
structure Receipt where
  table : RoleTable
  pre : Prelude .anon
  ev : Evidences .anon
  ds : Array (Declaration .anon)
  index : FEnv .anon

def Receipt.env (r : Receipt) : Env .anon := r.index.env

/-- Unwired receipt adapter. The existing preparation and checker run once;
all original binding/prelude/byte/reader/kernel errors retain their order. -/
def checkReceipt (binding : Binding) (limits : Limits) (records : Records) (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option ReducibilityHint) : Except Error Receipt := do
  let table ← (Admission.admitBinding Address.admissionHash binding).mapError .binding
  let pre ← (preludeFor table).mapError .prelude
  let (ev, ds) ← Admission.prepareWith Address.admissionHash binding pre limits records blobs hint
  let envA ← (Cached.checkDecls .verified ev ds).mapError fun (e, i) => .kernel e i
  return ⟨table, pre, ev, ds, mkFEnv envA⟩

theorem checkReceipt_env (binding : Binding) (limits : Limits) (records : Records) (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option ReducibilityHint) :
    (checkReceipt binding limits records blobs hint).map Receipt.env =
      Ixon.Authenticated.checkBytes binding limits records blobs hint := by
  change Receipt.env <$> checkReceipt binding limits records blobs hint = _
  simp only [checkReceipt, map_bind, map_pure, Receipt.env, mkFEnv, bind_pure]
  rfl

private theorem mapError_ok {ε ε' α : Type} {f : ε → ε'} {x : Except ε α} {v : α}
    (h : x.mapError f = .ok v) : x = .ok v := by
  cases x with
  | error e => cases h
  | ok a => cases h; rfl

theorem checkReceipt_ok {binding limits records blobs hint r}
    (run : checkReceipt binding limits records blobs hint = .ok r) :
    Admission.admitBinding Address.admissionHash binding = .ok r.table ∧
    preludeFor r.table = .ok r.pre ∧
    Admission.prepareWith Address.admissionHash binding r.pre limits records blobs hint = .ok (r.ev, r.ds) ∧
    Cached.checkDecls .verified r.ev r.ds = .ok r.env ∧ r.index = mkFEnv r.env := by
  unfold checkReceipt at run
  obtain ⟨table, admitted, rest⟩ := Ix.CompileCert.Loop.except_bind_ok.mp run
  obtain ⟨pre, prelude, rest⟩ := Ix.CompileCert.Loop.except_bind_ok.mp rest
  obtain ⟨⟨ev, ds⟩, prepared, rest⟩ := Ix.CompileCert.Loop.except_bind_ok.mp rest
  obtain ⟨envA, checked, returned⟩ := Ix.CompileCert.Loop.except_bind_ok.mp rest
  simp only [pure, Except.pure, Except.ok.injEq] at returned
  subst r
  exact ⟨mapError_ok admitted, mapError_ok prelude, prepared, mapError_ok checked, rfl⟩

structure Snapshot where
  position : Nat
  cv : Ix.Kernel.ConstantVal .anon
  raw : Ix.Kernel.Expr .anon
  hint : ReducibilityHint
  counter : Nat
  expected : Ix.Kernel.Expr .anon
  checked : Ix.Kernel.Expr .anon
  view : FEnv .anon

/-- Executable logical prefix. The view's own env remains final. -/
def Snapshot.before (s : Snapshot) : Env .anon := s.view.env.prefixTo s.counter

def Receipt.snapshot (r : Receipt) (i : Nat) : Except String Snapshot := do
  let some d := r.ds[i]? | throw "snapshot: declaration index is unavailable"
  let .defnDecl cv raw hint := d | throw "snapshot: declaration is not a definition"
  let some (counter, c) := r.index.idx[cv.name]? | throw "snapshot: definition index entry is unavailable"
  let .defnInfo stored checked _ := c | throw "snapshot: indexed constant is not a definition"
  return ⟨i, cv, raw, hint, counter, stored.type, checked, r.index.restrictTo counter⟩

/-- Every actual definition succeeds, with the same raw declaration, stored
header/body and exact prefix. No counter, uniqueness or prefix premise. -/
theorem snapshot_of_check (V : Type w) [SetTheory V] {binding limits records blobs hint r}
    (run : checkReceipt binding limits records blobs hint = .ok r)
    {i : Nat} {cv : Ix.Kernel.ConstantVal .anon} {raw : Ix.Kernel.Expr .anon} {h : ReducibilityHint}
    (atDecl : r.ds.toList[i]? = some (.defnDecl cv raw h)) :
    ∃ F before expected checked,
      let snap : Snapshot := ⟨i, cv, raw, h, before.consts.length, expected, checked,
        r.index.restrictTo before.consts.length⟩
      DefinitionFrontAt r.ev r.ds.toList r.env i cv raw h F before expected checked ∧
      r.snapshot i = .ok snap ∧ snap.before = before ∧ snap.view.env = r.env ∧
      (∀ n, snap.view.find? n = before.find? n) ∧ snap.view.find? cv.name = none := by
  obtain ⟨_, _, _, checkedRun, canonical⟩ := checkReceipt_ok run
  obtain ⟨F, before, expected, checked, front, counter, logical, _, lookup, hidden⟩ :=
    checked_context V checkedRun atDecl
  have indexed : r.index.idx[cv.name]? = some (before.consts.length,
      .defnInfo ⟨cv.name, cv.levelParams, expected⟩ checked h) := by rw [canonical]; exact counter
  have atArray : r.ds[i]? = some (.defnDecl cv raw h) := by simpa using atDecl
  refine ⟨F, before, expected, checked, front, ?_, ?_, rfl, ?_, ?_⟩
  · simp [Receipt.snapshot, atArray, indexed, pure, Except.pure]
  · exact logical
  · intro n
    rw [canonical]
    exact lookup n
  · rw [canonical]
    exact hidden

end Ix.Cert.DefinitionSnapshots
