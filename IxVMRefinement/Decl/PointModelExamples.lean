import IxVMRefinement.Decl.PointModel

/-! # Constructors-only blocks over the pinned `PUnit` basis

`PointBlock` (`Decl/PointModel.lean`) is inhabited, by derivations, at three blocks over the
environment that stores the kernel's `PUnit` pin and nothing else:

* a two-type mutual block, `A B : Type` with `A.mk : B → A` and `B.mk : A → B`;
* a block with a parameter, `W : Type → Type` with `W.mk : (α : Type) → α → W α`;
* over the second, a nested-shaped block: `T : Type` with `T.mk : W T → T`, whose constructor
  takes a field whose type applies the earlier-installed `W` to the block's own type.

Each installs by `pointBlock_install`, and the fold's invariant holds at the result in every
set theory, with no hypothesis left (`mutual_installs`, `nested_installs`). The second and third
are installed one after the other: the invariant the first install gives is the one the second
takes.
-/

namespace IxVM.Refinement.Decl.Point.Examples

open Ix.Kernel
open Ix.Kernel.Semantics
open Ix.Kernel.Model
open Ix.Kernel.Rules (Red DefEq Infer Grade)
open IxVM.Consistency (StoredAs ValStored InstallStep Annotates)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

/-! ## Keys -/

/-- An address for each natural number: a byte string of that length. -/
def adr (n : Nat) : Address := ⟨⟨(List.replicate n (0 : UInt8)).toArray⟩⟩

theorem adr_inj {m n : Nat} (h : adr m = adr n) : m = n := by
  have := congrArg (fun a : Address => a.hash.data.size) h
  simpa [adr] using this

/-- The input key at `adr n`. -/
def key (n : Nat) : Key .anon := .id (adr n)

@[simp] theorem key_inj {m n : Nat} : key m = key n ↔ m = n :=
  ⟨fun e => adr_inj (Key.id.inj e), fun h => by rw [h]⟩

/-- An input key is not reserved. -/
theorem reserved_id (a : Address) :
    reservedBasisNames.contains (Key.id a : Key .anon) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hm : (Key.id a : Key .anon) ∈ reservedBasisNames := List.contains_iff_mem.mp h
  simp only [reservedBasisNames, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    exact nomatch h

/-- A block whose records sit at input keys is no pinned basis block. -/
theorem basisPinHit_none_of_id {block : List (ConstantInfo .anon)}
    (hid : ∀ ci ∈ block, ∃ a, ci.name = .id a) : basisPinHit block = none := by
  have noMatch : ∀ kind ∈ [BasisKind.eqK, .natK, .punitK, .emptyK, .falseK],
      (kind.decls.map (·.name) == block.map (·.name)) = false := by
    intro kind member
    apply beq_eq_false_iff_ne.mpr
    intro same
    have hrole : ∃ s : Role, Key.role s ∈ (kind.decls (md := .anon)).map (·.name) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · exact ⟨.eq, by decide⟩
      · exact ⟨.nat, by decide⟩
      · exact ⟨.punit, by decide⟩
      · exact ⟨.empty, by decide⟩
      · exact ⟨.false, by decide⟩
    obtain ⟨s, hs⟩ := hrole
    rw [same] at hs
    obtain ⟨ci, hci, hname⟩ := List.mem_map.mp hs
    obtain ⟨a, ha⟩ := hid ci hci
    rw [ha] at hname
    exact nomatch hname
  unfold basisPinHit
  rw [List.find?_eq_none.mpr (fun kind member => by rw [noMatch kind member]; decide)]
  rfl

/-- **The front door of a constant at an input key whose declared type is already annotated**:
closed, without `let`, with resolving constants and a typing. -/
theorem front_of {env : Env .anon} {a : Address} {lps : List LevelParam}
    {ty stype : Expr .anon} {v : Level}
    (hfresh : env.find? (.id a) = none) (hnd : LevelParam.nodup lps = true)
    (hnl : noLetNoFvar ty = true) (hb : ty.looseBVarsBounded 0 = true)
    (hf : ty.hasFvar = false) (hlp : ty.allLevelParamsDefined lps = true)
    (hres : ty.constsResolve env = true)
    (hty : Infer env .full 0 ty stype) (hs : Red env 0 stype (.sort v)) :
    ConstantValRunJ rulesJ env ⟨.id a, lps, ty⟩ ty :=
  ⟨(by show (env.find? (.id a)).isNone = true; rw [hfresh]; rfl), reserved_id a, rfl, hnd, hb, hf,
    annot_of_annotates (annotates_refl_of_noLetNoFvar hnl) hf hb 0, hlp, hres, stype, v, hty,
    hs⟩

/-! ## The pinned `PUnit` basis -/

/-- The environment after the `PUnit` basis block. -/
def envP : Env .anon := ⟨[punitRecA, punitUnitA, punitA]⟩

theorem envP_run : DeclBasisRun Env.empty .punitK envP :=
  ⟨fun h => nomatch h, by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩

theorem envP_foldInv (V : Type u) [SetTheory V] : FoldInv V envP :=
  foldInv_step_basis envP_run V (foldInv_empty V)

theorem envP_pin : PUnitPin envP :=
  PUnitPin.of_stored (ciP := punitA) (ciU := punitUnitA) (p := uN) (q := uN)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem envP_roles : ∀ c ∈ envP.consts, keyIsRole c.name = true := by decide +kernel

theorem envP_find_id (a : Address) : envP.find? (.id a) = none := by
  cases h : envP.find? (.id a) with
  | none => rfl
  | some c =>
    have hr := envP_roles c (Env.find?_mem h)
    rw [Env.find?_name h] at hr
    exact nomatch hr

/-! ## Terms -/

/-- `Type`. -/
def tyType : Expr .anon := .sort (.succ .zero)

/-- `A → B`, at a codomain that is never a proposition. -/
def arrow (A B : Expr .anon) : Expr .anon := .forallE A B { pw := .never }

/-- A constant without level parameters. -/
def cst (n : Nat) : Expr .anon := .const (key n) []

/-! ## A two-type mutual block -/

/-- `A : Type`. -/
def fA : FormerRec := ⟨⟨key 0, [], tyType⟩, {}, tyType⟩

/-- `B : Type`. -/
def fB : FormerRec := ⟨⟨key 1, [], tyType⟩, {}, tyType⟩

/-- `A.mk : B → A`. -/
def cA : CtorRec := ⟨⟨key 2, [], arrow (cst 1) (cst 0)⟩, 0, 1, arrow (cst 1) (cst 0)⟩

/-- `B.mk : A → B`. -/
def cB : CtorRec := ⟨⟨key 3, [], arrow (cst 0) (cst 1)⟩, 0, 1, arrow (cst 0) (cst 1)⟩

/-- The block's records. -/
def mutualBlock : List (ConstantInfo .anon) :=
  [fA, fB].map (·.declared) ++ [cA, cB].map (·.declared)

theorem type_front {env : Env .anon} {n : Nat} (hfresh : env.find? (key n) = none) :
    ConstantValRunJ rulesJ env ⟨key n, [], tyType⟩ tyType :=
  front_of hfresh rfl rfl rfl rfl rfl rfl Infer.sort Red.refl

/-- A constant stored at type `Type` without level parameters has type `Type`. -/
theorem infer_cst {env : Env .anon} {n : Nat} {ci : ConstantInfo .anon} {d : Nat}
    (hf : env.find? (key n) = some ci) (ht : ci.isTowerEntry = false)
    (hl : ci.toConstantVal.levelParams = []) (hty : ci.toConstantVal.type = tyType) :
    Infer env .full d (cst n) tyType := by
  have h := Infer.const (env := env) (g := .full) (d := d) (us := []) hf ht (by rw [hl])
  rw [hl, hty] at h
  exact h

/-- `X → Y` is a type where `X` and `Y` are closed constants of type `Type`. -/
theorem infer_arrow {env : Env .anon} {m n : Nat}
    (hm : ∀ d, Infer env .full d (cst m) tyType) (hn : ∀ d, Infer env .full d (cst n) tyType) :
    Infer env .full 0 (arrow (cst m) (cst n)) (.sort (.imax (.succ .zero) (.succ .zero))) :=
  Infer.forallE (ty := cst m) (body := cst n) (s := tyType) (bs := tyType)
    (u := .succ .zero) (v := .succ .zero) (mb := { pw := .never })
    (hm 0) Red.refl (hn 1) Red.refl rfl

theorem stageAB_find_A : (stage envP [fA, fB]).find? (key 0) = some fA.stored :=
  stage_find (formers := [fA, fB]) (f := fA) (by simp [fA, fB]) (by simp)

theorem stageAB_find_B : (stage envP [fA, fB]).find? (key 1) = some fB.stored :=
  stage_find (formers := [fA, fB]) (f := fB) (by simp [fA, fB]) (by simp)

theorem stageAB_fresh {n : Nat} (h0 : n ≠ 0) (h1 : n ≠ 1) :
    (stage envP [fA, fB]).find? (key n) = none :=
  find?_append_none_of_not_mem (env := envP) (cs := [fB.stored, fA.stored])
    (by simp [fA, fB, FormerRec.stored, ConstantInfo.name, ConstantInfo.toConstantVal, h0, h1])
    (envP_find_id _)

theorem stageAB_A (d : Nat) : Infer (stage envP [fA, fB]) .full d (cst 0) tyType :=
  infer_cst stageAB_find_A rfl rfl rfl

theorem stageAB_B (d : Nat) : Infer (stage envP [fA, fB]) .full d (cst 1) tyType :=
  infer_cst stageAB_find_B rfl rfl rfl

/-- **The mutual block's checks.** -/
theorem mutual_block : PointBlock envP mutualBlock [fA, fB] [cA, cB] where
  members := fun ci => List.mem_append
  notPinned := basisPinHit_none_of_id (by
    intro ci hci
    simp only [mutualBlock, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hci
    rcases hci with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩)
  nodup := by simp [fA, fB, cA, cB]
  keyF := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact ⟨_, rfl⟩
  keyC := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact ⟨_, rfl⟩
  formerFront := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact type_front (envP_find_id _)
  formerAnnot := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact Annotates.sort
  formerSort := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact ⟨_, rfl⟩
  ctorFront := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact front_of (stageAB_fresh (by decide) (by decide)) rfl rfl rfl rfl
        (by simp [cA, cB, arrow, cst, Expr.allLevelParamsDefined])
        (by simp [cA, cB, arrow, cst, Expr.constsResolve, stageAB_find_A, stageAB_find_B])
        (infer_arrow stageAB_B stageAB_A) Red.refl
    · exact front_of (stageAB_fresh (by decide) (by decide)) rfl rfl rfl rfl
        (by simp [cA, cB, arrow, cst, Expr.allLevelParamsDefined])
        (by simp [cA, cB, arrow, cst, Expr.constsResolve, stageAB_find_A, stageAB_find_B])
        (infer_arrow stageAB_A stageAB_B) Red.refl
  ctorAnnot := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact annotates_refl_of_noLetNoFvar rfl
  ctorResult := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨fA, by simp, [], rfl, rfl⟩
    · exact ⟨fB, by simp, [], rfl, rfl⟩
  pin := envP_pin

/-- **The mutual block installs over the pinned basis and the fold's invariant holds at the
result**, in every set theory. -/
theorem mutual_installs :
    InstallStep envP (.indDecl mutualBlock 0) (installed envP [fA, fB] [cA, cB]) ∧
      ∀ (V : Type u) [SetTheory V], FoldInv V (installed envP [fA, fB] [cA, cB]) :=
  ⟨mutual_block.installStep 0, fun V _ => mutual_block.foldInv V (envP_foldInv V)⟩

/-- The installed mutual block has a model in every set theory. -/
theorem mutual_model (V : Type u) [SetTheory V] :
    EnvModelOk V .verified (installed envP [fA, fB] [cA, cB]) :=
  foldInv_envModelOk V _ (mutual_installs.2 V)

/-! ## A block with a parameter -/

/-- `Type → Type`. -/
def tyW : Expr .anon := arrow tyType tyType

/-- `(α : Type) → α → W α`, with `W` at `key 4`. -/
def tyWmk : Expr .anon :=
  .forallE tyType (.forallE (.bvar 0) (.app (cst 4) (.bvar 1)) { pw := .never })
    { pw := .never }

/-- `W : Type → Type`. -/
def fW : FormerRec := ⟨⟨key 4, [], tyW⟩, {}, tyW⟩

/-- `W.mk : (α : Type) → α → W α`. -/
def cW : CtorRec := ⟨⟨key 5, [], tyWmk⟩, 1, 1, tyWmk⟩

/-- The block's records. -/
def paramBlock : List (ConstantInfo .anon) := [fW].map (·.declared) ++ [cW].map (·.declared)

theorem infer_tyW {env : Env .anon} :
    Infer env .full 0 tyW (.sort (.imax (.succ (.succ .zero)) (.succ (.succ .zero)))) :=
  Infer.forallE (ty := tyType) (body := tyType) (s := .sort (.succ (.succ .zero)))
    (bs := .sort (.succ (.succ .zero))) (u := .succ (.succ .zero)) (v := .succ (.succ .zero))
    (mb := { pw := .never }) Infer.sort Red.refl Infer.sort Red.refl rfl

theorem stageW_find : (stage envP [fW]).find? (key 4) = some fW.stored :=
  stage_find (formers := [fW]) (f := fW) (by simp [fW]) (by simp)

theorem stageW_fresh {n : Nat} (h : n ≠ 4) : (stage envP [fW]).find? (key n) = none :=
  find?_append_none_of_not_mem (env := envP) (cs := [fW.stored])
    (by simp [fW, FormerRec.stored, ConstantInfo.name, ConstantInfo.toConstantVal, h])
    (envP_find_id _)

/-- `W x : Type` for a variable `x : Type`, where `W` is stored at type `Type → Type`. -/
theorem infer_W_app {env : Env .anon} {ci : ConstantInfo .anon} {d i : Nat} (hi : i < d)
    (hf : env.find? (key 4) = some ci) (ht : ci.isTowerEntry = false)
    (hl : ci.toConstantVal.levelParams = []) (hty : ci.toConstantVal.type = tyW) :
    Infer env .full d (.app (cst 4) (.fvar i tyType)) tyType := by
  have hW : Infer env .full d (cst 4) (tyW.instantiateLevelParams [] []) := by
    have h := Infer.const (env := env) (g := .full) (d := d) (us := []) hf ht (by rw [hl])
    rw [hl, hty] at h
    exact h
  exact Infer.app (f := cst 4) (a := .fvar i tyType) (ty := tyType) (body := tyType)
    (ta := tyType) (mt := { pw := Level.substPW [] [] PropWhen.never }) hW Red.refl
    (Infer.fvar hi) DefEq.refl

theorem infer_tyWmk {env : Env .anon} {ci : ConstantInfo .anon}
    (hf : env.find? (key 4) = some ci) (ht : ci.isTowerEntry = false)
    (hl : ci.toConstantVal.levelParams = []) (hty : ci.toConstantVal.type = tyW) :
    Infer env .full 0 tyWmk
      (.sort (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero)))) := by
  have hinner : Infer env .full 1
      (.forallE (.fvar 0 tyType) (.app (cst 4) (.fvar 0 tyType)) { pw := .never })
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
    Infer.forallE (ty := .fvar 0 tyType) (body := .app (cst 4) (.fvar 0 tyType))
      (s := tyType) (bs := tyType) (u := .succ .zero) (v := .succ .zero)
      (mb := { pw := .never }) (Infer.fvar (by decide)) Red.refl
      (infer_W_app (by decide) hf ht hl hty) Red.refl rfl
  exact Infer.forallE (ty := tyType)
    (body := .forallE (.bvar 0) (.app (cst 4) (.bvar 1)) { pw := .never })
    (s := .sort (.succ (.succ .zero))) (bs := .sort (.imax (.succ .zero) (.succ .zero)))
    (u := .succ (.succ .zero)) (v := .imax (.succ .zero) (.succ .zero))
    (mb := { pw := .never }) Infer.sort Red.refl hinner Red.refl rfl

/-- **The parametric block's checks.** -/
theorem param_block : PointBlock envP paramBlock [fW] [cW] where
  members := fun ci => List.mem_append
  notPinned := basisPinHit_none_of_id (by
    intro ci hci
    simp only [paramBlock, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hci
    rcases hci with rfl | rfl <;> exact ⟨_, rfl⟩)
  nodup := by simp [fW, cW]
  keyF := by
    intro f hf
    obtain rfl := List.mem_singleton.mp hf
    exact ⟨_, rfl⟩
  keyC := by
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact ⟨_, rfl⟩
  formerFront := by
    intro f hf
    obtain rfl := List.mem_singleton.mp hf
    exact front_of (envP_find_id _) rfl rfl rfl rfl
      (by simp [fW, tyW, arrow, tyType, Expr.allLevelParamsDefined, Level.allParamsDefined])
      rfl infer_tyW Red.refl
  formerAnnot := by
    intro f hf
    obtain rfl := List.mem_singleton.mp hf
    exact annotates_refl_of_noLetNoFvar rfl
  formerSort := by
    intro f hf
    obtain rfl := List.mem_singleton.mp hf
    exact ⟨_, rfl⟩
  ctorFront := by
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact front_of (stageW_fresh (by decide)) rfl rfl (by decide) rfl
      (by simp [cW, tyWmk, cst, tyType, Expr.allLevelParamsDefined, Level.allParamsDefined])
      (by simp [cW, tyWmk, cst, tyType, Expr.constsResolve, stageW_find])
      (infer_tyWmk stageW_find rfl rfl rfl) Red.refl
  ctorAnnot := by
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact annotates_refl_of_noLetNoFvar rfl
  ctorResult := by
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact ⟨fW, by simp, [], rfl, rfl⟩
  pin := envP_pin

/-- The environment with `W` and `W.mk` installed. -/
def envW : Env .anon := installed envP [fW] [cW]

theorem envW_foldInv (V : Type u) [SetTheory V] : FoldInv V envW :=
  param_block.foldInv V (envP_foldInv V)

theorem envW_pin : PUnitPin envW := envP_pin.mono param_block.envExt

/-! ## A nested-shaped block over `W` -/

/-- `T : Type`. -/
def fT : FormerRec := ⟨⟨key 6, [], tyType⟩, {}, tyType⟩

/-- `W T → T`. -/
def tyTmk : Expr .anon := arrow (.app (cst 4) (cst 6)) (cst 6)

/-- `T.mk : W T → T`: a field whose type applies the earlier-installed `W` to the block's own
type. -/
def cT : CtorRec := ⟨⟨key 7, [], tyTmk⟩, 0, 1, tyTmk⟩

/-- The block's records. -/
def nestedBlock : List (ConstantInfo .anon) := [fT].map (·.declared) ++ [cT].map (·.declared)

theorem envW_find_W : envW.find? (key 4) = some fW.stored :=
  param_block.find_former (f := fW) (by simp)

theorem envW_fresh {n : Nat} (h4 : n ≠ 4) (h5 : n ≠ 5) : envW.find? (key n) = none := by
  show (installed envP [fW] [cW]).find? (key n) = none
  rw [installed_eq]
  exact find?_append_none_of_not_mem (env := envP) (cs := newConsts [fW] [cW])
    (by simp [newConsts, fW, cW, FormerRec.stored, CtorRec.stored, ConstantInfo.name,
      ConstantInfo.toConstantVal, h4, h5])
    (envP_find_id _)

theorem stageT_find_T : (stage envW [fT]).find? (key 6) = some fT.stored :=
  stage_find (formers := [fT]) (f := fT) (by simp [fT]) (by simp)

theorem stageT_find_W : (stage envW [fT]).find? (key 4) = some fW.stored := by
  show Env.find? ⟨fT.stored :: envW.consts⟩ (key 4) = some fW.stored
  rw [EnvExt.find?_cons_ne (c := fT.stored) (k := key 4)
    (by simp [fT, FormerRec.stored, ConstantInfo.name, ConstantInfo.toConstantVal])]
  exact envW_find_W

theorem stageT_fresh : (stage envW [fT]).find? (key 7) = none := by
  show Env.find? ⟨fT.stored :: envW.consts⟩ (key 7) = none
  rw [EnvExt.find?_cons_ne (c := fT.stored) (k := key 7)
    (by simp [fT, FormerRec.stored, ConstantInfo.name, ConstantInfo.toConstantVal])]
  exact envW_fresh (by decide) (by decide)

theorem stageT_T (d : Nat) : Infer (stage envW [fT]) .full d (cst 6) tyType :=
  infer_cst stageT_find_T rfl rfl rfl

/-- `W T : Type` at the staged environment. -/
theorem stageT_WT : Infer (stage envW [fT]) .full 0 (.app (cst 4) (cst 6)) tyType := by
  have hW : Infer (stage envW [fT]) .full 0 (cst 4) (tyW.instantiateLevelParams [] []) := by
    have h := Infer.const (env := stage envW [fT]) (g := .full) (d := 0) (us := [])
      stageT_find_W rfl rfl
    exact h
  exact Infer.app (f := cst 4) (a := cst 6) (ty := tyType) (body := tyType) (ta := tyType)
    (mt := { pw := Level.substPW [] [] PropWhen.never }) hW Red.refl (stageT_T 0) DefEq.refl

theorem infer_tyTmk :
    Infer (stage envW [fT]) .full 0 tyTmk (.sort (.imax (.succ .zero) (.succ .zero))) :=
  Infer.forallE (ty := .app (cst 4) (cst 6)) (body := cst 6) (s := tyType) (bs := tyType)
    (u := .succ .zero) (v := .succ .zero) (mb := { pw := .never })
    stageT_WT Red.refl (stageT_T 1) Red.refl rfl

/-- **The nested-shaped block's checks**, over the environment that stores `W`. -/
theorem nested_block : PointBlock envW nestedBlock [fT] [cT] where
  members := fun ci => List.mem_append
  notPinned := basisPinHit_none_of_id (by
    intro ci hci
    simp only [nestedBlock, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hci
    rcases hci with rfl | rfl <;> exact ⟨_, rfl⟩)
  nodup := by simp [fT, cT]
  keyF := by
    intro f hf
    obtain rfl := List.mem_singleton.mp hf
    exact ⟨_, rfl⟩
  keyC := by
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact ⟨_, rfl⟩
  formerFront := by
    intro f hf
    obtain rfl := List.mem_singleton.mp hf
    exact type_front (envW_fresh (by decide) (by decide))
  formerAnnot := by
    intro f hf
    obtain rfl := List.mem_singleton.mp hf
    exact Annotates.sort
  formerSort := by
    intro f hf
    obtain rfl := List.mem_singleton.mp hf
    exact ⟨_, rfl⟩
  ctorFront := by
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact front_of stageT_fresh rfl rfl rfl rfl
      (by simp [cT, tyTmk, arrow, cst, Expr.allLevelParamsDefined])
      (by simp [cT, tyTmk, arrow, cst, Expr.constsResolve, stageT_find_T, stageT_find_W])
      infer_tyTmk Red.refl
  ctorAnnot := by
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact annotates_refl_of_noLetNoFvar rfl
  ctorResult := by
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact ⟨fT, by simp, [], rfl, rfl⟩
  pin := envW_pin

/-- **The nested-shaped block installs over the environment that stores `W`, and the fold's
invariant holds at the result**, in every set theory. Two constructors-only installs in a row:
the parametric block, then the block whose constructor mentions it. -/
theorem nested_installs :
    InstallStep envP (.indDecl paramBlock 1) envW ∧
      InstallStep envW (.indDecl nestedBlock 0) (installed envW [fT] [cT]) ∧
      ∀ (V : Type u) [SetTheory V], FoldInv V (installed envW [fT] [cT]) :=
  ⟨param_block.installStep 1, nested_block.installStep 0,
    fun V _ => nested_block.foldInv V (envW_foldInv V)⟩

/-- The installed nested-shaped block has a model in every set theory. -/
theorem nested_model (V : Type u) [SetTheory V] :
    EnvModelOk V .verified (installed envW [fT] [cT]) :=
  foldInv_envModelOk V _ (nested_installs.2.2 V)

/-- At the installed nested-shaped block, `T` carries no capability and no projection table is
stored for it. -/
theorem nested_inert {cvT : ConstantVal .anon} {caps : IndCaps .anon}
    (h : (installed envW [fT] [cT]).find? (key 6) = some (.indInfo cvT caps)) :
    caps.eta = false ∧ caps.unitlike = false ∧ caps.etaCtor = none ∧ caps.ruleK = false :=
  nested_block.former_caps (f := fT) (by simp) h

end IxVM.Refinement.Decl.Point.Examples
