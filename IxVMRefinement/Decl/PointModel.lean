import IxVMRefinement.Decl.PointModelLeaf
import IxVMRefinement.Decl.DeclSpecs
import IxVMRefinement.Decl.PrefixLoads
import IxC.Kernel.Model.NoRecBlock
import IxC.Kernel.Semantics.Inductives.DeclRecTwinExtJ

/-! # A constructors-only install of a mutual or nested inductive block

A block of inductive types whose recursors no declaration of the run uses is installed with
its types and constructors only: every type at the empty capability record, no recursor, no
projection table. `Ix.Kernel.Model` then asks only that each constant inhabit its type, and the
one-point interpretation (`Decl/PointModelLeaf.lean`) gives that with no positivity or universe
condition.

* `PointBlock` is the interface: the judgement-level facts a refinement of the circuit's check
  of the block's inductive and constructor records supplies, at the environments that check
  types them (the formers at the prefix, the constructors with the block's formers stored).
* `pointBlock_install` is the conditional theorem: the block installs into
  `installed env formers ctors`, the prefix with exactly the block's types and constructors in
  front (`InstallStep`), and the fold's invariant is kept in every set theory
  (`FoldInv`, `FullDeclInv`). No auxiliary constant is stored.
* The last section states what the stored block does not support: no recursor, no rule of a
  native or basis recursor at its constructors, no projection table, no η or unit-like
  capability.
-/

namespace IxVM.Refinement.Decl.Point

open Ix.Kernel
open Ix.Kernel.Semantics
open Ix.Kernel.Model
open Ix.Kernel.Rules (Red DefEq Infer Grade)
open IxVM.Refinement.Core (Ctx)
open IxVM.Consistency (StoredAs ValStored InstallStep Annotates)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

/-! ## The records of a block -/

/-- **A type former as checked**: the declared constant, the capability record its declaration
carries (not read: the former is stored at the empty one), and the annotation of its type. -/
structure FormerRec where
  cv : ConstantVal .anon
  caps : IndCaps .anon
  type' : Expr .anon

/-- **A constructor as checked**: the declared constant with its parameter and field counts,
and the annotation of its type. -/
structure CtorRec where
  cv : ConstantVal .anon
  nP : Nat
  nF : Nat
  type' : Expr .anon

/-- The former as its declaration states it. -/
def FormerRec.declared (f : FormerRec) : ConstantInfo .anon := .indInfo f.cv f.caps

/-- The former as stored: its annotated type, the empty capability record. -/
def FormerRec.stored (f : FormerRec) : ConstantInfo .anon :=
  .indInfo ⟨f.cv.name, f.cv.levelParams, f.type'⟩ {}

/-- The constructor as its declaration states it. -/
def CtorRec.declared (c : CtorRec) : ConstantInfo .anon := .ctorInfo c.cv c.nP c.nF

/-- The constructor as stored: its annotated type, its declared counts. -/
def CtorRec.stored (c : CtorRec) : ConstantInfo .anon :=
  .ctorInfo ⟨c.cv.name, c.cv.levelParams, c.type'⟩ c.nP c.nF

/-- **The staged environment**: the prefix with the block's formers stored. The constructor
types are typed here. -/
def stage (env : Env .anon) (formers : List FormerRec) : Env .anon :=
  ⟨(formers.map (·.stored)).reverse ++ env.consts⟩

/-- **The installed environment**: the staged one with the block's constructors stored. -/
def installed (env : Env .anon) (formers : List FormerRec) (ctors : List CtorRec) : Env .anon :=
  ⟨(ctors.map (·.stored)).reverse ++ (stage env formers).consts⟩

/-- The constants the install adds, newest first. -/
def newConsts (formers : List FormerRec) (ctors : List CtorRec) : List (ConstantInfo .anon) :=
  (ctors.map (·.stored)).reverse ++ (formers.map (·.stored)).reverse

theorem installed_eq (env : Env .anon) (formers : List FormerRec) (ctors : List CtorRec) :
    installed env formers ctors = ⟨newConsts formers ctors ++ env.consts⟩ := by
  unfold installed stage newConsts
  rw [List.append_assoc]

theorem map_formerStored_names :
    ∀ (fs : List FormerRec), (fs.map (·.stored)).map (·.name) = fs.map (·.cv.name)
  | [] => rfl
  | f :: fs => congrArg (f.cv.name :: ·) (map_formerStored_names fs)

theorem map_ctorStored_names :
    ∀ (cs : List CtorRec), (cs.map (·.stored)).map (·.name) = cs.map (·.cv.name)
  | [] => rfl
  | c :: cs => congrArg (c.cv.name :: ·) (map_ctorStored_names cs)

theorem newConsts_names (formers : List FormerRec) (ctors : List CtorRec) :
    (newConsts formers ctors).map (·.name) =
      (formers.map (·.cv.name) ++ ctors.map (·.cv.name)).reverse := by
  unfold newConsts
  rw [List.map_append, List.map_reverse, List.map_reverse, map_formerStored_names,
    map_ctorStored_names, List.reverse_append]

/-! ## The interface -/

/-- **What the check of a constructors-only block establishes.** The fields are judgement-level
facts over derivations (`rulesJ`), each with the circuit check expected to supply it:
* `members`: the declaration's records are the listed formers and constructors (the reader's
  block);

* `nodup`, `keyF`, `keyC`: the members' keys are distinct input keys (an address the role table
  binds to no role). **No block-arm check gives the input-key half**: it is the table's
  validity, which pins the basis roles to prelude records;
* `formerFront`: each former's front door at the prefix (`ConstantValRunJ`: fresh, not
  reserved, not a projection-function shape, distinct level parameters, closed type, an
  annotation whose constants resolve and that is a type): `validate_expr_well_scoped`,
  `expr_mentions_block = 0` and `k_ensure_sort` on the inductive record;
* `formerAnnot`, `ctorAnnot`: the stored types annotate the declared ones (the term
  representation of the loaded record);
* `formerSort`: the annotated type is a syntactic telescope into a sort. **The circuit's
  `get_result_sort_level` reduces to weak head normal form before each binder**, so it gives
  this only where that reduction is the identity;
* `ctorFront`: each constructor's front door at the staged environment:
  `validate_expr_well_scoped` and `k_ensure_sort` on the constructor record, typed with the
  block's formers loadable;
* `ctorResult`: the annotated type is a syntactic telescope ending in a former of the block
  applied to as many arguments as that former's type has binders: `check_ctor_return_type`
  (head a member of the block, `n_params + n_indices` arguments) with the former's binder
  count;
* `pin`: the kernel's `PUnit` pin is stored in the prefix.

Nothing is asked about positivity, field universes or parameter agreement. -/
structure PointBlock (env : Env .anon) (block : List (ConstantInfo .anon))
    (formers : List FormerRec) (ctors : List CtorRec) : Prop where
  members : ∀ ci, ci ∈ block ↔
    ci ∈ formers.map (·.declared) ∨ ci ∈ ctors.map (·.declared)
  nodup : (formers.map (·.cv.name) ++ ctors.map (·.cv.name)).Nodup
  keyF : ∀ f ∈ formers, ∃ a, f.cv.name = .id a
  keyC : ∀ c ∈ ctors, ∃ a, c.cv.name = .id a
  formerFront : ∀ f ∈ formers, ConstantValRunJ rulesJ env f.cv f.type'
  formerAnnot : ∀ f ∈ formers, Annotates f.type' f.cv.type
  formerSort : ∀ f ∈ formers, ∃ l, f.type'.resultSort = some l
  ctorFront : ∀ c ∈ ctors, ConstantValRunJ rulesJ (stage env formers) c.cv c.type'
  ctorAnnot : ∀ c ∈ ctors, Annotates c.type' c.cv.type
  ctorResult : ∀ c ∈ ctors, ∃ f ∈ formers, ∃ us,
    EndsHead f.cv.name us f.type'.piArity c.type'
  pin : PUnitPin env

/-! ## From the staged checks to a run -/

/-- **A front door moves along an environment extension** that keeps the name fresh. -/
theorem constantValRunJ_weaken {env env' : Env .anon} (hx : EnvExt env env')
    {cv : ConstantVal .anon} {type' : Expr .anon} (hfresh : env'.find? cv.name = none)
    (h : ConstantValRunJ rulesJ env cv type') : ConstantValRunJ rulesJ env' cv type' := by
  obtain ⟨-, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr, stype, u, hst, hens⟩ := h
  refine ⟨by rw [hfresh]; rfl, hnres, hpshape, hnd, hlbt, hitf, hann, htp, ?_, stype, u, ?_, ?_⟩
  · exact Expr.constsResolve_le (fun n hn => isSome_of_envExt hx hn) htr
  · exact Infer.weaken hx hst
  · exact Red.weaken hx hens

theorem PointRun.append {F : List (Key .anon)} :
    ∀ (xs : List (ConstantInfo .anon)) {ys : List (ConstantInfo .anon)} {e e₁ e₂ : Env .anon},
      PointRun F e xs e₁ → PointRun F e₁ ys e₂ → PointRun F e (xs ++ ys) e₂
  | [], ys, e, e₁, e₂, h1, h2 => by
    have h : e₁ = e := h1
    subst h
    exact h2
  | x :: xs, ys, e, e₁, e₂, h1, h2 => by
    obtain ⟨ciA, hm, h1'⟩ := h1
    exact ⟨ciA, hm, PointRun.append xs h1' h2⟩

/-- The formers, each typed at `base`, run at any extension that stores none of them. -/
theorem formers_run (F : List (Key .anon)) {base : Env .anon} :
    ∀ (fs : List FormerRec) (env : Env .anon), EnvExt base env →
      (∀ f ∈ fs, ConstantValRunJ rulesJ base f.cv f.type' ∧ (∃ a, f.cv.name = .id a) ∧
        ∃ l, f.type'.resultSort = some l) →
      (fs.map (·.cv.name)).Nodup → (∀ f ∈ fs, env.find? f.cv.name = none) →
      PointRun F env (fs.map (·.declared)) (stage env fs) ∧ EnvExt base (stage env fs)
  | [], env, hx, _, _, _ => ⟨rfl, hx⟩
  | f :: rest, env, hx, hfacts, hnd, hfresh => by
    obtain ⟨hfront, hid, l, hl⟩ := hfacts f List.mem_cons_self
    have hfr : env.find? f.cv.name = none := hfresh f List.mem_cons_self
    have hnd' : f.cv.name ∉ rest.map (·.cv.name) ∧ (rest.map (·.cv.name)).Nodup :=
      List.nodup_cons.mp hnd
    have hx' : EnvExt env ⟨f.stored :: env.consts⟩ :=
      EnvExt.cons hfr (fun _ => id_ne_projTableName hid _)
    have hfresh' : ∀ g ∈ rest,
        (⟨f.stored :: env.consts⟩ : Env .anon).find? g.cv.name = none := by
      intro g hg
      have hne : f.stored.name ≠ g.cv.name :=
        fun e => hnd'.1 (List.mem_map.mpr ⟨g, hg, e.symm⟩)
      rw [EnvExt.find?_cons_ne hne]
      exact hfresh g (List.mem_cons_of_mem _ hg)
    obtain ⟨hrun, hxr⟩ := formers_run F rest ⟨f.stored :: env.consts⟩ (hx.trans hx')
      (fun g hg => hfacts g (List.mem_cons_of_mem _ hg)) hnd'.2 hfresh'
    have hst : stage env (f :: rest) = stage ⟨f.stored :: env.consts⟩ rest := by
      simp [stage, List.reverse_cons, List.append_assoc]
    rw [hst]
    exact ⟨⟨f.stored, ⟨f.type', constantValRunJ_weaken hx hfr hfront, hid, rfl, l, hl⟩, hrun⟩,
      hxr⟩

/-- The constructors, each typed at `base` with its result a former `base` stores, run at any
extension that stores none of them. -/
theorem ctors_run (F : List (Key .anon)) {base : Env .anon} :
    ∀ (cs : List CtorRec) (env : Env .anon), EnvExt base env →
      (∀ c ∈ cs, ConstantValRunJ rulesJ base c.cv c.type' ∧ (∃ a, c.cv.name = .id a) ∧
        ∃ (T : Key .anon) (us : List Level) (cvT : ConstantVal .anon) (caps : IndCaps .anon),
          T ∈ F ∧ base.find? T = some (.indInfo cvT caps) ∧
          EndsHead T us cvT.type.piArity c.type') →
      (cs.map (·.cv.name)).Nodup → (∀ c ∈ cs, env.find? c.cv.name = none) →
      PointRun F env (cs.map (·.declared)) ⟨(cs.map (·.stored)).reverse ++ env.consts⟩
  | [], env, _, _, _, _ => rfl
  | c :: rest, env, hx, hfacts, hnd, hfresh => by
    obtain ⟨hfront, hid, T, us, cvT, caps, hT, hfT, hends⟩ := hfacts c List.mem_cons_self
    have hfr : env.find? c.cv.name = none := hfresh c List.mem_cons_self
    have hnd' : c.cv.name ∉ rest.map (·.cv.name) ∧ (rest.map (·.cv.name)).Nodup :=
      List.nodup_cons.mp hnd
    have hx' : EnvExt env ⟨c.stored :: env.consts⟩ :=
      EnvExt.cons hfr (fun _ => id_ne_projTableName hid _)
    have hfresh' : ∀ g ∈ rest,
        (⟨c.stored :: env.consts⟩ : Env .anon).find? g.cv.name = none := by
      intro g hg
      have hne : c.stored.name ≠ g.cv.name :=
        fun e => hnd'.1 (List.mem_map.mpr ⟨g, hg, e.symm⟩)
      rw [EnvExt.find?_cons_ne hne]
      exact hfresh g (List.mem_cons_of_mem _ hg)
    have hrun := ctors_run F rest ⟨c.stored :: env.consts⟩ (hx.trans hx')
      (fun g hg => hfacts g (List.mem_cons_of_mem _ hg)) hnd'.2 hfresh'
    have hst : (⟨((c :: rest).map (·.stored)).reverse ++ env.consts⟩ : Env .anon) =
        ⟨(rest.map (·.stored)).reverse ++ (c.stored :: env.consts)⟩ := by
      simp [List.reverse_cons, List.append_assoc]
    rw [hst]
    exact ⟨c.stored, ⟨c.type', constantValRunJ_weaken hx hfr hfront, hid, rfl, T, us, cvT,
      caps, hT, hx.find hfT, hends⟩, hrun⟩

/-- **A block whose records sit at input keys is no pinned basis block**: a pinned block's
names are role keys. -/
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

theorem stage_find {env : Env .anon} {formers : List FormerRec}
    (hnd : (formers.map (·.cv.name)).Nodup) {f : FormerRec} (hf : f ∈ formers) :
    (stage env formers).find? f.cv.name = some f.stored := by
  have hnd' : (((formers.map (·.stored)).reverse).map (·.name)).Nodup := by
    rw [List.map_reverse, map_formerStored_names]
    exact List.nodup_reverse.mpr hnd
  exact find?_mem_of_nodup (rest := env.consts) hnd'
    (List.mem_reverse.mpr (List.mem_map_of_mem hf))

section Block

variable {env : Env .anon} {block : List (ConstantInfo .anon)} {formers : List FormerRec}
  {ctors : List CtorRec}

theorem PointBlock.nodupF (hb : PointBlock env block formers ctors) :
    (formers.map (·.cv.name)).Nodup :=
  (List.nodup_append.mp hb.nodup).1

theorem PointBlock.nodupC (hb : PointBlock env block formers ctors) :
    (ctors.map (·.cv.name)).Nodup :=
  (List.nodup_append.mp hb.nodup).2.1

theorem PointBlock.freshF (hb : PointBlock env block formers ctors) :
    ∀ f ∈ formers, env.find? f.cv.name = none :=
  fun f hf => Option.isNone_iff_eq_none.mp (hb.formerFront f hf).1

theorem PointBlock.freshC (hb : PointBlock env block formers ctors) :
    ∀ c ∈ ctors, (stage env formers).find? c.cv.name = none :=
  fun c hc => Option.isNone_iff_eq_none.mp (hb.ctorFront c hc).1

/-- The block is no pinned basis block: its records sit at input keys. -/
theorem PointBlock.notPinned (hb : PointBlock env block formers ctors) :
    basisPinHit block = none :=
  basisPinHit_none_of_id (fun ci hci => by
    rcases (hb.members ci).mp hci with h | h
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp h
      exact hb.keyF f hf
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
      exact hb.keyC c hc)

/-- The formers' run and the extension to the staged environment. -/
theorem PointBlock.formersRun (hb : PointBlock env block formers ctors) :
    PointRun (formers.map (·.cv.name)) env (formers.map (·.declared)) (stage env formers) ∧
      EnvExt env (stage env formers) :=
  formers_run _ formers env (EnvExt.refl env)
    (fun f hf => ⟨hb.formerFront f hf, hb.keyF f hf, hb.formerSort f hf⟩) hb.nodupF hb.freshF

/-- **The block's run**: the formers in order, then the constructors in order. -/
theorem PointBlock.run (hb : PointBlock env block formers ctors) :
    PointRun (formers.map (·.cv.name)) env
      (formers.map (·.declared) ++ ctors.map (·.declared)) (installed env formers ctors) := by
  refine PointRun.append _ hb.formersRun.1 ?_
  exact ctors_run _ ctors (stage env formers) (EnvExt.refl _)
    (fun c hc => by
      obtain ⟨f, hf, us, hends⟩ := hb.ctorResult c hc
      exact ⟨hb.ctorFront c hc, hb.keyC c hc, f.cv.name, us,
        ⟨f.cv.name, f.cv.levelParams, f.type'⟩, {}, List.mem_map_of_mem hf,
        stage_find hb.nodupF hf, hends⟩)
    hb.nodupC hb.freshC

/-- The added constants are fresh, with distinct keys. -/
theorem PointBlock.freshChain (hb : PointBlock env block formers ctors) :
    FreshChain env (newConsts formers ctors) (installed env formers ctors) where
  eq := installed_eq env formers ctors
  nodup := by
    rw [newConsts_names]
    exact List.nodup_reverse.mpr hb.nodup
  fresh := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
      have hfr := hb.freshC r hr
      cases h : env.find? r.cv.name with
      | none => exact h
      | some x =>
        have := hb.formersRun.2.find h
        rw [hfr] at this
        exact nomatch this
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
      exact hb.freshF r hr

theorem PointBlock.mem_new_former (hb : PointBlock env block formers ctors) {f : FormerRec}
    (hf : f ∈ formers) : f.stored ∈ newConsts formers ctors :=
  List.mem_append_right _ (List.mem_reverse.mpr (List.mem_map_of_mem hf))

theorem PointBlock.mem_new_ctor (hb : PointBlock env block formers ctors) {c : CtorRec}
    (hc : c ∈ ctors) : c.stored ∈ newConsts formers ctors :=
  List.mem_append_left _ (List.mem_reverse.mpr (List.mem_map_of_mem hc))

/-- A stored member is found at its key. -/
theorem PointBlock.find_new (hb : PointBlock env block formers ctors) {x : ConstantInfo .anon}
    (hx : x ∈ newConsts formers ctors) : (installed env formers ctors).find? x.name = some x := by
  rw [installed_eq]
  exact find?_mem_of_nodup (rest := env.consts) hb.freshChain.nodup hx

/-- **Every former is stored at the empty capability record with its annotated type.** -/
theorem PointBlock.find_former (hb : PointBlock env block formers ctors) {f : FormerRec}
    (hf : f ∈ formers) : (installed env formers ctors).find? f.cv.name = some f.stored :=
  hb.find_new (hb.mem_new_former hf)

/-- **Every constructor is stored with its declared counts and its annotated type.** -/
theorem PointBlock.find_ctor (hb : PointBlock env block formers ctors) {c : CtorRec}
    (hc : c ∈ ctors) : (installed env formers ctors).find? c.cv.name = some c.stored :=
  hb.find_new (hb.mem_new_ctor hc)

/-- **Every record of the block is stored as declared.** -/
theorem PointBlock.stored (hb : PointBlock env block formers ctors) :
    ∀ ci₀ ∈ block, ∃ ci, (installed env formers ctors).find? ci₀.name = some ci ∧
      StoredAs ci ci₀ := by
  intro ci₀ hci₀
  rcases (hb.members ci₀).mp hci₀ with h | h
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp h
    exact ⟨f.stored, hb.find_former hf, ⟨rfl, rfl, hb.formerAnnot f hf⟩, trivial⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    exact ⟨c.stored, hb.find_ctor hc, ⟨rfl, rfl, hb.ctorAnnot c hc⟩, rfl, rfl⟩

/-- Every added constant is a former's or a constructor's stored form. -/
theorem PointBlock.new_cases (hb : PointBlock env block formers ctors) {x : ConstantInfo .anon}
    (hx : x ∈ newConsts formers ctors) :
    (∃ f ∈ formers, x = f.stored) ∨ ∃ c ∈ ctors, x = c.stored := by
  rcases List.mem_append.mp hx with h | h
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp h)
    exact Or.inr ⟨c, hc, rfl⟩
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp h)
    exact Or.inl ⟨f, hf, rfl⟩

/-- Every added constant sits at an input key. -/
theorem PointBlock.new_id (hb : PointBlock env block formers ctors) {x : ConstantInfo .anon}
    (hx : x ∈ newConsts formers ctors) : ∃ a, x.name = .id a := by
  rcases hb.new_cases hx with ⟨f, hf, rfl⟩ | ⟨c, hc, rfl⟩
  · exact hb.keyF f hf
  · exact hb.keyC c hc

/-- **The install, by shape**: the block's records, stored as declared, in front of the prefix,
and nothing else. -/
theorem PointBlock.installStep (hb : PointBlock env block formers ctors) (nP : Nat) :
    InstallStep env (.indDecl block nP) (installed env formers ctors) := by
  have hinst : IxVM.Consistency.installs (.indDecl block nP) = block := by
    simp [IxVM.Consistency.installs, hb.notPinned]
  refine installStep_glue_of_freshChain hb.freshChain ?_ ?_ ?_
  · intro x hx
    left
    rw [hinst]
    rcases hb.new_cases hx with ⟨f, hf, rfl⟩ | ⟨c, hc, rfl⟩
    · exact ⟨f.declared, (hb.members _).mpr (Or.inl (List.mem_map_of_mem hf)), rfl⟩
    · exact ⟨c.declared, (hb.members _).mpr (Or.inr (List.mem_map_of_mem hc)), rfl⟩
  · intro ci₀ hci₀
    rw [hinst] at hci₀
    rcases (hb.members ci₀).mp hci₀ with h | h
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp h
      exact List.mem_map_of_mem (f := (·.name)) (hb.mem_new_former hf)
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
      exact List.mem_map_of_mem (f := (·.name)) (hb.mem_new_ctor hc)
  · intro ci₀ hci₀
    rw [hinst] at hci₀
    exact hb.stored ci₀ hci₀

end Block

/-! ## The store invariant along a run -/

/-- A member is stored as an inductive at the empty capability record or as a constructor, at
its declared name and level parameters and its annotated type. -/
theorem PointMember.kind {F : List (Key .anon)} {env : Env .anon} {ci ciA : ConstantInfo .anon}
    (h : PointMember F env ci ciA) :
    ∃ type', ConstantValRunJ rulesJ env ci.toConstantVal type' ∧ (∃ a, ci.name = .id a) ∧
      (ciA = .indInfo ⟨ci.toConstantVal.name, ci.toConstantVal.levelParams, type'⟩ {} ∨
        ∃ nP nF, ciA =
          .ctorInfo ⟨ci.toConstantVal.name, ci.toConstantVal.levelParams, type'⟩ nP nF) := by
  obtain ⟨type', hcv, hid, hk⟩ := h
  refine ⟨type', hcv, hid, ?_⟩
  cases ci with
  | indInfo cv caps => exact Or.inl hk.1
  | ctorInfo cv nP nF => exact Or.inr ⟨nP, nF, hk.1⟩
  | axiomInfo _ => exact False.elim hk
  | defnInfo _ _ _ => exact False.elim hk
  | thmInfo _ _ => exact False.elim hk
  | recInfo _ _ _ _ => exact False.elim hk
  | projInfo _ => exact False.elim hk

/-- **One member keeps the fold's store invariant**: it is a fresh typed constant that is no
theorem, recursor or projection table, and no η-capable former. -/
theorem foldStoreInv_member {F : List (Key .anon)} {env : Env .anon}
    {ci ciA : ConstantInfo .anon} (h : FoldStoreInv env) (hm : PointMember F env ci ciA) :
    FoldStoreInv ⟨ciA :: env.consts⟩ := by
  obtain ⟨type', hcv, hid, hkind⟩ := hm.kind
  have hty := typeFacts_of_runJ (judgeFrames_rulesJ env) hcv
  have hfresh : env.find? ci.toConstantVal.name = none := Option.isNone_iff_eq_none.mp hcv.1
  have hname : ciA.name = ci.toConstantVal.name := by
    rcases hkind with rfl | ⟨nP, nF, rfl⟩ <;> rfl
  have hcvA : ciA.toConstantVal =
      ⟨ci.toConstantVal.name, ci.toConstantVal.levelParams, type'⟩ := by
    rcases hkind with rfl | ⟨nP, nF, rfl⟩ <;> rfl
  have hfreshA : env.find? ciA.name = none := by rw [hname]; exact hfresh
  have hnotdefn : ∀ cv v hint, ciA ≠ .defnInfo cv v hint := by
    rcases hkind with rfl | ⟨nP, nF, rfl⟩ <;> intro _ _ _ hh <;> exact nomatch hh
  have hnotrec : NotRec ciA := by
    rcases hkind with rfl | ⟨nP, nF, rfl⟩ <;> intro _ _ _ _ hh <;> exact nomatch hh
  have hnotproj : NotProj ciA := by
    rcases hkind with rfl | ⟨nP, nF, rfl⟩ <;> intro _ hh <;> exact nomatch hh
  have hnotthm : NotThm ciA := by
    rcases hkind with rfl | ⟨nP, nF, rfl⟩ <;> intro _ _ hh <;> exact nomatch hh
  have hcaps0 : ∀ cv caps, ciA = .indInfo cv caps → caps = {} := by
    rcases hkind with rfl | ⟨nP, nF, rfl⟩
    · intro cv caps hh
      exact (ConstantInfo.indInfo.inj hh).2.symm
    · intro cv caps hh
      exact nomatch hh
  have hext : EnvExt env ⟨ciA :: env.consts⟩ :=
    EnvExt.cons hfreshA (fun _ => by rw [hname]; exact id_ne_projTableName hid _)
  have heta := etaShape_step_noEta hext h.etaCtorStored h.etaShape
    (NewSat.cons (fun cv caps heq => by
      have hc := hcaps0 cv caps heq
      subst hc
      rfl))
  exact
    { store := storeInv_consTyped h.store hfreshA (by rw [hcvA]; exact hty)
        (fun cv v hint heq => absurd heq (hnotdefn cv v hint)) hnotrec hnotproj
        (fun cv caps heq => by
          rw [hcaps0 cv caps heq]
          exact ⟨fun hh => (nomatch hh), fun hh => (nomatch hh)⟩)
      thmTyped := thmTyped_step_noThm hext h.thmTyped (NewSat.cons hnotthm)
      recK := recK_step_noRec h.store h.recK (fun hh => hext.find hh) (NewSat.cons hnotrec)
      etaTowers := etaTowers_step_noEta hext h.etaTowers
        (NewSat.cons (fun cv caps heq _ => by
          have hc := hcaps0 cv caps heq
          subst hc
          rfl))
      strongProps := strongEnvProps_step_noProj (fun hh => hext.find hh) h.strongProps
        (NewSat.cons hnotproj)
      recShape := recShape_step_noRec h.store h.recShape (fun hh => hext.find hh)
        (NewSat.cons hnotrec)
      etaCtorStored := heta.1
      etaShape := heta.2 }

theorem foldStoreInv_run {F : List (Key .anon)} :
    ∀ (members : List (ConstantInfo .anon)) {env env₂ : Env .anon},
      PointRun F env members env₂ → FoldStoreInv env → FoldStoreInv env₂
  | [], env, env₂, hrun, h => by
    have he : env₂ = env := hrun
    rw [he]
    exact h
  | ci :: rest, env, env₂, hrun, h => by
    obtain ⟨ciA, hm, hrest⟩ := hrun
    exact foldStoreInv_run rest hrest (foldStoreInv_member h hm)

/-! ## The conditional theorem -/

section Install

variable {env : Env .anon} {block : List (ConstantInfo .anon)} {formers : List FormerRec}
  {ctors : List CtorRec}

/-- **The fold's invariant is kept**, in every set theory. -/
theorem PointBlock.foldInv (hb : PointBlock env block formers ctors) :
    ∀ (V : Type u) [SetTheory V], FoldInv V env → FoldInv V (installed env formers ctors) :=
  fun V _ h =>
    ⟨pointRun_modelT hb.run
      (fun T hT => by
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hT
        exact hb.freshF f hf)
      hb.pin h.model,
    foldStoreInv_run _ hb.run h.store⟩

/-- The added keys are their own roots. -/
theorem PointBlock.auxRootSynced (hb : PointBlock env block formers ctors)
    (h : AuxRootSynced env) : AuxRootSynced (installed env formers ctors) := by
  rw [installed_eq]
  refine h.of_prepend (fun ci hci => ?_)
  obtain ⟨a, ha⟩ := hb.new_id hci
  have := env_find?_isSome_of_mem_prefix (tail := env.consts) hci
  rw [ha] at this ⊢
  exact this

/-- **The install extends the prefix**: every stored constant is kept, and no projection table
of a stored structure is added. -/
theorem PointBlock.envExt (hb : PointBlock env block formers ctors) :
    EnvExt env (installed env formers ctors) where
  find := fun {n c} hf => by
    rw [installed_eq, EnvExt.find?_append_of_fresh (fun x hx hn => by
      have := hb.freshChain.fresh x hx
      rw [hn, hf] at this
      exact nomatch this)]
    exact hf
  tables := fun {T cv caps} _ => by
    rw [installed_eq]
    exact EnvExt.find?_append_of_fresh (fun x hx hn => by
      obtain ⟨a, ha⟩ := hb.new_id hx
      rw [ha] at hn
      exact absurd hn.symm (auxKey_ne_id T .projTable a))

/-- **A constructors-only block installs and keeps the fold's invariant.** From the facts
`PointBlock` lists, the declaration `.indDecl block nP` installs into
`installed env formers ctors`: the prefix with the block's types (at the empty capability
record) and constructors in front, each stored as declared, and no other constant. The fold's
invariant, with or without the auxiliary-root companion, holds there in every set theory in
which it holds at the prefix. -/
theorem pointBlock_install (hb : PointBlock env block formers ctors) (nP : Nat) :
    InstallStep env (.indDecl block nP) (installed env formers ctors) ∧
      (∀ (V : Type u) [SetTheory V], FoldInv V env →
        FoldInv V (installed env formers ctors)) ∧
      (∀ (V : Type u) [SetTheory V], FullDeclInv V env →
        FullDeclInv V (installed env formers ctors)) ∧
      ∀ k, (env.find? k).isSome = true →
        ((installed env formers ctors).find? k).isSome = true :=
  ⟨hb.installStep nP, hb.foldInv,
    FullDeclInv.step_of_foldInv_aux hb.foldInv hb.auxRootSynced,
    fun k hk => isSome_of_envExt hb.envExt hk⟩

end Install

/-! ## What the stored block does not support

At the installed environment the block's types and constructors are stored and nothing else of
the family is. The lemmas below say so in the forms the declaration fold and the core's
companion facts read:

* no recursor is stored by the install (`newSat_notRec`), so the recursor companions of the
  prefix are the installed environment's (`coreCompanions`), and no rule of a native or basis
  recursor is at a constructor of the block, now or after any later declaration
  (`noRuleFamily`, with `Ix.Kernel.Model.noRuleFamily_declsRunJ`);
* a former of the block is stored at the empty capability record (`former_caps`): it is not
  η-capable, not unit-like, names no η constructor and carries no K, so the rules
  `DefEq.structEta`, `structEtaTy`, `structUnit` and `unitLikeTy`, each of which reads one of
  those flags at the family, have no instance at it (the rescues read a stored recursor);
* a former of the block has no projection table (`former_noTable`), so `Infer.proj` and
  `Red.proj` have no instance at it.

The only law of `Ix.Kernel.Model` that reads a member of the block is membership in its type.
-/

section NoLaws

variable {env : Env .anon} {block : List (ConstantInfo .anon)} {formers : List FormerRec}
  {ctors : List CtorRec}

/-- A constant the installed environment stores is the prefix's, or a former or a constructor
of the block in its stored form. -/
theorem PointBlock.find_cases (hb : PointBlock env block formers ctors) {n : Key .anon}
    {x : ConstantInfo .anon} (hf : (installed env formers ctors).find? n = some x) :
    env.find? n = some x ∨ (∃ f ∈ formers, x = f.stored) ∨ ∃ c ∈ ctors, x = c.stored := by
  rw [installed_eq] at hf
  rcases find?_append_inv hf with h | ⟨hmem, -⟩
  · exact Or.inl h
  · exact Or.inr (hb.new_cases hmem)

/-- **The install stores no recursor.** -/
theorem PointBlock.newSat_notRec (hb : PointBlock env block formers ctors) :
    NewSat env (installed env formers ctors) NotRec := by
  intro n x hf
  rcases hb.find_cases hf with h | ⟨f, -, rfl⟩ | ⟨c, -, rfl⟩
  · exact Or.inl h
  · exact Or.inr (fun _ _ _ _ hh => nomatch hh)
  · exact Or.inr (fun _ _ _ _ hh => nomatch hh)

/-- **The install stores no projection table.** -/
theorem PointBlock.newSat_notProj (hb : PointBlock env block formers ctors) :
    NewSat env (installed env formers ctors) NotProj := by
  intro n x hf
  rcases hb.find_cases hf with h | ⟨f, -, rfl⟩ | ⟨c, -, rfl⟩
  · exact Or.inl h
  · exact Or.inr (fun _ hh => nomatch hh)
  · exact Or.inr (fun _ hh => nomatch hh)

/-- **A former of the block is stored at the empty capability record**: no η, no unit-like
collapse, no η constructor, no K. -/
theorem PointBlock.former_caps (hb : PointBlock env block formers ctors) {f : FormerRec}
    (hf : f ∈ formers) {cvT : ConstantVal .anon} {caps : IndCaps .anon}
    (h : (installed env formers ctors).find? f.cv.name = some (.indInfo cvT caps)) :
    caps.eta = false ∧ caps.unitlike = false ∧ caps.etaCtor = none ∧ caps.ruleK = false := by
  have h2 := (hb.find_former hf).symm.trans h
  obtain ⟨-, hc⟩ := ConstantInfo.indInfo.inj (Option.some.inj h2)
  subst hc
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **A former of the block has no projection table**, at an environment whose auxiliary keys
have their roots stored. -/
theorem PointBlock.former_noTable (hb : PointBlock env block formers ctors)
    (haux : AuxRootSynced env) {f : FormerRec} (hf : f ∈ formers) :
    (installed env formers ctors).find? (projTableName f.cv.name) = none ∧
      ∀ i, (installed env formers ctors).findProj? f.cv.name i = none := by
  obtain ⟨a, ha⟩ := hb.keyF f hf
  have hold : env.find? (projTableName f.cv.name) = none :=
    haux.fresh_of_base_none (by
      rw [ha]
      have := hb.freshF f hf
      rw [ha] at this
      exact this)
  have hnew : (installed env formers ctors).find? (projTableName f.cv.name) = none := by
    rw [installed_eq, EnvExt.find?_append_of_fresh (fun x hx hn => by
      obtain ⟨b, hb'⟩ := hb.new_id hx
      rw [hb'] at hn
      exact absurd hn.symm (auxKey_ne_id f.cv.name .projTable b))]
    exact hold
  refine ⟨hnew, fun i => ?_⟩
  unfold Env.findProj?
  rw [hnew]

/-- **No rule of a native or basis recursor is at a constructor of the block's formers.** -/
theorem PointBlock.noRuleFamily (hb : PointBlock env block formers ctors)
    (hS : Ix.Kernel.Open.StoreInv env) {f : FormerRec} (hf : f ∈ formers) :
    NoRuleFamily (installed env formers ctors) f.cv.name :=
  noRuleFamily_step (noRuleFamily_of_fresh hS (hb.freshF f hf)) hS.rec_ctors
    (fun h => hb.envExt.find h)
    (newRulesAvoid_of_noNewRec (fun {n cv mI rP rules} h => by
      rcases hb.newSat_notRec n _ h with h' | h'
      · exact h'
      · exact absurd rfl (h' cv mI rP rules)))

/-- **A step that stores no recursor keeps the core's recursor and role companions.** The role
fields are monotone along the extension; the recursor fields read stored recursors, which are
the prefix's, and the constructors of their rules, which the prefix stores. -/
theorem coreCompanions_of_noRec {c : Ctx} (h : CoreCompanions c)
    (hS : Ix.Kernel.Open.StoreInv c.env) {env₂ : Env .anon} (hext : EnvExt c.env env₂)
    (hno : NewSat c.env env₂ NotRec) : CoreCompanions ⟨c.E, env₂, c.t, c.lim⟩ := by
  have hold : ∀ {k : Key .anon} {cv : ConstantVal .anon} {mI rP : Nat}
      {rls : List (RecRule .anon)}, env₂.find? k = some (.recInfo cv mI rP rls) →
      c.env.find? k = some (.recInfo cv mI rP rls) := by
    intro k cv mI rP rls hf
    rcases hno k _ hf with h' | h'
    · exact h'
    · exact absurd rfl (h' cv mI rP rls)
  have hctor : ∀ {k : Key .anon} {cv : ConstantVal .anon} {mI rP : Nat}
      {rls : List (RecRule .anon)} {rl : RecRule .anon} {cvj : ConstantVal .anon} {nP nF : Nat},
      c.env.find? k = some (.recInfo cv mI rP rls) → rl ∈ rls →
      env₂.find? rl.ctor = some (.ctorInfo cvj nP nF) →
      c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) := by
    intro k cv mI rP rls rl cvj nP nF hf hrl hc
    obtain ⟨-, cvj', nF', hc'⟩ := hS.recRules_fire hf hrl
    have h2 := hext.find hc'
    rw [hc] at h2
    rw [hc']
    exact h2.symm
  exact
    { natLit := fun h1 h2 h3 => hext.natLitSupported_mono (h.natLit h1 h2 h3)
      strLit := fun h1 => hext.strLitSupported_mono (h.strLit h1)
      natOps := fun r hr hm => hext.natOpStored_mono (h.natOps r hr hm)
      natAdd := fun h1 => hext.opt_mono (p := Ix.Kernel.Rules.natAddTyOk) (h.natAdd h1) rfl
      eqStored := fun h1 =>
        let ⟨ci', hci'⟩ := h.eqStored h1
        ⟨ci', hext.find hci'⟩
      quotBasis := fun h1 ci' hm => hext.find (h.quotBasis h1 ci' hm)
      recMajorRecord := fun k cv mI rP rls p us hf hne hdom =>
        h.recMajorRecord k cv mI rP rls p us (hold hf) hne hdom
      recRulesNodupAndProj := fun k cv mI rP rls hf =>
        h.recRulesNodupAndProj k cv mI rP rls (hold hf)
      recPlain := fun k cv mI rP rls rl cvj nP nF hf hrl hfire hc =>
        h.recPlain k cv mI rP rls rl cvj nP nF (hold hf) hrl hfire (hctor (hold hf) hrl hc)
      ruleCtorHead := fun k cv mI rP rls hf =>
        (h.ruleCtorHead k cv mI rP rls (hold hf)).imp
          (fun hhead rl cvj nP nF T us hrl hc hdom =>
            hhead rl cvj nP nF T us hrl (hctor (hold hf) hrl hc) hdom) id }

/-- **The install keeps the core's companions**, at every record store, table and group
limit. -/
theorem PointBlock.coreCompanions (hb : PointBlock env block formers ctors)
    (hS : Ix.Kernel.Open.StoreInv env) (E : Ixon.Env) (t : RoleTable) (lim : Option Nat)
    (h : CoreCompanions ⟨E, env, t, lim⟩) :
    CoreCompanions ⟨E, installed env formers ctors, t, lim⟩ :=
  coreCompanions_of_noRec (c := ⟨E, env, t, lim⟩) h hS hb.envExt hb.newSat_notRec

/-- **The step, in the shape every declaration route takes**: the install, the fold's invariant
with its auxiliary-root companion, the core's companions at every record store, table and group
limit, and the stored keys kept. -/
theorem pointBlock_step (hb : PointBlock env block formers ctors) (nP : Nat)
    (hS : Ix.Kernel.Open.StoreInv env) :
    ∃ env₂, InstallStep env (.indDecl block nP) env₂ ∧
      (∀ (V : Type u) [SetTheory V], FullDeclInv V env → FullDeclInv V env₂) ∧
      (∀ (E : Ixon.Env) (t : RoleTable) (lim : Option Nat),
        CoreCompanions ⟨E, env, t, lim⟩ → CoreCompanions ⟨E, env₂, t, lim⟩) ∧
      ∀ k, (env.find? k).isSome = true → (env₂.find? k).isSome = true :=
  ⟨installed env formers ctors, hb.installStep nP, (pointBlock_install.{u} hb nP).2.2.1,
    fun E t lim h => hb.coreCompanions hS E t lim h,
    fun k hk => isSome_of_envExt hb.envExt hk⟩

/-- No added constant is a model family's: the claimed environment keeps them all. -/
theorem PointBlock.not_modelAux (hb : PointBlock env block formers ctors)
    {x : ConstantInfo .anon} (hx : x ∈ newConsts formers ctors) :
    IxVM.Consistency.isModelAux x = false := by
  obtain ⟨a, ha⟩ := hb.new_id hx
  unfold IxVM.Consistency.isModelAux
  rw [ha]

end NoLaws

end IxVM.Refinement.Decl.Point
