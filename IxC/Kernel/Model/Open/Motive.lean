module

public import IxC.Kernel.Model.Open.Graded
public import IxC.Kernel.Model.Rules.Motive

@[expose] public section

/-!
# The rules' soundness over the public `Model`: the motives

The kernel's rules (`IxC/Kernel/Rules/Rel.lean`) are sound over every `Model V env`: one
motive per relation, read through the open-term denotation `DenotesO` at an assignment
`σ` of sets to the free variables the rules open binders with. A term the rules handle at
depth `d` is framed (`Frame`: its free variables are below `d`, hereditarily through their
types; it has no loose bound variable), so it is read at the fixed variable environment
`ρ₀`.

* `Ctx M φ σ e`: `σ` gives each free variable of `e` a member of what its type denotes,
  and the type's reading is graded.
* `RedS`: a reduct denotes what the subject does, and stays graded.
* `DefEqS`: two framed, graded sides denote the same set.
* `InferFullS`: at the full grade, the subject has a graded denotation, and so does its
  type, which holds it. This is what the kernel's typing of a declaration says in a model.
* `InferIOS`: at the io grade, a graded denotation of the subject is a member of a graded
  denotation of its type.

The frame and the leaf inclusion are the internal tier's (`Model/Rules/Motive.lean`).
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules
open Ix.Kernel.Model.Rules (Frame LeavesSub)

universe w

variable {V : Type w} [SetTheory V] {env : Env md}

/-- The variable environment a term with no loose bound variable is read at. -/
noncomputable def ρ₀ : BVarIdx → V := fun _ => empty

/-- `e` denotes `v` at the free-variable assignment `σ`. -/
abbrev Den (M : Model V env) (φ : LevelParam → Nat) (σ : Nat → V) (e : Expr md) (v : V) :
    Prop :=
  DenotesO M.cval env φ σ ρ₀ e v

/-- `e`'s reading at `σ` is graded. -/
abbrev Gr (M : Model V env) (φ : LevelParam → Nat) (σ : Nat → V) (e : Expr md) : Prop :=
  GradedBy (DenotesO M.cval env φ σ) ρ₀ e

/-- **`σ` satisfies `e`'s free variables**: each is a member of what its type denotes, and
the type's reading is graded. -/
def Ctx (M : Model V env) (φ : LevelParam → Nat) (σ : Nat → V) (e : Expr md) : Prop :=
  ∀ l ∈ e.fvarLeaves, (∃ T, Den M φ σ l.2 T ∧ σ l.1 ∈ˢ T) ∧ Gr M φ σ l.2

/-- **`Red`'s motive.** -/
def RedS (M : Model V env) (φ : LevelParam → Nat) (d : Nat) (e e' : Expr md) : Prop :=
  Frame d e → Frame d e' ∧ LeavesSub e' e ∧
    ∀ σ, Ctx M φ σ e → ∀ v, Den M φ σ e v → Gr M φ σ e → Den M φ σ e' v ∧ Gr M φ σ e'

/-- **`DefEq`'s motive.** -/
def DefEqS (M : Model V env) (φ : LevelParam → Nat) (d : Nat) (a b : Expr md) : Prop :=
  Frame d a → Frame d b → ∀ σ, Ctx M φ σ a → Ctx M φ σ b →
    ∀ v w, Den M φ σ a v → Den M φ σ b w → Gr M φ σ a → Gr M φ σ b → v = w

/-- **`Infer`'s motive at the full grade**: the subject and its type have graded
denotations, the first a member of the second. -/
def InferFullS (M : Model V env) (φ : LevelParam → Nat) (d : Nat) (e t : Expr md) : Prop :=
  Frame d e → Frame d t ∧ LeavesSub t e ∧
    ∀ σ, Ctx M φ σ e → ∃ v T, Den M φ σ e v ∧ Gr M φ σ e ∧ Den M φ σ t T ∧ Gr M φ σ t ∧
      v ∈ˢ T

/-- **`Infer`'s motive at the io grade**: a graded denotation of the subject is a member of
a graded denotation of its type. -/
def InferIOS (M : Model V env) (φ : LevelParam → Nat) (d : Nat) (e t : Expr md) : Prop :=
  Frame d e → Frame d t ∧ LeavesSub t e ∧
    ∀ σ, Ctx M φ σ e → ∀ v, Den M φ σ e v → Gr M φ σ e →
      ∃ T, Den M φ σ t T ∧ Gr M φ σ t ∧ v ∈ˢ T

/-- The grade-dispatched inference motive. -/
def InferS (M : Model V env) (φ : LevelParam → Nat) : Grade → Nat → Expr md → Expr md → Prop
  | .full, d, e, t => InferFullS M φ d e t
  | .io, d, e, t => InferIOS M φ d e t

/-- The full grade's motive gives the io grade's. -/
theorem InferFullS.io {M : Model V env} {φ : LevelParam → Nat} {d : Nat} {e t : Expr md}
    (h : InferFullS M φ d e t) : InferIOS M φ d e t := by
  intro hf
  obtain ⟨hft, hsub, k⟩ := h hf
  refine ⟨hft, hsub, fun σ hC v hv _ => ?_⟩
  obtain ⟨v', T, hv', -, hT, hgT, hm⟩ := k σ hC
  obtain rfl := DenotesO.functional hv hv'
  exact ⟨T, hT, hgT, hm⟩

/-! ## Frames -/

theorem Frame.app_iff {d : Nat} {f a : Expr md} : Frame d (.app f a) ↔ Frame d f ∧ Frame d a := by
  simp only [Frame, Expr.WScoped, Expr.looseBVarsBounded, Bool.and_eq_true, Expr.LeavesBounded,
    Expr.fvarLeaves, List.mem_append]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
    exact ⟨⟨h1, h3, fun l hl => h5 l (Or.inl hl)⟩, ⟨h2, h4, fun l hl => h5 l (Or.inr hl)⟩⟩
  · rintro ⟨⟨h1, h3, h5⟩, ⟨h2, h4, h6⟩⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, fun l hl => hl.elim (h5 l) (h6 l)⟩

theorem Frame.proj_iff {d : Nat} {s : Key md} {i : Nat} {e : Expr md} :
    Frame d (.proj s i e) ↔ Frame d e := by
  simp only [Frame, Expr.WScoped, Expr.looseBVarsBounded, Expr.LeavesBounded, Expr.fvarLeaves]

/-- The parts of a framed binder: its domain is framed, its body scoped one binder in. -/
structure BinderParts (d : Nat) (ty body : Expr md) : Prop where
  ty : Frame d ty
  ws : Expr.WScoped d body
  lbb : body.looseBVarsBounded 1 = true
  leaves : Expr.LeavesBounded body

theorem Frame.lam_parts {d : Nat} {ty body : Expr md} {m : BinderMeta}
    (h : Frame d (.lam ty body m)) : BinderParts d ty body := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩, hw.2, hb.2,
    fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.pi_parts {d : Nat} {ty body : Expr md} {m : BinderMeta}
    (h : Frame d (.forallE ty body m)) : BinderParts d ty body := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩, hw.2, hb.2,
    fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem BinderParts.lam {d : Nat} {ty body : Expr md} (h : BinderParts d ty body)
    (m : BinderMeta) : Frame d (.lam ty body m) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Expr.WScoped]; exact ⟨h.ty.1, h.ws⟩
  · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]; exact ⟨h.ty.2.1, h.lbb⟩
  · intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    exact hl.elim (h.ty.2.2 l) (h.leaves l)

theorem BinderParts.pi {d : Nat} {ty body : Expr md} (h : BinderParts d ty body)
    (m : BinderMeta) : Frame d (.forallE ty body m) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Expr.WScoped]; exact ⟨h.ty.1, h.ws⟩
  · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]; exact ⟨h.ty.2.1, h.lbb⟩
  · intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    exact hl.elim (h.ty.2.2 l) (h.leaves l)

/-- **Opening a binder at a fresh variable** frames the body one level deeper. -/
theorem BinderParts.open {d : Nat} {ty body : Expr md} (h : BinderParts d ty body) :
    Frame (d + 1) (body.instantiate1 (.fvar d ty)) := by
  refine ⟨Expr.WScoped.instantiate1 h.ty.1 0 h.ws,
    Ix.Kernel.looseBVarsBounded_instantiate1 body 0 h.lbb, ?_⟩
  intro l hl
  rcases Expr.fvarLeaves_instantiate1 body 0 hl with hl | hl
  · exact h.leaves l hl
  · simp only [Expr.fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact h.ty.2.1
    · exact h.ty.2.2 l hl

/-- **Substituting a framed value** for a binder's variable keeps the frame, and adds no
free variable beyond the body's and the value's. -/
theorem BinderParts.subst {d : Nat} {ty body a : Expr md} (h : BinderParts d ty body)
    (ha : Frame d a) :
    Frame d (body.instantiate1 a) ∧
      ∀ l ∈ (body.instantiate1 a).fvarLeaves, l ∈ body.fvarLeaves ∨ l ∈ a.fvarLeaves := by
  have hsub := fun l (hl : l ∈ (body.instantiate1 a).fvarLeaves) =>
    Expr.fvarLeaves_instantiate1 body 0 hl
  refine ⟨⟨Expr.WScoped.instantiate1_gen ha.1 0 h.ws,
    Expr.looseBVarsBounded_instantiate1_gen ha.2.1 h.lbb, fun l hl => ?_⟩, hsub⟩
  rcases hsub l hl with hl | hl
  · exact h.leaves l hl
  · exact ha.2.2 l hl

/-! ## Contexts -/

/-- The free variables of a scoped term are below the depth, and each one's type is scoped
below the variable. -/
theorem leaves_scoped : ∀ {e : Expr md} {d : Nat}, Expr.WScoped d e →
    ∀ l ∈ e.fvarLeaves, l.1 < d ∧ Expr.WScoped l.1 l.2 := by
  intro e
  induction e with
  | fvar idx ty ih =>
    intro d hw l hl
    simp only [Expr.WScoped] at hw
    simp only [Expr.fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact hw
    · have h := ih hw.2 l hl
      exact ⟨Nat.lt_trans h.1 hw.1, h.2⟩
  | app f a ihf iha =>
    intro d hw l hl
    simp only [Expr.WScoped] at hw
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    exact hl.elim (ihf hw.1 l) (iha hw.2 l)
  | lam ty b _ iht ihb =>
    intro d hw l hl
    simp only [Expr.WScoped] at hw
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    exact hl.elim (iht hw.1 l) (ihb hw.2 l)
  | forallE ty b _ iht ihb =>
    intro d hw l hl
    simp only [Expr.WScoped] at hw
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    exact hl.elim (iht hw.1 l) (ihb hw.2 l)
  | letE t v b _ iht ihv ihb =>
    intro d hw l hl
    simp only [Expr.WScoped] at hw
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact iht hw.1 l hl
    · exact ihv hw.2.1 l hl
    · exact ihb hw.2.2 l hl
  | proj s i e ih =>
    intro d hw l hl
    simp only [Expr.WScoped] at hw
    simp only [Expr.fvarLeaves] at hl
    exact ih hw l hl
  | bvar _ => intro d _ l hl; simp [Expr.fvarLeaves] at hl
  | sort _ => intro d _ l hl; simp [Expr.fvarLeaves] at hl
  | const _ _ => intro d _ l hl; simp [Expr.fvarLeaves] at hl
  | lit _ => intro d _ l hl; simp [Expr.fvarLeaves] at hl

theorem Ctx.of_subset {M : Model V env} {φ : LevelParam → Nat} {σ : Nat → V} {e e' : Expr md}
    (h : Ctx M φ σ e) (hs : LeavesSub e' e) : Ctx M φ σ e' :=
  fun l hl => h l (hs l hl)

omit [SetTheory V] in
theorem setAt_ne {σ : Nat → V} {d i : Nat} {x : V} (h : i ≠ d) : setAt σ d x i = σ i := by
  simp [setAt, h]

omit [SetTheory V] in
theorem setAt_self {σ : Nat → V} {d : Nat} {x : V} : setAt σ d x d = x := by
  simp [setAt]

/-- A reading of a term scoped below `d` does not see free variable `d`. -/
theorem Den.setAbove {M : Model V env} {φ : LevelParam → Nat} {σ : Nat → V} {d : Nat} {x : V}
    {e : Expr md} (hw : Expr.WScoped d e) {v : V} :
    Den M φ (setAt σ d x) e v ↔ Den M φ σ e v :=
  ⟨fun h => h.congr_fvars fun l hl => setAt_ne (Nat.ne_of_lt (leaves_scoped hw l hl).1),
   fun h => h.congr_fvars fun l hl => (setAt_ne (Nat.ne_of_lt (leaves_scoped hw l hl).1)).symm⟩

theorem Gr.setAbove {M : Model V env} {φ : LevelParam → Nat} {σ : Nat → V} {d : Nat} {x : V}
    {e : Expr md} (hw : Expr.WScoped d e) :
    Gr M φ (setAt σ d x) e ↔ Gr M φ σ e :=
  ⟨fun h => GradedBy.congr_fvarsO
      (fun l hl => setAt_ne (Nat.ne_of_lt (leaves_scoped hw l hl).1)) h,
   fun h => GradedBy.congr_fvarsO
      (fun l hl => (setAt_ne (Nat.ne_of_lt (leaves_scoped hw l hl).1)).symm) h⟩

/-- **A context survives setting a variable above the term's scope.** -/
theorem Ctx.setAbove {M : Model V env} {φ : LevelParam → Nat} {σ : Nat → V} {d : Nat} {x : V}
    {e : Expr md} (hw : Expr.WScoped d e) (h : Ctx M φ σ e) : Ctx M φ (setAt σ d x) e := by
  intro l hl
  obtain ⟨hlt, hwl⟩ := leaves_scoped hw l hl
  have hwl' : Expr.WScoped d l.2 := Expr.WScoped.mono (Nat.le_of_lt hlt) hwl
  obtain ⟨⟨T, hT, hm⟩, hg⟩ := h l hl
  exact ⟨⟨T, (Den.setAbove hwl').2 hT, by rw [setAt_ne (Nat.ne_of_lt hlt)]; exact hm⟩,
    (Gr.setAbove hwl').2 hg⟩

/-- **The context of an opened binder body**: setting the fresh variable `d` to a member
`x` of the domain's denotation satisfies the opened body's free variables. -/
theorem Ctx.open {M : Model V env} {φ : LevelParam → Nat} {σ : Nat → V} {d : Nat} {x A : V}
    {ty body : Expr md} (hwty : Expr.WScoped d ty) (hwb : Expr.WScoped d body)
    (hCty : Ctx M φ σ ty) (hCb : Ctx M φ σ body) (hA : Den M φ σ ty A) (hx : x ∈ˢ A)
    (hgty : Gr M φ σ ty) :
    Ctx M φ (setAt σ d x) (body.instantiate1 (.fvar d ty)) := by
  intro l hl
  rcases Expr.fvarLeaves_instantiate1 body 0 hl with hl | hl
  · exact Ctx.setAbove hwb hCb l hl
  · simp only [Expr.fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · refine ⟨⟨A, (Den.setAbove hwty).2 hA, ?_⟩, (Gr.setAbove hwty).2 hgty⟩
      show setAt σ d x d ∈ˢ A
      rw [setAt_self]
      exact hx
    · exact Ctx.setAbove hwty hCty l hl

/-! ## Readings -/

/-- A binder's datum `never` is read in the graph regime. -/
theorem regime_ne_zero_of_isNever {pw : PropWhen} (h : pw.isNever = true) (φ : LevelParam → Nat) :
    regime φ pw ≠ 0 := by
  rw [PropWhen.isNever_iff.mp h]
  simp [regime]

/-- A term with no loose bound variable denotes alike at every variable environment. -/
theorem Den.all {M : Model V env} {φ : LevelParam → Nat} {σ : Nat → V} {e : Expr md} {v : V}
    (h : Den M φ σ e v) (hb : e.looseBVarsBounded 0 = true) :
    ∀ ρ, DenotesO M.cval env φ σ ρ e v :=
  fun _ => h.closed hb

theorem Gr.all {M : Model V env} {φ : LevelParam → Nat} {σ : Nat → V} {e : Expr md}
    (h : Gr M φ σ e) (hb : e.looseBVarsBounded 0 = true) :
    ∀ ρ, GradedBy (DenotesO M.cval env φ σ) ρ e :=
  fun _ => GradedBy.closedO h hb

/-- **β in the sets**: a λ applied to a member of its domain is its body there. -/
theorem app_lamR_of_mem {r : Nat} {A X : V} {F : V → V} (hX : X ∈ˢ A)
    (hP : r = 0 → ∀ x, x ∈ˢ A → F x = pt) : app (lamR r A F) X = F X := by
  by_cases hr : r = 0
  · subst hr
    rw [lamR_zero, app_pt, hP rfl X hX]
  · exact app_lamR_pos hr hX

/-- **A graph-regime λ graded at an application has the argument in its domain.** -/
theorem mem_dom_of_graded {r r' : Nat} {A A' X : V} {B : V → V} {G : V → V}
    (hr : r ≠ 0) (hmem : lamR r A G ∈ˢ piR r' A' B) (hX : X ∈ˢ A') : X ∈ˢ A := by
  have hr' : r' ≠ 0 := by
    intro h0
    subst h0
    exact lamR_ne_pt hr (eq_pt_of_mem_piR_zero hmem)
  have hself : lamR r A G ∈ˢ piR r A (fun x => sing (G x)) :=
    lamR_mem (fun x _ => mem_sing.mpr rfl)
  rw [piR_dom_unique hr hr' hself hmem]
  exact hX

end Ix.Kernel.Open
