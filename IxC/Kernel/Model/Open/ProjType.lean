module

public import IxC.Kernel.Model.Open.Rescue
import IxC.Kernel.Verify.InstSpine
import IxC.Kernel.Verify.Leaves
import IxC.Kernel.Verify.Shift

@[expose] public section

/-!
# The rules' soundness over the public `Model`: a projection's type

`Infer.proj` types `.proj T i e` by the table entry's stored body, instantiated at the
arguments of the subject's reduced type and at the subject (`ProjEntry.typeAt`). Its soundness
reads the projection-typing law (`Model.proj_type`) at the values:

* the reduced type's grading gives the parameters' licence (`spineOk_of_graded`);
* the substitution lemmas for a spine of closed values (`DenotesO.instSpine`,
  `GradedBy.instSpineO`) read the instantiated body as the body with the values pushed in
  order, which is how the law reads it;
* the table's guard is `FireSem` with the entry's O5 bound (`towerGuardAt_of_sem`), and the
  body's scoping is the stored environment's (`StoredBodies`).
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules
open Ix.Kernel.Model.Rules (Frame LeavesSub)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Pushing a list of values -/

omit [SetTheory V] in
/-- Inserting below a pushed list is inserting before pushing it. -/
theorem insertAt_pushVals : ∀ (xs : List V) (k : Nat) (x : V) (ρ : BVarIdx → V),
    insertAt (k + xs.length) x (pushVals ρ xs) = pushVals (insertAt k x ρ) xs
  | [], _, _, _ => rfl
  | y :: ys, k, x, ρ => by
    show insertAt (k + (ys.length + 1)) x (pushVals (push y ρ) ys) =
      pushVals (push y (insertAt k x ρ)) ys
    rw [push_insertAt, ← insertAt_pushVals ys (k + 1) x (push y ρ),
      show k + 1 + ys.length = k + (ys.length + 1) by omega]

omit [SetTheory V] in
theorem pushVals_snoc : ∀ (xs : List V) (x : V) (ρ : BVarIdx → V),
    pushVals ρ (xs ++ [x]) = push x (pushVals ρ xs)
  | [], _, _ => rfl
  | y :: ys, x, ρ => pushVals_snoc ys x (push y ρ)

variable {env : Env md} {M : Model V env} {φ : LevelParam → Nat}

/-! ## A spine of closed values -/

/-- **Substituting a spine of closed values** for a body's outer bound variables, outermost
first (`instSpine`), denotes what the body denotes with the values pushed in order. -/
theorem DenotesO.instSpine {σ : Nat → V} {args : List (Expr md)} {xs : List V}
    (h : DenList M φ σ args xs) : (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
    ∀ (e : Expr md) (ρ : BVarIdx → V) (v : V),
      DenotesO M.cval env φ σ ρ (Expr.instSpine args (args.length - 1) e) v ↔
        DenotesO M.cval env φ σ (pushVals ρ xs) e v := by
  induction h with
  | nil => intro _ e ρ v; exact Iff.rfl
  | @cons a as x xs hx hxs ih =>
    intro hb e ρ v
    have hl : as.length = xs.length := hxs.length_eq
    have ha := Den.all hx (hb a List.mem_cons_self)
    simp only [List.length_cons, Nat.add_sub_cancel, Expr.instSpine]
    rw [ih (fun c hc => hb c (List.mem_cons_of_mem _ hc)),
      DenotesO.instantiate1 ha e as.length (pushVals ρ xs) v, hl]
    have hins := insertAt_pushVals xs 0 x ρ
    rw [Nat.zero_add, insertAt_zero] at hins
    show _ ↔ DenotesO M.cval env φ σ (pushVals (push x ρ) xs) e v
    rw [hins]

/-- **Substituting a spine of closed, graded values** grades as the body does with the values
pushed in order. -/
theorem GradedBy.instSpineO {σ : Nat → V} {args : List (Expr md)} {xs : List V}
    (h : DenList M φ σ args xs) : (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
    (∀ a ∈ args, Gr M φ σ a) →
    ∀ (e : Expr md) (ρ : BVarIdx → V),
      GradedBy (DenotesO M.cval env φ σ) ρ (Expr.instSpine args (args.length - 1) e) ↔
        GradedBy (DenotesO M.cval env φ σ) (pushVals ρ xs) e := by
  induction h with
  | nil => intro _ _ e ρ; exact Iff.rfl
  | @cons a as x xs hx hxs ih =>
    intro hb hg e ρ
    have hl : as.length = xs.length := hxs.length_eq
    have hba := hb a List.mem_cons_self
    simp only [List.length_cons, Nat.add_sub_cancel, Expr.instSpine]
    rw [ih (fun c hc => hb c (List.mem_cons_of_mem _ hc))
        (fun c hc => hg c (List.mem_cons_of_mem _ hc)),
      GradedBy.instantiate1O (Den.all hx hba) (Gr.all (hg a List.mem_cons_self) hba) e
        as.length (pushVals ρ xs), hl]
    have hins := insertAt_pushVals xs 0 x ρ
    rw [Nat.zero_add, insertAt_zero] at hins
    show _ ↔ GradedBy (DenotesO M.cval env φ σ) (pushVals (push x ρ) xs) e
    rw [hins]

/-! ## The projection's type -/

/-- **The type of a projection, read**: the entry's body at the reduced type's arguments and
the subject is framed, its free variables are the subject's, and at a member `P` of the
subject's type it denotes, gradedly, a set holding the projection's value. -/
theorem proj_type_reads (hse : StoredEnv env) {d : Nat} {sn : Key md} {i : Nat}
    {pe tpe te : Expr md} {us : List Level} {entry : ProjEntry md}
    (hte : RedS M φ d tpe te) (hhead : te.getAppFn = .const sn us)
    (hP : env.findProj? sn i = some entry) (hlen : te.getAppArgs.length = entry.numParams)
    (hus : us.length = entry.levelParams.length) (hfire : FireSem entry us)
    (hfpe : Frame d pe) (hftpe : Frame d tpe) (hsub : LeavesSub tpe pe) :
    Frame d (entry.typeAt us te.getAppArgs pe) ∧
      LeavesSub (entry.typeAt us te.getAppArgs pe) (.proj sn i pe) ∧
      ∀ σ, Ctx M φ σ pe → ∀ P T, Den M φ σ pe P → Gr M φ σ pe → Den M φ σ tpe T →
        Gr M φ σ tpe → P ∈ˢ T →
        ∃ B, Den M φ σ (entry.typeAt us te.getAppArgs pe) B ∧
          Gr M φ σ (entry.typeAt us te.getAppArgs pe) ∧ field (i + entry.off) P ∈ˢ B := by
  obtain ⟨hfte, hsubte, kte⟩ := hte hftpe
  obtain ⟨hbf, hbb⟩ := hse.bodies sn i entry hP
  obtain ⟨-, hO5, -, -⟩ := hse.tables sn i entry hP
  have hbf' : (entry.body.instantiateLevelParams entry.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact hbf
  have hbb' : (entry.body.instantiateLevelParams entry.levelParams us).looseBVarsBounded
      (entry.numParams + 1) = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hbb
  have heq := Ix.Kernel.ProjEntry.typeAt_eq_instSpine entry us hlen pe
  have hfargs := Frame.getAppArgs hfte
  have hall : ∀ a ∈ te.getAppArgs ++ [pe], Frame d a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hfargs a ha
    · rw [List.mem_singleton.mp ha]; exact hfpe
  have hlen' : (te.getAppArgs ++ [pe]).length - 1 = entry.numParams := by simp [hlen]
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    refine ⟨Ix.Kernel.instSpine_WScoped _ (Expr.WScoped.of_not_hasFvar hbf')
      fun a ha => (hall a ha).1, ?_, ?_⟩
    · have h := Ix.Kernel.instSpine_closed (args := te.getAppArgs ++ [pe])
        (fun a ha => (hall a ha).2.1)
        (by rw [show (te.getAppArgs ++ [pe]).length = entry.numParams + 1 by simp [hlen]]
            exact hbb')
      rwa [hlen'] at h
    · intro l hl
      rcases Ix.Kernel.fvarLeaves_instSpine _ hl with hl | ⟨a, ha, hla⟩
      · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hbf'] at hl; exact nomatch hl
      · exact (hall a ha).2.2 l hla
  · intro l hl
    rw [heq] at hl
    simp only [Expr.fvarLeaves]
    rcases Ix.Kernel.fvarLeaves_instSpine _ hl with hl | ⟨a, ha, hla⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hbf'] at hl; exact nomatch hl
    · rcases List.mem_append.mp ha with ha | ha
      · exact hsub l (hsubte l (fvarLeaves_getAppArgs ha l hla))
      · rw [List.mem_singleton.mp ha] at hla; exact hla
  · intro σ hCpe P T hPd hgP hT hgT hPT
    obtain ⟨hTe, hgte⟩ := kte σ (hCpe.of_subset hsub) T hT hgT
    have hsp := eq_mkAppN_of_getAppFn hhead
    have hTe' : Den M φ σ (Expr.mkAppN (.const sn us) te.getAppArgs) T := by
      rw [← hsp]; exact hTe
    have hgte' : Gr M φ σ (Expr.mkAppN (.const sn us) te.getAppArgs) := by
      rw [← hsp]; exact hgte
    obtain ⟨F, ts, hF, hts, rfl⟩ := Den.mkAppN_inv hTe'
    have htslen : ts.length = entry.numParams := by rw [← hts.length_eq, hlen]
    -- the law at the values
    obtain ⟨B, hB, hgB, hmB⟩ := M.proj_type sn i entry hP us φ ρ₀ F ts P hus
      (DenotesO.to_denotes hF rfl) (Ix.Kernel.Model.towerGuardAt_of_sem hO5 hfire) htslen
      (spineOk_of_graded hgte' hF hts) hPT
    -- the instantiated body is the body at the values
    have hargs : DenList M φ σ (te.getAppArgs ++ [pe]) (ts ++ [P]) :=
      DenList.append hts (.cons hPd .nil)
    have hbargs : ∀ a ∈ te.getAppArgs ++ [pe], a.looseBVarsBounded 0 = true :=
      fun a ha => (hall a ha).2.1
    have hgargs : ∀ a ∈ te.getAppArgs ++ [pe], Gr M φ σ a := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact Gr.mkAppN_args hgte' a ha
      · rw [List.mem_singleton.mp ha]; exact hgP
    refine ⟨B, ?_, ?_, hmB⟩
    · have h := (DenotesO.instSpine hargs hbargs
        (entry.body.instantiateLevelParams entry.levelParams us) ρ₀ B).2
        (by rw [pushVals_snoc]; exact DenotesO.of_denotes hB)
      rw [hlen'] at h
      rw [heq]; exact h
    · have h := (GradedBy.instSpineO hargs hbargs hgargs
        (entry.body.instantiateLevelParams entry.levelParams us) ρ₀).2
        (by rw [pushVals_snoc]; exact GradedBy.toOpen hgB hbf')
      rw [hlen'] at h
      rw [heq]; exact h

/-- **Projection** (`Infer.proj`): the scrutinee's type reduces to the structure at its
parameters, so the projection-typing law types the projection by the entry's body. -/
theorem Infer.proj_sound (hse : StoredEnv env) {g : Grade} {d : Nat} {sn : Key md} {i : Nat}
    {pe tpe te : Expr md} {us : List Level} {entry : ProjEntry md}
    (htpe : InferS M φ g d pe tpe) (hte : RedS M φ d tpe te)
    (hhead : te.getAppFn = .const sn us) (hP : env.findProj? sn i = some entry)
    (hlen : te.getAppArgs.length = entry.numParams) (hus : us.length = entry.levelParams.length)
    (hfire : FireSem entry us) :
    InferS M φ g d (.proj sn i pe) (entry.typeAt us te.getAppArgs pe) := by
  cases g with
  | full =>
    intro hfr
    have hfpe : Frame d pe := Frame.proj_iff.1 hfr
    obtain ⟨hftpe, hsub, k⟩ := (htpe : InferFullS M φ d pe tpe) hfpe
    obtain ⟨hft, hsubt, kt⟩ := proj_type_reads hse hte hhead hP hlen hus hfire hfpe hftpe hsub
    refine ⟨hft, hsubt, fun σ hC => ?_⟩
    have hCpe : Ctx M φ σ pe := hC.of_subset fun l hl => by simpa [Expr.fvarLeaves] using hl
    obtain ⟨P, T, hPd, hgP, hT, hgT, hPT⟩ := k σ hCpe
    obtain ⟨B, hB, hgB, hmB⟩ := kt σ hCpe P T hPd hgP hT hgT hPT
    exact ⟨_, B, .proj_table hP hPd, hgP, hB, hgB, hmB⟩
  | io =>
    intro hfr
    have hfpe : Frame d pe := Frame.proj_iff.1 hfr
    obtain ⟨hftpe, hsub, k⟩ := (htpe : InferIOS M φ d pe tpe) hfpe
    obtain ⟨hft, hsubt, kt⟩ := proj_type_reads hse hte hhead hP hlen hus hfire hfpe hftpe hsub
    refine ⟨hft, hsubt, fun σ hC v hv hg => ?_⟩
    have hCpe : Ctx M φ σ pe := hC.of_subset fun l hl => by simpa [Expr.fvarLeaves] using hl
    obtain ⟨P, hPd, rfl⟩ : ∃ P, Den M φ σ pe P ∧ v = field (i + entry.off) P := by
      cases hv with
      | proj_table ht he => rw [hP] at ht; cases ht; exact ⟨_, he, rfl⟩
      | proj_fst ht _ => rw [hP] at ht; exact nomatch ht
      | proj_snd ht _ => rw [hP] at ht; exact nomatch ht
    have hgP : Gr M φ σ pe := hg
    obtain ⟨T, hT, hgT, hPT⟩ := k σ hCpe P hPd hgP
    exact kt σ hCpe P T hPd hgP hT hgT hPT

end Ix.Kernel.Open
