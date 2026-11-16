import IxVMRefinement.Decl.AnnotationInputScope
import IxVMRefinement.Decl.ThmBodyView
import IxC.Kernel.Verify.Rename.UnionFold

/-! # Name scopes from actual prefix checking

The checker confines installed names to declared bases. A resolved raw type therefore
belongs to the scope of the prefix's names. These results keep the scope producer separate
from the later-unit noninterference required by an environment frame.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

/-- Resolution supplies expression support at any scope covering the environment's stored keys. -/
theorem expression_good_of_resolves {env : Env .anon} {P : KeyScope .anon}
    (keys : ∀ name, (env.find? name).isSome = true → name.Good P) :
    ∀ (e : Expr .anon), e.constsResolve env = true → e.Good P := by
  intro e
  induction e with
  | bvar _ | sort _ => intro _; trivial
  | fvar _ ty ih => exact ih
  | const name levels => intro found; exact keys name found
  | app f a ihf iha =>
    intro resolved
    simp only [Expr.constsResolve, Bool.and_eq_true] at resolved
    exact ⟨ihf resolved.1, iha resolved.2⟩
  | lam ty body bm iht ihb | forallE ty body bm iht ihb =>
    intro resolved
    simp only [Expr.constsResolve, Bool.and_eq_true] at resolved
    exact ⟨iht resolved.1, ihb resolved.2⟩
  | letE ty value body bm iht ihv ihb =>
    intro resolved
    simp only [Expr.constsResolve, Bool.and_eq_true] at resolved
    exact ⟨iht resolved.1.1, ihv resolved.1.2, ihb resolved.2⟩
  | proj name i inner ih =>
    intro resolved
    simp only [Expr.constsResolve, Bool.and_eq_true] at resolved
    exact ⟨keys name resolved.1, ih resolved.2⟩
  | lit literal =>
    cases literal with
    | natVal _ => intro _; trivial
    | strVal _ =>
      intro resolved role member
      apply keys (.role role)
      simp only [Expr.constsResolve, Bool.and_eq_true] at resolved
      rcases resolved with ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hString⟩, hStringOfList⟩, hList⟩, hNil⟩, hCons⟩, hChar⟩, hCharOfNat⟩
      simp only [strRoles, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals assumption

/-- Every successful pure fold confines its stored names to the names declared so far. -/
theorem checkedDecls_findOver {md : Mode} (mode : CheckMode) (fuel : Nat) (ev : Evidences md) :
    ∀ (declarations : List (Declaration md)) (known : List (Key md)) {before after : Env md},
      FindOver known before →
      declarations.foldlM (checkDecl mode (fueledOps mode fuel) ev) before = .ok after →
      FindOver (known ++ declarations.flatMap Declaration.names) after := by
  intro declarations
  induction declarations with
  | nil =>
    intro known before after confined checked
    have same : before = after := Except.ok.inj checked
    subst after
    simpa only [List.flatMap_nil, List.append_nil] using confined
  | cons d rest ih =>
    intro known before after confined checked
    obtain ⟨middle, head, tail⟩ := foldlM_cons_ok checked
    have grown := checkDecl_post mode (fueledOps mode fuel) ev before d middle head
    have next : FindOver (known ++ d.names) middle := by
      intro name ci found
      rcases grown.find_cases found with old | added
      · exact (confined name ci old).mono (fun _ member => List.mem_append_left _ member)
      · exact added.1.mono (fun _ member => List.mem_append_right _ member)
    simpa only [List.flatMap_cons, List.append_assoc] using ih (known ++ d.names) next tail

/-- Checked theorem-body replacement preserves the installed-name scope. -/
theorem ThmBodyView.Agrees.findOver {source target : Env .anon}
    (agreement : ThmBodyView.Agrees source target) {known : List (Key .anon)}
    (confined : FindOver known source) : FindOver known target := by
  intro name ci found
  have present : (source.find? name).isSome = true := by
    rw [agreement.isSome, found]
    rfl
  obtain ⟨original, originalFound⟩ := Option.isSome_iff_exists.mp present
  exact confined name original originalFound

/-- The real constant check places the raw reader type in the prefix's declared name scope. -/
theorem constantValRun_good_input {env : Env .anon} (store : Ix.Kernel.Open.StoreInv env)
    {known : List (Key .anon)} (confined : FindOver known env)
    {fuel : Nat} {cv : ConstantVal .anon} {type : Core.KExpr}
    (run : Ix.Kernel.Semantics.ConstantValRun .verified fuel env cv type) :
    cv.type.Good (nameScope known) := by
  apply expression_good_of_resolves ?_ cv.type (constantValRun_input_resolves store run)
  intro name present
  obtain ⟨ci, found⟩ := Option.isSome_iff_exists.mp present
  exact Key.good_nameScope.mpr (confined name ci found)

end IxVM.Refinement.Decl
