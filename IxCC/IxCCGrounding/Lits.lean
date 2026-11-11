import IxCCGrounding.Model

/-!
# `Nat` literals in a model (`IxCCGrounding.Lits`)

The literal reading needs `Nat`, `Nat.zero` and `Nat.succ` stored as the kernel stores them
(`NatBasis`, a checked fact). Then a literal denotes its constructor form (`Denotes.natLit`):
`litSet M φ n`, the `n`-fold successor of `Nat.zero`'s denotation. It lies in `⟦Nat⟧`, by `mem`
of `Nat.zero` and `Nat.succ`, and it does not depend on the level assignment, by `cval_params`
(the constructors have no level parameters).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory

universe w

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- The facts about the basis the literal reading uses, at an assignment `φ`. -/
structure NatFacts (M : Model V env) (φ : LevelParam → Nat) : Prop where
  natD : ∀ (ρ : BVarIdx → V) (X : V), Denotes M.cval env φ ρ natK X ↔ X = M.cval natName φ
  zeroD : ∀ (ρ : BVarIdx → V) (X : V), Denotes M.cval env φ ρ zeroK X ↔ X = M.cval natZeroName φ
  succD : ∀ (ρ : BVarIdx → V) (X : V), Denotes M.cval env φ ρ succK X ↔ X = M.cval natSuccName φ
  zeroMem : M.cval natZeroName φ ∈ˢ M.cval natName φ
  succMem : ∀ n, n ∈ˢ M.cval natName φ → app (M.cval natSuccName φ) n ∈ˢ M.cval natName φ

theorem natFacts (M : Model V env) (hS : NatBasis env) (φ : LevelParam → Nat) :
    NatFacts M φ := by
  obtain ⟨ciN, hfN, hlN⟩ := hS.nat
  obtain ⟨cvZ, hfZ, hnZ, htZ, hlZ⟩ := hS.zero
  obtain ⟨cvS, hfS, hnS, htS, hlS⟩ := hS.succ
  have natD : ∀ (ρ : BVarIdx → V) (X : V),
      Denotes M.cval env φ ρ natK X ↔ X = M.cval natName φ := fun _ _ => den_const0 hfN hlN
  refine ⟨natD, fun _ _ => den_const0 hfZ hlZ, fun _ _ => den_const0 hfS hlS, ?_, ?_⟩
  · obtain ⟨T, hT, hm⟩ := M.mem _ (find_mem hfZ) φ (fun _ => empty)
    simp only [ConstantInfo.toConstantVal, ConstantInfo.name] at hT hm
    rw [htZ] at hT
    rw [hnZ, (natD _ T).mp hT] at hm
    exact hm
  · intro n hn
    obtain ⟨T, hT, hm⟩ := M.mem _ (find_mem hfS) φ (fun _ => empty)
    simp only [ConstantInfo.toConstantVal, ConstantInfo.name] at hT hm
    rw [htS] at hT
    rw [hnS] at hm
    obtain ⟨B, hB, happ⟩ := app_mem_den_pi hT ((natD _ _).mpr rfl) hm hn
    rwa [(natD _ B).mp hB] at happ

noncomputable def litSet (M : Model V env) (φ : LevelParam → Nat) : Nat → V
  | 0 => M.cval natZeroName φ
  | n + 1 => app (M.cval natSuccName φ) (litSet M φ n)

theorem lit_den (M : Model V env) {φ : LevelParam → Nat} (hF : NatFacts M φ) (ρ : BVarIdx → V) :
    ∀ (n : Nat) (X : V), Denotes M.cval env φ ρ (litE n) X ↔ X = litSet M φ n
  | 0, X => ⟨fun h => by cases h with | natLit h' => exact (hF.zeroD _ _).mp h',
      fun h => h ▸ .natLit ((hF.zeroD _ _).mpr rfl)⟩
  | n + 1, X => ⟨fun h => by
        cases h with
        | natLit h' =>
          obtain ⟨F, A, hF', hA, hX⟩ := den_app.mp h'
          rw [hX, (hF.succD _ _).mp hF', (lit_den M hF ρ n A).mp hA]
          rfl,
      fun h => h ▸ .natLit (.app ((hF.succD _ _).mpr rfl) ((lit_den M hF ρ n _).mpr rfl))⟩

theorem lit_mem (M : Model V env) {φ : LevelParam → Nat} (hF : NatFacts M φ) :
    ∀ n, litSet M φ n ∈ˢ M.cval natName φ
  | 0 => hF.zeroMem
  | n + 1 => hF.succMem _ (lit_mem M hF n)

theorem litSet_indep (M : Model V env) (hL : Laws M) (hS : NatBasis env)
    (φ φ' : LevelParam → Nat) : ∀ n, litSet M φ n = litSet M φ' n
  | 0 => by
    obtain ⟨cvZ, hfZ, _, _, hlZ⟩ := hS.zero
    exact hL.cval_params _ _ hfZ φ φ' (by simp [ConstantInfo.toConstantVal, hlZ])
  | n + 1 => by
    obtain ⟨cvS, hfS, _, _, hlS⟩ := hS.succ
    simp only [litSet]
    rw [hL.cval_params _ _ hfS φ φ' (by simp [ConstantInfo.toConstantVal, hlS]),
      litSet_indep M hL hS φ φ' n]

end IxCC.Grounding
