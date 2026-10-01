import Compilatrix.Anf.Proof.Walk.Prog
import Compilatrix.Anf.Proof.Convert.Prog

/-! # Passes over a program's globals

What the middle-end passes keep: the globals live below the program's size
(`GlobalsBelow`, established by P1 and kept by every pass), a program
rebuilt from its global list with each global mapped has the mapped globals
(`get?_ofList_globalList`), and a program with the same globals refines its
source (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf

/-- Every global lies below the program's size (so `globalList` lists
them all). -/
def Program.GlobalsBelow (P : Program) : Prop := ∀ g gd, P.global? g = some gd → g < P.size

/-- Every id below the size has a global. -/
def Program.Dense (P : Program) : Prop := ∀ g, g < P.size → ∃ gd, P.global? g = some gd

/-- The global ids are exactly `0 … size - 1`. -/
def Program.WF (P : Program) : Prop := P.GlobalsBelow ∧ P.Dense

namespace PassProof

open Compilatrix.Sem (Result)

theorem get?_ofList_globalList (P : Program) (F : GlobalId → GDef → GDef) (g : GlobalId) :
    (Src.NatMap.ofList (P.globalList.map fun p => (p.1, F p.1 p.2))).get? g =
      if g < P.size then (P.global? g).map (F g) else none := by
  have hn : ((P.globalList.map fun p => (p.1, F p.1 p.2)).map (·.1)).Nodup := by
    rw [List.map_map]; exact Program.globalList_keys_nodup P
  by_cases hmem : ∃ gd, g < P.size ∧ P.global? g = some gd
  · obtain ⟨gd, hlt, hgd⟩ := hmem
    rw [if_pos hlt, hgd, Option.map_some]
    exact Src.NatMap.get?_ofList hn (List.mem_map.2 ⟨(g, gd), Program.mem_globalList.2 ⟨hlt, hgd⟩, rfl⟩)
  · cases hx : (Src.NatMap.ofList (P.globalList.map fun p => (p.1, F p.1 p.2))).get? g with
    | some x =>
      have := Convert.Proof.natMap_ofList_mem hn hx
      obtain ⟨⟨g', gd⟩, hm, he⟩ := List.mem_map.1 this
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact absurd ⟨gd, Program.mem_globalList.1 hm⟩ hmem
    | none =>
      split
      · next hlt =>
        cases hgd : P.global? g with
        | none => rfl
        | some gd => exact absurd ⟨gd, hlt, hgd⟩ hmem
      · rfl

/-- A program with the same roots, constructors and globals refines its
source. -/
theorem refines_of_globals {P Q : Program} (hroots : Q.roots = P.roots) (hknown : Q.known = P.known)
    (hg : ∀ g, Q.global? g = P.global? g) : Sem.Refines P Q :=
  WalkProof.WalkProg.refines (Valid := fun _ _ _ => False)
    { roots := hroots, known := hknown
      globals := fun g gd h => ⟨gd, by rw [hg, h], rfl, .inl rfl⟩
      suffix := fun _ _ _ _ _ h _ _ => h, cknown := fun _ _ _ h => h.elim, cglob := fun _ _ _ h => h.elim
      cbody := fun _ _ _ h => h.elim, inl := fun _ _ _ _ h => h.elim, noRed := fun _ _ _ h => h.elim }

end PassProof

end Compilatrix.Anf

namespace Compilatrix.Anf.PassProof

/-- A program whose globals are its source's, mapped, keeps the shape of
its ids. -/
theorem wf_of_mapped {P Q : Program} {F : GlobalId → GDef → GDef} (hsize : Q.size = P.size)
    (hQ : ∀ g, Q.global? g = if g < P.size then (P.global? g).map (F g) else none) (h : P.WF) : Q.WF := by
  refine ⟨fun g gd hg => ?_, fun g hg => ?_⟩
  · rw [hQ] at hg
    split at hg
    · next hlt => rw [hsize]; exact hlt
    · cases hg
  · rw [hsize] at hg
    obtain ⟨gd, hgd⟩ := h.2 g hg
    exact ⟨F g gd, by rw [hQ, if_pos hg, hgd]; rfl⟩

end Compilatrix.Anf.PassProof
