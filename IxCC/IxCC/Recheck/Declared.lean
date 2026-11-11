import IxCC.Recheck.Cert
import IxCC.Anf.Entry

/-! # The roots' declared parameter counts, and the inputs the theorems cover

A root is called with exactly its declared number of parameters
(`docs/closures-design.md`, "Proof obligation", the decisions of 2026-11-13
and 2026-11-14). The declared count (`declaredParams`) is the number of
leading binders of the root's declared type as written (`Src.Term.pis`
unfolds no definition), the quantity `CompileClaim.rootParamsAllNat`
compares, read from the source program; no certificate can change it.
`declaredCounts` lists them by root position: the closures step
(`Anf.Pipeline.closures`) makes each root's entry at that count.

`ExactDeclared` is the end-to-end statements' input premise: an input of
exactly its root's declared count. `Covered` is the set of inputs they
hold on: those, and every input when the closures step left the
certificate's program unchanged, which is what every program that compiled
before the step was added gets. Kernel-evaluable (D17): lists. -/

namespace IxCC.Recheck

/-- A source root's declared parameter count. -/
def declaredParams (src : Src.Program) (c : Src.CId) : Option Nat :=
  (src.decl? c).map fun d => d.type.pis.1.length

/-- Inputs of exactly their source root's declared parameter count. -/
def ExactDeclared (src : Src.Program) (i : Nat × List Nat) : Prop :=
  ∀ addr c, src.roots[i.1]? = some (addr, c) → ∀ n, declaredParams src c = some n → i.2.length = n

/-- The source roots' declared counts by position, if every root has a
declaration. -/
def declaredCounts (src : Src.Program) : Option (List Nat) :=
  src.roots.mapM fun r => declaredParams src r.2

/-- **The inputs the end-to-end theorems cover**: those of exactly the source
root's declared count, and every input when the closures step left the
certificate's middle-end program unchanged. -/
def Covered (mid : Anf.Pipeline.Cert) (src : Src.Program) (lam : Lam.Program) (anf : Anf.Program)
    (i : Nat × List Nat) : Prop :=
  ExactDeclared src i ∨ Anf.Pipeline.run mid lam = .ok anf

theorem declaredCounts_get : ∀ {roots : List (Ixon.Address × Src.CId)} {src : Src.Program}
    {decl : List Nat}, roots.mapM (fun r => declaredParams src r.2) = some decl →
    ∀ {j : Nat} {n : Nat}, decl[j]? = some n → ∃ addr c, roots[j]? = some (addr, c) ∧
      declaredParams src c = some n
  | [], _, decl, h, j, n, hn => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp at hn
  | (addr, c) :: rest, src, decl, h, j, n, hn => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hc : declaredParams src c with
    | none => rw [hc] at h; cases h
    | some m =>
      rw [hc] at h
      simp only [Option.bind_some] at h
      cases hr : rest.mapM (fun r => declaredParams src r.2) with
      | none => rw [hr] at h; cases h
      | some ds =>
        rw [hr] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
          subst hn
          exact ⟨addr, c, rfl, hc⟩
        | succ j =>
          simp only [List.getElem?_cons_succ] at hn
          obtain ⟨a', c', h1, h2⟩ := declaredCounts_get hr hn
          exact ⟨a', c', by simpa using h1, h2⟩

/-- An input of the declared count is one of the closures step's
`Anf.Entry.DeclExact`. -/
theorem declaredCounts_exact {src : Src.Program} {decl : List Nat} (h : declaredCounts src = some decl)
    {i : Nat × List Nat} (hi : ExactDeclared src i) : Anf.Entry.DeclExact decl i := by
  intro n hn
  obtain ⟨addr, c, hr, hd⟩ := declaredCounts_get h hn
  exact hi addr c hr n hd

end IxCC.Recheck
