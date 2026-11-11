import IxCC.Recheck.Cert
import IxCC.Anf.Entry
import IxCC.Src.Relevance.Check

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
before the step was added gets. Kernel-evaluable (D17): lists.

`fnParam?` finds a root parameter that a caller would have to fill with a
closure (below, "Roots whose caller would pass a closure"). -/

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

/-! ## Roots whose caller would pass a closure

A closure does not cross a program boundary (decision 1 of 2026-11-10): the
entry wrapper, the executables and every compile claim pass words. A root
with a parameter of function type therefore has no caller that can pass a
meaningful argument; compiled, every input that reaches an application of
the parameter traps (the closures step's dispatcher has no closure of the
program to select). The compiler refuses such a root before it produces an
object (`Recheck.checkFnParams`, `rt.fnparam`).

**Which declared parameters are refused.** The parameters are the binders of
the root's declared type as written (`Src.Term.pis`), the ones
`declaredParams` counts and `CompileClaim.rootParamsAllNat` reads. One is
refused when all of these hold (`fnParamDomain`):

* the relevance checker classifies it as relevant
  (`Src.Relevance.Check.Canonical.classifyDomain`, the classification that
  justifies erasure's tags): not a type or type former (`α : Type`,
  `F : Type → Type`: erased), not a proof (`h : n < 5`, `h : ∀ n, P n`:
  erased), and not unclassifiable;
* its domain, after unfolding safe definitions at its head as that
  classification does (`whnfType`, eight steps), is a Π-type: `Nat → Nat`,
  or a definition such as `NatFn := Nat → Nat`;
* its domain is not `Nat` itself (the claims' own test, `natDomain`).

Not refused: `Nat`, `Bool` and other inductives, structures, even one with a
field of function type (`ops : Ops`; a call through such a field traps at
run time as `applyArg` did), a variable's type (`x : α`), type parameters
and proofs. Every root refused here is refused by the compile claims too
(`CompileClaim.rootParamsAllNat_of_fnParam`): a refused parameter's domain is
not `Nat`. -/

open Src.Relevance.Check.Canonical in
/-- The sort a declaration's earlier binder of domain `d` lives in, as the
relevance checker's telescope records it (`classifyTelescope`). -/
def domSort (p : Src.Program) (d : Src.Term) : Option Ixon.Univ :=
  match (whnfType p 8 d).pis.2 with
  | .sort u => some u
  | _ => none

/-- Domain `dom` is the `Nat` constant of `p` (`CompileClaim.isNatType`). -/
def natDomain (p : Src.Program) (dom : Src.Term) : Bool :=
  some dom == p.known.nat.map (Src.Term.const · [])

open Src.Relevance.Check.Canonical in
/-- A declared parameter (binder `b`, domain `dom`, under the earlier
binders' domains `ctx`) that a caller would have to fill with a closure: not
`Nat`, relevant, and of function type after unfolding at its head. -/
def fnParamDomain (p : Src.Program) (ctx : List (Src.Term × Option Ixon.Univ)) (b : Src.Binder)
    (dom : Src.Term) : Bool :=
  !natDomain p dom && classifyDomain p ctx b dom == some .rel &&
    match whnfType p 8 dom with
    | .pi .. => true
    | _ => false

/-- The position of the first parameter of telescope `bs` (from position
`i`, under `ctx`) that `fnParamDomain` refuses. -/
def fnParamAt (p : Src.Program) :
    List (Src.Binder × Src.Term) → List (Src.Term × Option Ixon.Univ) → Nat → Option Nat
  | [], _, _ => none
  | (b, d) :: rest, ctx, i =>
    if fnParamDomain p ctx b d then some i
    else fnParamAt p rest ((d, domSort p d) :: ctx) (i + 1)

/-- A root constant's first parameter of function type (`fnParamAt` on its
declared type's binders as written), by position. -/
def fnParam? (src : Src.Program) (c : Src.CId) : Option Nat :=
  (src.decl? c).bind fun d => fnParamAt src d.type.pis.1 [] 0

/-- A parameter `fnParamAt` refuses is in the telescope, and its domain is
not `Nat`. -/
theorem fnParamAt_mem {p : Src.Program} :
    ∀ {bs : List (Src.Binder × Src.Term)} {ctx : List (Src.Term × Option Ixon.Univ)} {i j : Nat},
      fnParamAt p bs ctx i = some j → ∃ bd ∈ bs, natDomain p bd.2 = false
  | [], _, _, _, h => by simp [fnParamAt] at h
  | (b, d) :: rest, ctx, i, j, h => by
    simp only [fnParamAt] at h
    split at h
    · next hf =>
      refine ⟨(b, d), by simp, ?_⟩
      cases hn : natDomain p d with
      | false => rfl
      | true => simp [fnParamDomain, hn] at hf
    · obtain ⟨bd, hm, hn⟩ := fnParamAt_mem h
      exact ⟨bd, by simp [hm], hn⟩

end IxCC.Recheck
