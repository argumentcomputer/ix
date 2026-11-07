import IxCC.Rt.Rc.Proof.Readback.Region
import IxCC.Fir.Proof.Correct

set_option autoImplicit false
namespace IxCC.Rt.Rc.Procs.Readback
open IxCC.Own
open IxCC.Rt.Proof (Typed)

mutual
/-- A structural source-result typing and tag view. Every constructor uses
its admitted table row and its signature row; every field is represented,
including repeated and nested constructor fields. No memory/readback fact
is assumed by this relation. -/
inductive SourceTree (table : List Lam.CtorInfo) (sig : Sig) :
    FoTy → Fir.Val → Sem.Obs → Sem.Obs → Prop
  | nat (n : Nat) : SourceTree table sig .nat (.lit (.nat n)) (.nat n) (.nat n)
  | ctor {i cid : Nat} {c : Fir.CtorInfo} {types : List FoTy}
      {values : List Fir.Val} {source target : List Sem.Obs} :
      c.key = .src cid → Fir.CtorInfo.ofKey table c.key = some c →
      sig.ctor? i c.tag = some types → c.arity = values.length →
      SourceForest table sig types values source target →
      SourceTree table sig (.ind i) (.ctor c values) (.ctor cid source) (.ctor c.tag target)

inductive SourceForest (table : List Lam.CtorInfo) (sig : Sig) :
    List FoTy → List Fir.Val → List Sem.Obs → List Sem.Obs → Prop
  | nil : SourceForest table sig [] [] [] []
  | cons {ty : FoTy} {v : Fir.Val} {s t : Sem.Obs} {tys : List FoTy}
      {vs : List Fir.Val} {ss ts : List Sem.Obs} :
      SourceTree table sig ty v s t → SourceForest table sig tys vs ss ts →
      SourceForest table sig (ty :: tys) (v :: vs) (s :: ss) (t :: ts)
end

theorem SourceForest.length {table : List Lam.CtorInfo} {sig : Sig}
    {types : List FoTy} {values : List Fir.Val} {source target : List Sem.Obs}
    (h : SourceForest table sig types values source target) : types.length = values.length := by
  induction types generalizing values source target with
  | nil => cases h; rfl
  | cons ty types ih =>
    cases h with
    | cons head tail => simp [ih tail]

theorem SourceForest.get {table : List Lam.CtorInfo} {sig : Sig}
    {types : List FoTy} {values : List Fir.Val} {source target : List Sem.Obs}
    (h : SourceForest table sig types values source target) :
    ∀ (j : Nat) ty value, types[j]? = some ty → values[j]? = some value →
      ∃ s t, SourceTree table sig ty value s t := by
  intro j
  induction j generalizing types values source target with
  | zero =>
    cases h with
    | nil => intro ty value ht; simp at ht
    | @cons ty v s t tys vs ss ts head tail =>
      intro ty' v' ht hv
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ht hv
      subst ty'; subst v'; exact ⟨s, t, head⟩
  | succ j ih =>
    cases h with
    | nil => intro ty value ht; simp at ht
    | cons head tail => exact ih tail

mutual
theorem SourceTree.observations {table : List Lam.CtorInfo} {sig : Sig}
    {ty : FoTy} {value : Fir.Val} {source target : Sem.Obs}
    (h : SourceTree table sig ty value source target) :
    Fir.obsV value = some source ∧ Fir.readback value = some target := by
  cases h with
  | nat => exact ⟨rfl, rfl⟩
  | ctor key row signature arity fields =>
    obtain ⟨hs, ht⟩ := SourceForest.observations fields
    simp [Fir.obsV, Fir.readback, key, arity, hs, ht]
termination_by sizeOf value

theorem SourceForest.observations {table : List Lam.CtorInfo} {sig : Sig}
    {types : List FoTy} {values : List Fir.Val} {source target : List Sem.Obs}
    (h : SourceForest table sig types values source target) :
    Fir.obsList values = some source ∧ Fir.readbackList values = some target := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | cons head tail =>
    obtain ⟨hs, ht⟩ := SourceTree.observations head
    obtain ⟨hss, htt⟩ := SourceForest.observations tail
    simp [Fir.obsList, Fir.readbackList, hs, ht, hss, htt]
termination_by sizeOf values
end

theorem toFirList_rel {H : Heap} {fuel : Nat} :
    ∀ {values : List RVal} {logical : List Fir.Val},
      Own.toFirList H fuel values = some logical →
      Sem.Forall2 (fun v w => Own.toFir H fuel v = some w) values logical
  | [], logical, h => by simp only [Own.toFirList, Option.some.injEq] at h; subst logical; exact .nil
  | v :: vs, logical, h => by
    cases hv : Own.toFir H fuel v with
    | none => simp [Own.toFirList, hv] at h
    | some w =>
      cases ht : Own.toFirList H fuel vs with
      | none => simp [Own.toFirList, hv, ht] at h
      | some ws =>
        simp only [Own.toFirList, hv, ht, Option.some.injEq] at h
        subst logical
        exact .cons hv (toFirList_rel ht)

theorem typed_of_tree {table : List Lam.CtorInfo} {sig : Sig} {H : Heap} :
    ∀ fuel {v : RVal} {value : Fir.Val} {ty : FoTy} {source target : Sem.Obs},
      Own.toFir H fuel v = some value → SourceTree table sig ty value source target →
      Typed sig H ty v := by
  intro fuel
  induction fuel with
  | zero =>
    intro v value ty source target den tree
    cases v with
    | loc location => simp [Own.toFir] at den
    | lit literal =>
      simp only [Own.toFir, Option.some.injEq] at den
      subst value
      cases tree
      exact .nat
    | erased =>
      simp only [Own.toFir, Option.some.injEq] at den
      subst value
      cases tree
    | ctor0 c =>
      simp only [Own.toFir, Option.some.injEq] at den
      subst value
      cases tree with
      | ctor key row signature arity forest =>
        cases forest
        exact .ctor0 signature
  | succ fuel ih =>
    intro v value ty source target den tree
    cases v with
    | lit literal =>
      simp only [Own.toFir, Option.some.injEq] at den
      subst value
      cases tree
      exact .nat
    | erased =>
      simp only [Own.toFir, Option.some.injEq] at den
      subst value
      cases tree
    | ctor0 c =>
      simp only [Own.toFir, Option.some.injEq] at den
      subst value
      cases tree with
      | ctor key row signature arity forest =>
        cases forest
        exact .ctor0 signature
    | loc location =>
      simp only [Own.toFir] at den
      split at den
      · next refs mode body cell =>
        obtain ⟨values, hv, he⟩ := Option.map_eq_some_iff.mp den
        subst value
        cases tree with
        | ctor key row signature arity forest =>
          have rel := toFirList_rel hv
          refine .cell cell signature (forest.length.trans rel.length.symm) ?_
          intro j ty v ht hv'
          obtain ⟨logical, hl, hd⟩ := rel.get hv'
          obtain ⟨s, t, subtree⟩ := forest.get j ty logical ht hl
          exact ih hd subtree
      · cases den

/-- Full source constructor-ID observation to physical constructor-tag
observation at the unchanged driver fuel. The structural SourceTree input
states signature/table typing, never desired memory execution agreement. -/
theorem source_readback_region {table : List Lam.CtorInfo} {sig : Sig}
    {ty : FoTy} {logical : Fir.Val} {source target : Sem.Obs}
    (tree : SourceTree table sig ty logical source target)
    {H : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {base bump limit : Lir.Word} {slots : List Slot} {regionBytes : Nat}
    (heap : HeapLive H addresses mem)
    (partition : ArenaPartition H addresses base bump limit slots)
    (ordered : Own.Rc.HeapOk H) (region : limit.toNat-base.toNat ≤ regionBytes)
    {v : RVal} {word : Lir.Word} (den : Own.Proof.Den H v logical)
    (represented : valueWord addresses v = some word) :
    Fir.obsV logical = some source ∧ Rt.readback sig (regionBytes/8) mem ty word = some target := by
  have observations := tree.observations
  refine ⟨observations.1, ?_⟩
  rw [readback_region heap partition ordered region den (typed_of_tree _ den tree) represented]
  exact observations.2




end IxCC.Rt.Rc.Procs.Readback
